-- Prove2me | solution 1 for syracuse_descends_range_714321_718321
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T19:05:02.554518+00:00
-- url     : https://prove2.me/submissions/a1aa95f9-f43d-4f9e-a59f-a5ea0d1da8f0

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


theorem B917525 : Blo 714321 917525 := bbase (se 6 (by rfl) ⟨21504, by rfl⟩ : syracuseStep 917525 = 43009) (by norm_num)
theorem B1867853 : Blo 714321 1867853 := bbase (se 3 (by rfl) ⟨350222, by rfl⟩ : syracuseStep 1867853 = 700445) (by norm_num)
theorem B1147061 : Blo 714321 1147061 := bbase (se 5 (by rfl) ⟨53768, by rfl⟩ : syracuseStep 1147061 = 107537) (by norm_num)
theorem B5439797 : Blo 714321 5439797 := bbase (se 5 (by rfl) ⟨254990, by rfl⟩ : syracuseStep 5439797 = 509981) (by norm_num)
theorem B918301 : Blo 714321 918301 := bbase (se 3 (by rfl) ⟨172181, by rfl⟩ : syracuseStep 918301 = 344363) (by norm_num)
theorem B918481 : Blo 714321 918481 := bbase (se 2 (by rfl) ⟨344430, by rfl⟩ : syracuseStep 918481 = 688861) (by norm_num)
theorem B2753797 : Blo 714321 2753797 := bbase (se 4 (by rfl) ⟨258168, by rfl⟩ : syracuseStep 2753797 = 516337) (by norm_num)
theorem B3441989 : Blo 714321 3441989 := bbase (se 4 (by rfl) ⟨322686, by rfl⟩ : syracuseStep 3441989 = 645373) (by norm_num)
theorem B2721221 : Blo 714321 2721221 := bbase (se 4 (by rfl) ⟨255114, by rfl⟩ : syracuseStep 2721221 = 510229) (by norm_num)
theorem B2950613 : Blo 714321 2950613 := bbase (se 7 (by rfl) ⟨34577, by rfl⟩ : syracuseStep 2950613 = 69155) (by norm_num)
theorem B1017365 : Blo 714321 1017365 := bbase (se 6 (by rfl) ⟨23844, by rfl⟩ : syracuseStep 1017365 = 47689) (by norm_num)
theorem B1607237 : Blo 714321 1607237 := bbase (se 4 (by rfl) ⟨150678, by rfl⟩ : syracuseStep 1607237 = 301357) (by norm_num)
theorem B3671621 : Blo 714321 3671621 := bbase (se 4 (by rfl) ⟨344214, by rfl⟩ : syracuseStep 3671621 = 688429) (by norm_num)
theorem B1148509 : Blo 714321 1148509 := bbase (se 3 (by rfl) ⟨215345, by rfl⟩ : syracuseStep 1148509 = 430691) (by norm_num)
theorem B1607309 : Blo 714321 1607309 := bbase (se 3 (by rfl) ⟨301370, by rfl⟩ : syracuseStep 1607309 = 602741) (by norm_num)
theorem B1935029 : Blo 714321 1935029 := bbase (se 5 (by rfl) ⟨90704, by rfl⟩ : syracuseStep 1935029 = 181409) (by norm_num)
theorem B1607381 : Blo 714321 1607381 := bbase (se 7 (by rfl) ⟨18836, by rfl⟩ : syracuseStep 1607381 = 37673) (by norm_num)
theorem B2721509 : Blo 714321 2721509 := bbase (se 4 (by rfl) ⟨255141, by rfl⟩ : syracuseStep 2721509 = 510283) (by norm_num)
theorem B1607453 : Blo 714321 1607453 := bbase (se 3 (by rfl) ⟨301397, by rfl⟩ : syracuseStep 1607453 = 602795) (by norm_num)
theorem B1607525 : Blo 714321 1607525 := bbase (se 4 (by rfl) ⟨150705, by rfl⟩ : syracuseStep 1607525 = 301411) (by norm_num)
theorem B1607597 : Blo 714321 1607597 := bbase (se 3 (by rfl) ⟨301424, by rfl⟩ : syracuseStep 1607597 = 602849) (by norm_num)
theorem B1607669 : Blo 714321 1607669 := bbase (se 5 (by rfl) ⟨75359, by rfl⟩ : syracuseStep 1607669 = 150719) (by norm_num)
theorem B1607741 : Blo 714321 1607741 := bbase (se 3 (by rfl) ⟨301451, by rfl⟩ : syracuseStep 1607741 = 602903) (by norm_num)
theorem B1935461 : Blo 714321 1935461 := bbase (se 4 (by rfl) ⟨181449, by rfl⟩ : syracuseStep 1935461 = 362899) (by norm_num)
theorem B1607813 : Blo 714321 1607813 := bbase (se 4 (by rfl) ⟨150732, by rfl⟩ : syracuseStep 1607813 = 301465) (by norm_num)
theorem B1607885 : Blo 714321 1607885 := bbase (se 3 (by rfl) ⟨301478, by rfl⟩ : syracuseStep 1607885 = 602957) (by norm_num)
theorem B1018117 : Blo 714321 1018117 := bbase (se 4 (by rfl) ⟨95448, by rfl⟩ : syracuseStep 1018117 = 190897) (by norm_num)
theorem B1607957 : Blo 714321 1607957 := bbase (se 6 (by rfl) ⟨37686, by rfl⟩ : syracuseStep 1607957 = 75373) (by norm_num)
theorem B1608029 : Blo 714321 1608029 := bbase (se 3 (by rfl) ⟨301505, by rfl⟩ : syracuseStep 1608029 = 603011) (by norm_num)
theorem B2754917 : Blo 714321 2754917 := bbase (se 4 (by rfl) ⟨258273, by rfl⟩ : syracuseStep 2754917 = 516547) (by norm_num)
theorem B1608101 : Blo 714321 1608101 := bbase (se 4 (by rfl) ⟨150759, by rfl⟩ : syracuseStep 1608101 = 301519) (by norm_num)
theorem B1608173 : Blo 714321 1608173 := bbase (se 3 (by rfl) ⟨301532, by rfl⟩ : syracuseStep 1608173 = 603065) (by norm_num)
theorem B2034229 : Blo 714321 2034229 := bbase (se 5 (by rfl) ⟨95354, by rfl⟩ : syracuseStep 2034229 = 190709) (by norm_num)
theorem B1608245 : Blo 714321 1608245 := bbase (se 5 (by rfl) ⟨75386, by rfl⟩ : syracuseStep 1608245 = 150773) (by norm_num)
theorem B1935989 : Blo 714321 1935989 := bbase (se 5 (by rfl) ⟨90749, by rfl⟩ : syracuseStep 1935989 = 181499) (by norm_num)
theorem B1608317 : Blo 714321 1608317 := bbase (se 3 (by rfl) ⟨301559, by rfl⟩ : syracuseStep 1608317 = 603119) (by norm_num)
theorem B2296453 : Blo 714321 2296453 := bbase (se 4 (by rfl) ⟨215292, by rfl⟩ : syracuseStep 2296453 = 430585) (by norm_num)
theorem B1608389 : Blo 714321 1608389 := bbase (se 4 (by rfl) ⟨150786, by rfl⟩ : syracuseStep 1608389 = 301573) (by norm_num)
theorem B2034389 : Blo 714321 2034389 := bbase (se 7 (by rfl) ⟨23840, by rfl⟩ : syracuseStep 2034389 = 47681) (by norm_num)
theorem B1608461 : Blo 714321 1608461 := bbase (se 3 (by rfl) ⟨301586, by rfl⟩ : syracuseStep 1608461 = 603173) (by norm_num)
theorem B1608533 : Blo 714321 1608533 := bbase (se 9 (by rfl) ⟨4712, by rfl⟩ : syracuseStep 1608533 = 9425) (by norm_num)
theorem B2722693 : Blo 714321 2722693 := bbase (se 4 (by rfl) ⟨255252, by rfl⟩ : syracuseStep 2722693 = 510505) (by norm_num)
theorem B1608605 : Blo 714321 1608605 := bbase (se 3 (by rfl) ⟨301613, by rfl⟩ : syracuseStep 1608605 = 603227) (by norm_num)
theorem B2034629 : Blo 714321 2034629 := bbase (se 4 (by rfl) ⟨190746, by rfl⟩ : syracuseStep 2034629 = 381493) (by norm_num)
theorem B1149893 : Blo 714321 1149893 := bbase (se 4 (by rfl) ⟨107802, by rfl⟩ : syracuseStep 1149893 = 215605) (by norm_num)
theorem B1608677 : Blo 714321 1608677 := bbase (se 4 (by rfl) ⟨150813, by rfl⟩ : syracuseStep 1608677 = 301627) (by norm_num)
theorem B1018909 : Blo 714321 1018909 := bbase (se 3 (by rfl) ⟨191045, by rfl⟩ : syracuseStep 1018909 = 382091) (by norm_num)
theorem B1608749 : Blo 714321 1608749 := bbase (se 3 (by rfl) ⟨301640, by rfl⟩ : syracuseStep 1608749 = 603281) (by norm_num)
theorem B1608821 : Blo 714321 1608821 := bbase (se 5 (by rfl) ⟨75413, by rfl⟩ : syracuseStep 1608821 = 150827) (by norm_num)
theorem B2034821 : Blo 714321 2034821 := bbase (se 4 (by rfl) ⟨190764, by rfl⟩ : syracuseStep 2034821 = 381529) (by norm_num)
theorem B1150085 : Blo 714321 1150085 := bbase (se 4 (by rfl) ⟨107820, by rfl⟩ : syracuseStep 1150085 = 215641) (by norm_num)
theorem B2722997 : Blo 714321 2722997 := bbase (se 5 (by rfl) ⟨127640, by rfl⟩ : syracuseStep 2722997 = 255281) (by norm_num)
theorem B1608893 : Blo 714321 1608893 := bbase (se 3 (by rfl) ⟨301667, by rfl⟩ : syracuseStep 1608893 = 603335) (by norm_num)
theorem B2755781 : Blo 714321 2755781 := bbase (se 4 (by rfl) ⟨258354, by rfl⟩ : syracuseStep 2755781 = 516709) (by norm_num)
theorem B1608965 : Blo 714321 1608965 := bbase (se 4 (by rfl) ⟨150840, by rfl⟩ : syracuseStep 1608965 = 301681) (by norm_num)
theorem B1609037 : Blo 714321 1609037 := bbase (se 3 (by rfl) ⟨301694, by rfl⟩ : syracuseStep 1609037 = 603389) (by norm_num)
theorem B1019245 : Blo 714321 1019245 := bbase (se 3 (by rfl) ⟨191108, by rfl⟩ : syracuseStep 1019245 = 382217) (by norm_num)
theorem B1609109 : Blo 714321 1609109 := bbase (se 6 (by rfl) ⟨37713, by rfl⟩ : syracuseStep 1609109 = 75427) (by norm_num)
theorem B1609181 : Blo 714321 1609181 := bbase (se 3 (by rfl) ⟨301721, by rfl⟩ : syracuseStep 1609181 = 603443) (by norm_num)
theorem B2067941 : Blo 714321 2067941 := bbase (se 4 (by rfl) ⟨193869, by rfl⟩ : syracuseStep 2067941 = 387739) (by norm_num)
theorem B724501 : Blo 714321 724501 := bbase (se 6 (by rfl) ⟨16980, by rfl⟩ : syracuseStep 724501 = 33961) (by norm_num)
theorem B1609253 : Blo 714321 1609253 := bbase (se 4 (by rfl) ⟨150867, by rfl⟩ : syracuseStep 1609253 = 301735) (by norm_num)
theorem B1019461 : Blo 714321 1019461 := bbase (se 4 (by rfl) ⟨95574, by rfl⟩ : syracuseStep 1019461 = 191149) (by norm_num)
theorem B2068037 : Blo 714321 2068037 := bbase (se 4 (by rfl) ⟨193878, by rfl⟩ : syracuseStep 2068037 = 387757) (by norm_num)
theorem B1609325 : Blo 714321 1609325 := bbase (se 3 (by rfl) ⟨301748, by rfl⟩ : syracuseStep 1609325 = 603497) (by norm_num)
theorem B1609397 : Blo 714321 1609397 := bbase (se 5 (by rfl) ⟨75440, by rfl⟩ : syracuseStep 1609397 = 150881) (by norm_num)
theorem B1838789 : Blo 714321 1838789 := bbase (se 4 (by rfl) ⟨172386, by rfl⟩ : syracuseStep 1838789 = 344773) (by norm_num)
theorem B1609469 : Blo 714321 1609469 := bbase (se 3 (by rfl) ⟨301775, by rfl⟩ : syracuseStep 1609469 = 603551) (by norm_num)
theorem B921385 : Blo 714321 921385 := bbase (se 2 (by rfl) ⟨345519, by rfl⟩ : syracuseStep 921385 = 691039) (by norm_num)
theorem B5508917 : Blo 714321 5508917 := bbase (se 5 (by rfl) ⟨258230, by rfl⟩ : syracuseStep 5508917 = 516461) (by norm_num)
theorem B1609541 : Blo 714321 1609541 := bbase (se 4 (by rfl) ⟨150894, by rfl⟩ : syracuseStep 1609541 = 301789) (by norm_num)
theorem B921425 : Blo 714321 921425 := bbase (se 2 (by rfl) ⟨345534, by rfl⟩ : syracuseStep 921425 = 691069) (by norm_num)
theorem B724837 : Blo 714321 724837 := bbase (se 4 (by rfl) ⟨67953, by rfl⟩ : syracuseStep 724837 = 135907) (by norm_num)
theorem B1609613 : Blo 714321 1609613 := bbase (se 3 (by rfl) ⟨301802, by rfl⟩ : syracuseStep 1609613 = 603605) (by norm_num)
theorem B1019837 : Blo 714321 1019837 := bbase (se 3 (by rfl) ⟨191219, by rfl⟩ : syracuseStep 1019837 = 382439) (by norm_num)
theorem B1609685 : Blo 714321 1609685 := bbase (se 7 (by rfl) ⟨18863, by rfl⟩ : syracuseStep 1609685 = 37727) (by norm_num)
theorem B11636693 : Blo 714321 11636693 := bbase (se 7 (by rfl) ⟨136367, by rfl⟩ : syracuseStep 11636693 = 272735) (by norm_num)
theorem B1609757 : Blo 714321 1609757 := bbase (se 3 (by rfl) ⟨301829, by rfl⟩ : syracuseStep 1609757 = 603659) (by norm_num)
theorem B2035813 : Blo 714321 2035813 := bbase (se 4 (by rfl) ⟨190857, by rfl⟩ : syracuseStep 2035813 = 381715) (by norm_num)
theorem B1609829 : Blo 714321 1609829 := bbase (se 4 (by rfl) ⟨150921, by rfl⟩ : syracuseStep 1609829 = 301843) (by norm_num)
theorem B725117 : Blo 714321 725117 := bbase (se 3 (by rfl) ⟨135959, by rfl⟩ : syracuseStep 725117 = 271919) (by norm_num)
theorem B3051685 : Blo 714321 3051685 := bbase (se 4 (by rfl) ⟨286095, by rfl⟩ : syracuseStep 3051685 = 572191) (by norm_num)
theorem B1609901 : Blo 714321 1609901 := bbase (se 3 (by rfl) ⟨301856, by rfl⟩ : syracuseStep 1609901 = 603713) (by norm_num)
theorem B1609973 : Blo 714321 1609973 := bbase (se 5 (by rfl) ⟨75467, by rfl⟩ : syracuseStep 1609973 = 150935) (by norm_num)
theorem B1610045 : Blo 714321 1610045 := bbase (se 3 (by rfl) ⟨301883, by rfl⟩ : syracuseStep 1610045 = 603767) (by norm_num)
theorem B3871093 : Blo 714321 3871093 := bbase (se 5 (by rfl) ⟨181457, by rfl⟩ : syracuseStep 3871093 = 362915) (by norm_num)
theorem B1610117 : Blo 714321 1610117 := bbase (se 4 (by rfl) ⟨150948, by rfl⟩ : syracuseStep 1610117 = 301897) (by norm_num)
theorem B1610189 : Blo 714321 1610189 := bbase (se 3 (by rfl) ⟨301910, by rfl⟩ : syracuseStep 1610189 = 603821) (by norm_num)
theorem B725477 : Blo 714321 725477 := bbase (se 4 (by rfl) ⟨68013, by rfl⟩ : syracuseStep 725477 = 136027) (by norm_num)
theorem B1610261 : Blo 714321 1610261 := bbase (se 6 (by rfl) ⟨37740, by rfl⟩ : syracuseStep 1610261 = 75481) (by norm_num)
theorem B1610333 : Blo 714321 1610333 := bbase (se 3 (by rfl) ⟨301937, by rfl⟩ : syracuseStep 1610333 = 603875) (by norm_num)
theorem B1610405 : Blo 714321 1610405 := bbase (se 4 (by rfl) ⟨150975, by rfl⟩ : syracuseStep 1610405 = 301951) (by norm_num)
theorem B1610477 : Blo 714321 1610477 := bbase (se 3 (by rfl) ⟨301964, by rfl⟩ : syracuseStep 1610477 = 603929) (by norm_num)
theorem B6886133 : Blo 714321 6886133 := bbase (se 5 (by rfl) ⟨322787, by rfl⟩ : syracuseStep 6886133 = 645575) (by norm_num)
theorem B1086221 : Blo 714321 1086221 := bbase (se 3 (by rfl) ⟨203666, by rfl⟩ : syracuseStep 1086221 = 407333) (by norm_num)
theorem B1676045 : Blo 714321 1676045 := bbase (se 3 (by rfl) ⟨314258, by rfl⟩ : syracuseStep 1676045 = 628517) (by norm_num)
theorem B725785 : Blo 714321 725785 := bbase (se 2 (by rfl) ⟨272169, by rfl⟩ : syracuseStep 725785 = 544339) (by norm_num)
theorem B1610549 : Blo 714321 1610549 := bbase (se 5 (by rfl) ⟨75494, by rfl⟩ : syracuseStep 1610549 = 150989) (by norm_num)
theorem B1610621 : Blo 714321 1610621 := bbase (se 3 (by rfl) ⟨301991, by rfl⟩ : syracuseStep 1610621 = 603983) (by norm_num)
theorem B1381277 : Blo 714321 1381277 := bbase (se 3 (by rfl) ⟨258989, by rfl⟩ : syracuseStep 1381277 = 517979) (by norm_num)
theorem B1610693 : Blo 714321 1610693 := bbase (se 4 (by rfl) ⟨151002, by rfl⟩ : syracuseStep 1610693 = 302005) (by norm_num)
theorem B726013 : Blo 714321 726013 := bbase (se 3 (by rfl) ⟨136127, by rfl⟩ : syracuseStep 726013 = 272255) (by norm_num)
theorem B1610765 : Blo 714321 1610765 := bbase (se 3 (by rfl) ⟨302018, by rfl⟩ : syracuseStep 1610765 = 604037) (by norm_num)
theorem B1086509 : Blo 714321 1086509 := bbase (se 3 (by rfl) ⟨203720, by rfl⟩ : syracuseStep 1086509 = 407441) (by norm_num)
theorem B1610837 : Blo 714321 1610837 := bbase (se 8 (by rfl) ⟨9438, by rfl⟩ : syracuseStep 1610837 = 18877) (by norm_num)
theorem B1610909 : Blo 714321 1610909 := bbase (se 3 (by rfl) ⟨302045, by rfl⟩ : syracuseStep 1610909 = 604091) (by norm_num)
theorem B2036917 : Blo 714321 2036917 := bbase (se 5 (by rfl) ⟨95480, by rfl⟩ : syracuseStep 2036917 = 190961) (by norm_num)
theorem B1610981 : Blo 714321 1610981 := bbase (se 4 (by rfl) ⟨151029, by rfl⟩ : syracuseStep 1610981 = 302059) (by norm_num)
theorem B2725109 : Blo 714321 2725109 := bbase (se 5 (by rfl) ⟨127739, by rfl⟩ : syracuseStep 2725109 = 255479) (by norm_num)
theorem B1611053 : Blo 714321 1611053 := bbase (se 3 (by rfl) ⟨302072, by rfl⟩ : syracuseStep 1611053 = 604145) (by norm_num)
theorem B1938757 : Blo 714321 1938757 := bbase (se 4 (by rfl) ⟨181758, by rfl⟩ : syracuseStep 1938757 = 363517) (by norm_num)
theorem B1021261 : Blo 714321 1021261 := bbase (se 3 (by rfl) ⟨191486, by rfl⟩ : syracuseStep 1021261 = 382973) (by norm_num)
theorem B1611125 : Blo 714321 1611125 := bbase (se 5 (by rfl) ⟨75521, by rfl⟩ : syracuseStep 1611125 = 151043) (by norm_num)
theorem B1611197 : Blo 714321 1611197 := bbase (se 3 (by rfl) ⟨302099, by rfl⟩ : syracuseStep 1611197 = 604199) (by norm_num)
theorem B8721877 : Blo 714321 8721877 := bbase (se 7 (by rfl) ⟨102209, by rfl⟩ : syracuseStep 8721877 = 204419) (by norm_num)
theorem B1611269 : Blo 714321 1611269 := bbase (se 4 (by rfl) ⟨151056, by rfl⟩ : syracuseStep 1611269 = 302113) (by norm_num)
theorem B2725397 : Blo 714321 2725397 := bbase (se 6 (by rfl) ⟨63876, by rfl⟩ : syracuseStep 2725397 = 127753) (by norm_num)
theorem B1611341 : Blo 714321 1611341 := bbase (se 3 (by rfl) ⟨302126, by rfl⟩ : syracuseStep 1611341 = 604253) (by norm_num)
theorem B726629 : Blo 714321 726629 := bbase (se 4 (by rfl) ⟨68121, by rfl⟩ : syracuseStep 726629 = 136243) (by norm_num)
theorem B3053173 : Blo 714321 3053173 := bbase (se 5 (by rfl) ⟨143117, by rfl⟩ : syracuseStep 3053173 = 286235) (by norm_num)
theorem B1939061 : Blo 714321 1939061 := bbase (se 5 (by rfl) ⟨90893, by rfl⟩ : syracuseStep 1939061 = 181787) (by norm_num)
theorem B3053189 : Blo 714321 3053189 := bbase (se 4 (by rfl) ⟨286236, by rfl⟩ : syracuseStep 3053189 = 572473) (by norm_num)
theorem B1611413 : Blo 714321 1611413 := bbase (se 6 (by rfl) ⟨37767, by rfl⟩ : syracuseStep 1611413 = 75535) (by norm_num)
theorem B1611485 : Blo 714321 1611485 := bbase (se 3 (by rfl) ⟨302153, by rfl⟩ : syracuseStep 1611485 = 604307) (by norm_num)
theorem B1611557 : Blo 714321 1611557 := bbase (se 4 (by rfl) ⟨151083, by rfl⟩ : syracuseStep 1611557 = 302167) (by norm_num)
theorem B726889 : Blo 714321 726889 := bbase (se 2 (by rfl) ⟨272583, by rfl⟩ : syracuseStep 726889 = 545167) (by norm_num)
theorem B1611629 : Blo 714321 1611629 := bbase (se 3 (by rfl) ⟨302180, by rfl⟩ : syracuseStep 1611629 = 604361) (by norm_num)
theorem B1021853 : Blo 714321 1021853 := bbase (se 3 (by rfl) ⟨191597, by rfl⟩ : syracuseStep 1021853 = 383195) (by norm_num)
theorem B1611701 : Blo 714321 1611701 := bbase (se 5 (by rfl) ⟨75548, by rfl⟩ : syracuseStep 1611701 = 151097) (by norm_num)
theorem B1808365 : Blo 714321 1808365 := bbase (se 3 (by rfl) ⟨339068, by rfl⟩ : syracuseStep 1808365 = 678137) (by norm_num)
theorem B1021933 : Blo 714321 1021933 := bbase (se 3 (by rfl) ⟨191612, by rfl⟩ : syracuseStep 1021933 = 383225) (by norm_num)
theorem B1611773 : Blo 714321 1611773 := bbase (se 3 (by rfl) ⟨302207, by rfl⟩ : syracuseStep 1611773 = 604415) (by norm_num)
theorem B1611845 : Blo 714321 1611845 := bbase (se 4 (by rfl) ⟨151110, by rfl⟩ : syracuseStep 1611845 = 302221) (by norm_num)
theorem B1808477 : Blo 714321 1808477 := bbase (se 3 (by rfl) ⟨339089, by rfl⟩ : syracuseStep 1808477 = 678179) (by norm_num)
theorem B1022053 : Blo 714321 1022053 := bbase (se 4 (by rfl) ⟨95817, by rfl⟩ : syracuseStep 1022053 = 191635) (by norm_num)
theorem B1611917 : Blo 714321 1611917 := bbase (se 3 (by rfl) ⟨302234, by rfl⟩ : syracuseStep 1611917 = 604469) (by norm_num)
theorem B727213 : Blo 714321 727213 := bbase (se 3 (by rfl) ⟨136352, by rfl⟩ : syracuseStep 727213 = 272705) (by norm_num)
theorem B1022149 : Blo 714321 1022149 := bbase (se 4 (by rfl) ⟨95826, by rfl⟩ : syracuseStep 1022149 = 191653) (by norm_num)
theorem B1611989 : Blo 714321 1611989 := bbase (se 7 (by rfl) ⟨18890, by rfl⟩ : syracuseStep 1611989 = 37781) (by norm_num)
theorem B727261 : Blo 714321 727261 := bbase (se 3 (by rfl) ⟨136361, by rfl⟩ : syracuseStep 727261 = 272723) (by norm_num)
theorem B1808669 : Blo 714321 1808669 := bbase (se 3 (by rfl) ⟨339125, by rfl⟩ : syracuseStep 1808669 = 678251) (by norm_num)
theorem B1612061 : Blo 714321 1612061 := bbase (se 3 (by rfl) ⟨302261, by rfl⟩ : syracuseStep 1612061 = 604523) (by norm_num)
theorem B1612133 : Blo 714321 1612133 := bbase (se 4 (by rfl) ⟨151137, by rfl⟩ : syracuseStep 1612133 = 302275) (by norm_num)
theorem B1743229 : Blo 714321 1743229 := bbase (se 3 (by rfl) ⟨326855, by rfl⟩ : syracuseStep 1743229 = 653711) (by norm_num)
theorem B956845 : Blo 714321 956845 := bbase (se 3 (by rfl) ⟨179408, by rfl⟩ : syracuseStep 956845 = 358817) (by norm_num)
theorem B1612205 : Blo 714321 1612205 := bbase (se 3 (by rfl) ⟨302288, by rfl⟩ : syracuseStep 1612205 = 604577) (by norm_num)
theorem B1612277 : Blo 714321 1612277 := bbase (se 5 (by rfl) ⟨75575, by rfl⟩ : syracuseStep 1612277 = 151151) (by norm_num)
theorem B727553 : Blo 714321 727553 := bbase (se 2 (by rfl) ⟨272832, by rfl⟩ : syracuseStep 727553 = 545665) (by norm_num)
theorem B1612349 : Blo 714321 1612349 := bbase (se 3 (by rfl) ⟨302315, by rfl⟩ : syracuseStep 1612349 = 604631) (by norm_num)
theorem B1809013 : Blo 714321 1809013 := bbase (se 5 (by rfl) ⟨84797, by rfl⟩ : syracuseStep 1809013 = 169595) (by norm_num)
theorem B1612421 : Blo 714321 1612421 := bbase (se 4 (by rfl) ⟨151164, by rfl⟩ : syracuseStep 1612421 = 302329) (by norm_num)
theorem B2038421 : Blo 714321 2038421 := bbase (se 6 (by rfl) ⟨47775, by rfl⟩ : syracuseStep 2038421 = 95551) (by norm_num)
theorem B2726581 : Blo 714321 2726581 := bbase (se 5 (by rfl) ⟨127808, by rfl⟩ : syracuseStep 2726581 = 255617) (by norm_num)
theorem B1022645 : Blo 714321 1022645 := bbase (se 5 (by rfl) ⟨47936, by rfl⟩ : syracuseStep 1022645 = 95873) (by norm_num)
theorem B1612493 : Blo 714321 1612493 := bbase (se 3 (by rfl) ⟨302342, by rfl⟩ : syracuseStep 1612493 = 604685) (by norm_num)
theorem B1809125 : Blo 714321 1809125 := bbase (se 4 (by rfl) ⟨169605, by rfl⟩ : syracuseStep 1809125 = 339211) (by norm_num)
theorem B727813 : Blo 714321 727813 := bbase (se 4 (by rfl) ⟨68232, by rfl⟩ : syracuseStep 727813 = 136465) (by norm_num)
theorem B1612565 : Blo 714321 1612565 := bbase (se 6 (by rfl) ⟨37794, by rfl⟩ : syracuseStep 1612565 = 75589) (by norm_num)
theorem B1612637 : Blo 714321 1612637 := bbase (se 3 (by rfl) ⟨302369, by rfl⟩ : syracuseStep 1612637 = 604739) (by norm_num)
theorem B1809317 : Blo 714321 1809317 := bbase (se 4 (by rfl) ⟨169623, by rfl⟩ : syracuseStep 1809317 = 339247) (by norm_num)
theorem B1612709 : Blo 714321 1612709 := bbase (se 4 (by rfl) ⟨151191, by rfl⟩ : syracuseStep 1612709 = 302383) (by norm_num)
theorem B2726885 : Blo 714321 2726885 := bbase (se 4 (by rfl) ⟨255645, by rfl⟩ : syracuseStep 2726885 = 511291) (by norm_num)
theorem B1612781 : Blo 714321 1612781 := bbase (se 3 (by rfl) ⟨302396, by rfl⟩ : syracuseStep 1612781 = 604793) (by norm_num)
theorem B1514501 : Blo 714321 1514501 := bbase (se 4 (by rfl) ⟨141984, by rfl⟩ : syracuseStep 1514501 = 283969) (by norm_num)
theorem B1612853 : Blo 714321 1612853 := bbase (se 5 (by rfl) ⟨75602, by rfl⟩ : syracuseStep 1612853 = 151205) (by norm_num)
theorem B4594805 : Blo 714321 4594805 := bbase (se 5 (by rfl) ⟨215381, by rfl⟩ : syracuseStep 4594805 = 430763) (by norm_num)
theorem B1612925 : Blo 714321 1612925 := bbase (se 3 (by rfl) ⟨302423, by rfl⟩ : syracuseStep 1612925 = 604847) (by norm_num)
theorem B1612997 : Blo 714321 1612997 := bbase (se 4 (by rfl) ⟨151218, by rfl⟩ : syracuseStep 1612997 = 302437) (by norm_num)
theorem B4070645 : Blo 714321 4070645 := bbase (se 5 (by rfl) ⟨190811, by rfl⟩ : syracuseStep 4070645 = 381623) (by norm_num)
theorem B1809661 : Blo 714321 1809661 := bbase (se 3 (by rfl) ⟨339311, by rfl⟩ : syracuseStep 1809661 = 678623) (by norm_num)
theorem B1613069 : Blo 714321 1613069 := bbase (se 3 (by rfl) ⟨302450, by rfl⟩ : syracuseStep 1613069 = 604901) (by norm_num)
theorem B859421 : Blo 714321 859421 := bbase (se 3 (by rfl) ⟨161141, by rfl⟩ : syracuseStep 859421 = 322283) (by norm_num)
theorem B2792789 : Blo 714321 2792789 := bbase (se 11 (by rfl) ⟨2045, by rfl⟩ : syracuseStep 2792789 = 4091) (by norm_num)
theorem B1613141 : Blo 714321 1613141 := bbase (se 11 (by rfl) ⟨1181, by rfl⟩ : syracuseStep 1613141 = 2363) (by norm_num)
theorem B1809773 : Blo 714321 1809773 := bbase (se 3 (by rfl) ⟨339332, by rfl⟩ : syracuseStep 1809773 = 678665) (by norm_num)
theorem B1613213 : Blo 714321 1613213 := bbase (se 3 (by rfl) ⟨302477, by rfl⟩ : syracuseStep 1613213 = 604955) (by norm_num)
theorem B1613285 : Blo 714321 1613285 := bbase (se 4 (by rfl) ⟨151245, by rfl⟩ : syracuseStep 1613285 = 302491) (by norm_num)
theorem B859681 : Blo 714321 859681 := bbase (se 2 (by rfl) ⟨322380, by rfl⟩ : syracuseStep 859681 = 644761) (by norm_num)
theorem B1809965 : Blo 714321 1809965 := bbase (se 3 (by rfl) ⟨339368, by rfl⟩ : syracuseStep 1809965 = 678737) (by norm_num)
theorem B1613357 : Blo 714321 1613357 := bbase (se 3 (by rfl) ⟨302504, by rfl⟩ : syracuseStep 1613357 = 605009) (by norm_num)
theorem B859729 : Blo 714321 859729 := bbase (se 2 (by rfl) ⟨322398, by rfl⟩ : syracuseStep 859729 = 644797) (by norm_num)
theorem B1613429 : Blo 714321 1613429 := bbase (se 5 (by rfl) ⟨75629, by rfl⟩ : syracuseStep 1613429 = 151259) (by norm_num)
theorem B1613501 : Blo 714321 1613501 := bbase (se 3 (by rfl) ⟨302531, by rfl⟩ : syracuseStep 1613501 = 605063) (by norm_num)
theorem B3448565 : Blo 714321 3448565 := bbase (se 5 (by rfl) ⟨161651, by rfl⟩ : syracuseStep 3448565 = 323303) (by norm_num)
theorem B1613573 : Blo 714321 1613573 := bbase (se 4 (by rfl) ⟨151272, by rfl⟩ : syracuseStep 1613573 = 302545) (by norm_num)
theorem B1613645 : Blo 714321 1613645 := bbase (se 3 (by rfl) ⟨302558, by rfl⟩ : syracuseStep 1613645 = 605117) (by norm_num)
theorem B3055445 : Blo 714321 3055445 := bbase (se 9 (by rfl) ⟨8951, by rfl⟩ : syracuseStep 3055445 = 17903) (by norm_num)
theorem B1679197 : Blo 714321 1679197 := bbase (se 3 (by rfl) ⟨314849, by rfl⟩ : syracuseStep 1679197 = 629699) (by norm_num)
theorem B1810309 : Blo 714321 1810309 := bbase (se 4 (by rfl) ⟨169716, by rfl⟩ : syracuseStep 1810309 = 339433) (by norm_num)
theorem B1613717 : Blo 714321 1613717 := bbase (se 6 (by rfl) ⟨37821, by rfl⟩ : syracuseStep 1613717 = 75643) (by norm_num)
theorem B5447573 : Blo 714321 5447573 := bbase (se 6 (by rfl) ⟨127677, by rfl⟩ : syracuseStep 5447573 = 255355) (by norm_num)
theorem B1089445 : Blo 714321 1089445 := bbase (se 4 (by rfl) ⟨102135, by rfl⟩ : syracuseStep 1089445 = 204271) (by norm_num)
theorem B5152693 : Blo 714321 5152693 := bbase (se 5 (by rfl) ⟨241532, by rfl⟩ : syracuseStep 5152693 = 483065) (by norm_num)
theorem B1613789 : Blo 714321 1613789 := bbase (se 3 (by rfl) ⟨302585, by rfl⟩ : syracuseStep 1613789 = 605171) (by norm_num)
theorem B1810421 : Blo 714321 1810421 := bbase (se 5 (by rfl) ⟨84863, by rfl⟩ : syracuseStep 1810421 = 169727) (by norm_num)
theorem B1613861 : Blo 714321 1613861 := bbase (se 4 (by rfl) ⟨151299, by rfl⟩ : syracuseStep 1613861 = 302599) (by norm_num)
theorem B1613933 : Blo 714321 1613933 := bbase (se 3 (by rfl) ⟨302612, by rfl⟩ : syracuseStep 1613933 = 605225) (by norm_num)
theorem B5152949 : Blo 714321 5152949 := bbase (se 5 (by rfl) ⟨241544, by rfl⟩ : syracuseStep 5152949 = 483089) (by norm_num)
theorem B1810613 : Blo 714321 1810613 := bbase (se 5 (by rfl) ⟨84872, by rfl⟩ : syracuseStep 1810613 = 169745) (by norm_num)
theorem B1614005 : Blo 714321 1614005 := bbase (se 5 (by rfl) ⟨75656, by rfl⟩ : syracuseStep 1614005 = 151313) (by norm_num)
theorem B2040005 : Blo 714321 2040005 := bbase (se 4 (by rfl) ⟨191250, by rfl⟩ : syracuseStep 2040005 = 382501) (by norm_num)
theorem B1745101 : Blo 714321 1745101 := bbase (se 3 (by rfl) ⟨327206, by rfl⟩ : syracuseStep 1745101 = 654413) (by norm_num)
theorem B860401 : Blo 714321 860401 := bbase (se 2 (by rfl) ⟨322650, by rfl⟩ : syracuseStep 860401 = 645301) (by norm_num)
theorem B827641 : Blo 714321 827641 := bbase (se 2 (by rfl) ⟨310365, by rfl⟩ : syracuseStep 827641 = 620731) (by norm_num)
theorem B1614077 : Blo 714321 1614077 := bbase (se 3 (by rfl) ⟨302639, by rfl⟩ : syracuseStep 1614077 = 605279) (by norm_num)
theorem B1614149 : Blo 714321 1614149 := bbase (se 4 (by rfl) ⟨151326, by rfl⟩ : syracuseStep 1614149 = 302653) (by norm_num)
theorem B1614221 : Blo 714321 1614221 := bbase (se 3 (by rfl) ⟨302666, by rfl⟩ : syracuseStep 1614221 = 605333) (by norm_num)
theorem B4071829 : Blo 714321 4071829 := bbase (se 6 (by rfl) ⟨95433, by rfl⟩ : syracuseStep 4071829 = 190867) (by norm_num)
theorem B1614293 : Blo 714321 1614293 := bbase (se 7 (by rfl) ⟨18917, by rfl⟩ : syracuseStep 1614293 = 37835) (by norm_num)
theorem B1450469 : Blo 714321 1450469 := bbase (se 4 (by rfl) ⟨135981, by rfl⟩ : syracuseStep 1450469 = 271963) (by norm_num)
theorem B1810957 : Blo 714321 1810957 := bbase (se 3 (by rfl) ⟨339554, by rfl⟩ : syracuseStep 1810957 = 679109) (by norm_num)
theorem B1614365 : Blo 714321 1614365 := bbase (se 3 (by rfl) ⟨302693, by rfl⟩ : syracuseStep 1614365 = 605387) (by norm_num)
theorem B1450565 : Blo 714321 1450565 := bbase (se 4 (by rfl) ⟨135990, by rfl⟩ : syracuseStep 1450565 = 271981) (by norm_num)
theorem B1614437 : Blo 714321 1614437 := bbase (se 4 (by rfl) ⟨151353, by rfl⟩ : syracuseStep 1614437 = 302707) (by norm_num)
theorem B1811069 : Blo 714321 1811069 := bbase (se 3 (by rfl) ⟨339575, by rfl⟩ : syracuseStep 1811069 = 679151) (by norm_num)
theorem B1614509 : Blo 714321 1614509 := bbase (se 3 (by rfl) ⟨302720, by rfl⟩ : syracuseStep 1614509 = 605441) (by norm_num)
theorem B1614581 : Blo 714321 1614581 := bbase (se 5 (by rfl) ⟨75683, by rfl⟩ : syracuseStep 1614581 = 151367) (by norm_num)
theorem B1811261 : Blo 714321 1811261 := bbase (se 3 (by rfl) ⟨339611, by rfl⟩ : syracuseStep 1811261 = 679223) (by norm_num)
theorem B1614653 : Blo 714321 1614653 := bbase (se 3 (by rfl) ⟨302747, by rfl⟩ : syracuseStep 1614653 = 605495) (by norm_num)
theorem B2040677 : Blo 714321 2040677 := bbase (se 4 (by rfl) ⟨191313, by rfl⟩ : syracuseStep 2040677 = 382627) (by norm_num)
theorem B1614725 : Blo 714321 1614725 := bbase (se 4 (by rfl) ⟨151380, by rfl⟩ : syracuseStep 1614725 = 302761) (by norm_num)
theorem B1614797 : Blo 714321 1614797 := bbase (se 3 (by rfl) ⟨302774, by rfl⟩ : syracuseStep 1614797 = 605549) (by norm_num)
theorem B1614869 : Blo 714321 1614869 := bbase (se 6 (by rfl) ⟨37848, by rfl⟩ : syracuseStep 1614869 = 75697) (by norm_num)
theorem B1090613 : Blo 714321 1090613 := bbase (se 5 (by rfl) ⟨51122, by rfl⟩ : syracuseStep 1090613 = 102245) (by norm_num)
theorem B5022805 : Blo 714321 5022805 := bbase (se 8 (by rfl) ⟨29430, by rfl⟩ : syracuseStep 5022805 = 58861) (by norm_num)
theorem B1614941 : Blo 714321 1614941 := bbase (se 3 (by rfl) ⟨302801, by rfl⟩ : syracuseStep 1614941 = 605603) (by norm_num)
theorem B1811605 : Blo 714321 1811605 := bbase (se 6 (by rfl) ⟨42459, by rfl⟩ : syracuseStep 1811605 = 84919) (by norm_num)
theorem B1615013 : Blo 714321 1615013 := bbase (se 4 (by rfl) ⟨151407, by rfl⟩ : syracuseStep 1615013 = 302815) (by norm_num)
theorem B861401 : Blo 714321 861401 := bbase (se 2 (by rfl) ⟨323025, by rfl⟩ : syracuseStep 861401 = 646051) (by norm_num)
theorem B1090789 : Blo 714321 1090789 := bbase (se 4 (by rfl) ⟨102261, by rfl⟩ : syracuseStep 1090789 = 204523) (by norm_num)
theorem B1615085 : Blo 714321 1615085 := bbase (se 3 (by rfl) ⟨302828, by rfl⟩ : syracuseStep 1615085 = 605657) (by norm_num)
theorem B1811717 : Blo 714321 1811717 := bbase (se 4 (by rfl) ⟨169848, by rfl⟩ : syracuseStep 1811717 = 339697) (by norm_num)
theorem B2041109 : Blo 714321 2041109 := bbase (se 6 (by rfl) ⟨47838, by rfl⟩ : syracuseStep 2041109 = 95677) (by norm_num)
theorem B861473 : Blo 714321 861473 := bbase (se 2 (by rfl) ⟨323052, by rfl⟩ : syracuseStep 861473 = 646105) (by norm_num)
theorem B1615157 : Blo 714321 1615157 := bbase (se 5 (by rfl) ⟨75710, by rfl⟩ : syracuseStep 1615157 = 151421) (by norm_num)
theorem B1287517 : Blo 714321 1287517 := bbase (se 3 (by rfl) ⟨241409, by rfl⟩ : syracuseStep 1287517 = 482819) (by norm_num)
theorem B763229 : Blo 714321 763229 := bbase (se 3 (by rfl) ⟨143105, by rfl⟩ : syracuseStep 763229 = 286211) (by norm_num)
theorem B1615229 : Blo 714321 1615229 := bbase (se 3 (by rfl) ⟨302855, by rfl⟩ : syracuseStep 1615229 = 605711) (by norm_num)
theorem B1811909 : Blo 714321 1811909 := bbase (se 4 (by rfl) ⟨169866, by rfl⟩ : syracuseStep 1811909 = 339733) (by norm_num)
theorem B1615301 : Blo 714321 1615301 := bbase (se 4 (by rfl) ⟨151434, by rfl⟩ : syracuseStep 1615301 = 302869) (by norm_num)
theorem B1287677 : Blo 714321 1287677 := bbase (se 3 (by rfl) ⟨241439, by rfl⟩ : syracuseStep 1287677 = 482879) (by norm_num)
theorem B1615373 : Blo 714321 1615373 := bbase (se 3 (by rfl) ⟨302882, by rfl⟩ : syracuseStep 1615373 = 605765) (by norm_num)
theorem B861781 : Blo 714321 861781 := bbase (se 8 (by rfl) ⟨5049, by rfl⟩ : syracuseStep 861781 = 10099) (by norm_num)
theorem B1615445 : Blo 714321 1615445 := bbase (se 8 (by rfl) ⟨9465, by rfl⟩ : syracuseStep 1615445 = 18931) (by norm_num)
theorem B1615517 : Blo 714321 1615517 := bbase (se 3 (by rfl) ⟨302909, by rfl⟩ : syracuseStep 1615517 = 605819) (by norm_num)
theorem B8169173 : Blo 714321 8169173 := bbase (se 7 (by rfl) ⟨95732, by rfl⟩ : syracuseStep 8169173 = 191465) (by norm_num)
theorem B1615589 : Blo 714321 1615589 := bbase (se 4 (by rfl) ⟨151461, by rfl⟩ : syracuseStep 1615589 = 302923) (by norm_num)
theorem B861949 : Blo 714321 861949 := bbase (se 3 (by rfl) ⟨161615, by rfl⟩ : syracuseStep 861949 = 323231) (by norm_num)
theorem B763673 : Blo 714321 763673 := bbase (se 2 (by rfl) ⟨286377, by rfl⟩ : syracuseStep 763673 = 572755) (by norm_num)
theorem B1812253 : Blo 714321 1812253 := bbase (se 3 (by rfl) ⟨339797, by rfl⟩ : syracuseStep 1812253 = 679595) (by norm_num)
theorem B861997 : Blo 714321 861997 := bbase (se 3 (by rfl) ⟨161624, by rfl⟩ : syracuseStep 861997 = 323249) (by norm_num)
theorem B1615661 : Blo 714321 1615661 := bbase (se 3 (by rfl) ⟨302936, by rfl⟩ : syracuseStep 1615661 = 605873) (by norm_num)
theorem B1615733 : Blo 714321 1615733 := bbase (se 5 (by rfl) ⟨75737, by rfl⟩ : syracuseStep 1615733 = 151475) (by norm_num)
theorem B1812365 : Blo 714321 1812365 := bbase (se 3 (by rfl) ⟨339818, by rfl⟩ : syracuseStep 1812365 = 679637) (by norm_num)
theorem B862093 : Blo 714321 862093 := bbase (se 3 (by rfl) ⟨161642, by rfl⟩ : syracuseStep 862093 = 323285) (by norm_num)
theorem B1615805 : Blo 714321 1615805 := bbase (se 3 (by rfl) ⟨302963, by rfl⟩ : syracuseStep 1615805 = 605927) (by norm_num)
theorem B2041861 : Blo 714321 2041861 := bbase (se 4 (by rfl) ⟨191424, by rfl⟩ : syracuseStep 2041861 = 382849) (by norm_num)
theorem B1615877 : Blo 714321 1615877 := bbase (se 4 (by rfl) ⟨151488, by rfl⟩ : syracuseStep 1615877 = 302977) (by norm_num)
theorem B763921 : Blo 714321 763921 := bbase (se 2 (by rfl) ⟨286470, by rfl⟩ : syracuseStep 763921 = 572941) (by norm_num)
theorem B1812557 : Blo 714321 1812557 := bbase (se 3 (by rfl) ⟨339854, by rfl⟩ : syracuseStep 1812557 = 679709) (by norm_num)
theorem B1615949 : Blo 714321 1615949 := bbase (se 3 (by rfl) ⟨302990, by rfl⟩ : syracuseStep 1615949 = 605981) (by norm_num)
theorem B1616021 : Blo 714321 1616021 := bbase (se 6 (by rfl) ⟨37875, by rfl⟩ : syracuseStep 1616021 = 75751) (by norm_num)
theorem B8726741 : Blo 714321 8726741 := bbase (se 7 (by rfl) ⟨102266, by rfl⟩ : syracuseStep 8726741 = 204533) (by norm_num)
theorem B1616093 : Blo 714321 1616093 := bbase (se 3 (by rfl) ⟨303017, by rfl⟩ : syracuseStep 1616093 = 606035) (by norm_num)
theorem B1616165 : Blo 714321 1616165 := bbase (se 4 (by rfl) ⟨151515, by rfl⟩ : syracuseStep 1616165 = 303031) (by norm_num)
theorem B4073813 : Blo 714321 4073813 := bbase (se 10 (by rfl) ⟨5967, by rfl⟩ : syracuseStep 4073813 = 11935) (by norm_num)
theorem B1812901 : Blo 714321 1812901 := bbase (se 4 (by rfl) ⟨169959, by rfl⟩ : syracuseStep 1812901 = 339919) (by norm_num)
theorem B764353 : Blo 714321 764353 := bbase (se 2 (by rfl) ⟨286632, by rfl⟩ : syracuseStep 764353 = 573265) (by norm_num)
theorem B862669 : Blo 714321 862669 := bbase (se 3 (by rfl) ⟨161750, by rfl⟩ : syracuseStep 862669 = 323501) (by norm_num)
theorem B6105557 : Blo 714321 6105557 := bbase (se 7 (by rfl) ⟨71549, by rfl⟩ : syracuseStep 6105557 = 143099) (by norm_num)
theorem B764425 : Blo 714321 764425 := bbase (se 2 (by rfl) ⟨286659, by rfl⟩ : syracuseStep 764425 = 573319) (by norm_num)
theorem B1813013 : Blo 714321 1813013 := bbase (se 6 (by rfl) ⟨42492, by rfl⟩ : syracuseStep 1813013 = 84985) (by norm_num)
theorem B1288757 : Blo 714321 1288757 := bbase (se 5 (by rfl) ⟨60410, by rfl⟩ : syracuseStep 1288757 = 120821) (by norm_num)
theorem B797245 : Blo 714321 797245 := bbase (se 3 (by rfl) ⟨149483, by rfl⟩ : syracuseStep 797245 = 298967) (by norm_num)
theorem B830017 : Blo 714321 830017 := bbase (se 2 (by rfl) ⟨311256, by rfl⟩ : syracuseStep 830017 = 622513) (by norm_num)
theorem B797293 : Blo 714321 797293 := bbase (se 3 (by rfl) ⟨149492, by rfl⟩ : syracuseStep 797293 = 298985) (by norm_num)
theorem B1288901 : Blo 714321 1288901 := bbase (se 4 (by rfl) ⟨120834, by rfl⟩ : syracuseStep 1288901 = 241669) (by norm_num)
theorem B1813205 : Blo 714321 1813205 := bbase (se 7 (by rfl) ⟨21248, by rfl⟩ : syracuseStep 1813205 = 42497) (by norm_num)
theorem B1452829 : Blo 714321 1452829 := bbase (se 3 (by rfl) ⟨272405, by rfl⟩ : syracuseStep 1452829 = 544811) (by norm_num)
theorem B764797 : Blo 714321 764797 := bbase (se 3 (by rfl) ⟨143399, by rfl⟩ : syracuseStep 764797 = 286799) (by norm_num)
theorem B1813549 : Blo 714321 1813549 := bbase (se 3 (by rfl) ⟨340040, by rfl⟩ : syracuseStep 1813549 = 680081) (by norm_num)
theorem B1813661 : Blo 714321 1813661 := bbase (se 3 (by rfl) ⟨340061, by rfl⟩ : syracuseStep 1813661 = 680123) (by norm_num)
theorem B765173 : Blo 714321 765173 := bbase (se 5 (by rfl) ⟨35867, by rfl⟩ : syracuseStep 765173 = 71735) (by norm_num)
theorem B765245 : Blo 714321 765245 := bbase (se 3 (by rfl) ⟨143483, by rfl⟩ : syracuseStep 765245 = 286967) (by norm_num)
theorem B1813853 : Blo 714321 1813853 := bbase (se 3 (by rfl) ⟨340097, by rfl⟩ : syracuseStep 1813853 = 680195) (by norm_num)
theorem B1453501 : Blo 714321 1453501 := bbase (se 3 (by rfl) ⟨272531, by rfl⟩ : syracuseStep 1453501 = 545063) (by norm_num)
theorem B765433 : Blo 714321 765433 := bbase (se 2 (by rfl) ⟨287037, by rfl⟩ : syracuseStep 765433 = 574075) (by norm_num)
theorem B3616325 : Blo 714321 3616325 := bbase (se 4 (by rfl) ⟨339030, by rfl⟩ : syracuseStep 3616325 = 678061) (by norm_num)
theorem B1748645 : Blo 714321 1748645 := bbase (se 4 (by rfl) ⟨163935, by rfl⟩ : syracuseStep 1748645 = 327871) (by norm_num)
theorem B765617 : Blo 714321 765617 := bbase (se 2 (by rfl) ⟨287106, by rfl⟩ : syracuseStep 765617 = 574213) (by norm_num)
theorem B1814197 : Blo 714321 1814197 := bbase (se 5 (by rfl) ⟨85040, by rfl⟩ : syracuseStep 1814197 = 170081) (by norm_num)
theorem B3059477 : Blo 714321 3059477 := bbase (se 6 (by rfl) ⟨71706, by rfl⟩ : syracuseStep 3059477 = 143413) (by norm_num)
theorem B1814309 : Blo 714321 1814309 := bbase (se 4 (by rfl) ⟨170091, by rfl⟩ : syracuseStep 1814309 = 340183) (by norm_num)
theorem B1814501 : Blo 714321 1814501 := bbase (se 4 (by rfl) ⟨170109, by rfl⟩ : syracuseStep 1814501 = 340219) (by norm_num)
theorem B1814845 : Blo 714321 1814845 := bbase (se 3 (by rfl) ⟨340283, by rfl⟩ : syracuseStep 1814845 = 680567) (by norm_num)
theorem B766369 : Blo 714321 766369 := bbase (se 2 (by rfl) ⟨287388, by rfl⟩ : syracuseStep 766369 = 574777) (by norm_num)
theorem B1814957 : Blo 714321 1814957 := bbase (se 3 (by rfl) ⟨340304, by rfl⟩ : syracuseStep 1814957 = 680609) (by norm_num)
theorem B766441 : Blo 714321 766441 := bbase (se 2 (by rfl) ⟨287415, by rfl⟩ : syracuseStep 766441 = 574831) (by norm_num)
theorem B4076021 : Blo 714321 4076021 := bbase (se 5 (by rfl) ⟨191063, by rfl⟩ : syracuseStep 4076021 = 382127) (by norm_num)
theorem B9777685 : Blo 714321 9777685 := bbase (se 6 (by rfl) ⟨229164, by rfl⟩ : syracuseStep 9777685 = 458329) (by norm_num)
theorem B1454669 : Blo 714321 1454669 := bbase (se 3 (by rfl) ⟨272750, by rfl⟩ : syracuseStep 1454669 = 545501) (by norm_num)
theorem B1356365 : Blo 714321 1356365 := bbase (se 3 (by rfl) ⟨254318, by rfl⟩ : syracuseStep 1356365 = 508637) (by norm_num)
theorem B1815149 : Blo 714321 1815149 := bbase (se 3 (by rfl) ⟨340340, by rfl⟩ : syracuseStep 1815149 = 680681) (by norm_num)
theorem B766621 : Blo 714321 766621 := bbase (se 3 (by rfl) ⟨143741, by rfl⟩ : syracuseStep 766621 = 287483) (by norm_num)
theorem B2175653 : Blo 714321 2175653 := bbase (se 4 (by rfl) ⟨203967, by rfl⟩ : syracuseStep 2175653 = 407935) (by norm_num)
theorem B1356517 : Blo 714321 1356517 := bbase (se 4 (by rfl) ⟨127173, by rfl⟩ : syracuseStep 1356517 = 254347) (by norm_num)
theorem B1716997 : Blo 714321 1716997 := bbase (se 4 (by rfl) ⟨160968, by rfl⟩ : syracuseStep 1716997 = 321937) (by norm_num)
theorem B2044709 : Blo 714321 2044709 := bbase (se 4 (by rfl) ⟨191691, by rfl⟩ : syracuseStep 2044709 = 383383) (by norm_num)
theorem B3617621 : Blo 714321 3617621 := bbase (se 9 (by rfl) ⟨10598, by rfl⟩ : syracuseStep 3617621 = 21197) (by norm_num)
theorem B897953 : Blo 714321 897953 := bbase (se 2 (by rfl) ⟨336732, by rfl⟩ : syracuseStep 897953 = 673465) (by norm_num)
theorem B1160101 : Blo 714321 1160101 := bbase (se 4 (by rfl) ⟨108759, by rfl⟩ : syracuseStep 1160101 = 217519) (by norm_num)
theorem B1815493 : Blo 714321 1815493 := bbase (se 4 (by rfl) ⟨170202, by rfl⟩ : syracuseStep 1815493 = 340405) (by norm_num)
theorem B930793 : Blo 714321 930793 := bbase (se 2 (by rfl) ⟨349047, by rfl⟩ : syracuseStep 930793 = 698095) (by norm_num)
theorem B1356821 : Blo 714321 1356821 := bbase (se 6 (by rfl) ⟨31800, by rfl⟩ : syracuseStep 1356821 = 63601) (by norm_num)
theorem B1815605 : Blo 714321 1815605 := bbase (se 5 (by rfl) ⟨85106, by rfl⟩ : syracuseStep 1815605 = 170213) (by norm_num)
theorem B767065 : Blo 714321 767065 := bbase (se 2 (by rfl) ⟨287649, by rfl⟩ : syracuseStep 767065 = 575299) (by norm_num)
theorem B1455293 : Blo 714321 1455293 := bbase (se 3 (by rfl) ⟨272867, by rfl⟩ : syracuseStep 1455293 = 545735) (by norm_num)
theorem B1815797 : Blo 714321 1815797 := bbase (se 5 (by rfl) ⟨85115, by rfl⟩ : syracuseStep 1815797 = 170231) (by norm_num)
theorem B1717517 : Blo 714321 1717517 := bbase (se 3 (by rfl) ⟨322034, by rfl⟩ : syracuseStep 1717517 = 644069) (by norm_num)
theorem B6108533 : Blo 714321 6108533 := bbase (se 5 (by rfl) ⟨286337, by rfl⟩ : syracuseStep 6108533 = 572675) (by norm_num)
theorem B3061253 : Blo 714321 3061253 := bbase (se 4 (by rfl) ⟨286992, by rfl⟩ : syracuseStep 3061253 = 573985) (by norm_num)
theorem B5879317 : Blo 714321 5879317 := bbase (se 6 (by rfl) ⟨137796, by rfl⟩ : syracuseStep 5879317 = 275593) (by norm_num)
theorem B1816141 : Blo 714321 1816141 := bbase (se 3 (by rfl) ⟨340526, by rfl⟩ : syracuseStep 1816141 = 681053) (by norm_num)
theorem B1717901 : Blo 714321 1717901 := bbase (se 3 (by rfl) ⟨322106, by rfl⟩ : syracuseStep 1717901 = 644213) (by norm_num)
theorem B1717949 : Blo 714321 1717949 := bbase (se 3 (by rfl) ⟨322115, by rfl⟩ : syracuseStep 1717949 = 644231) (by norm_num)
theorem B1816253 : Blo 714321 1816253 := bbase (se 3 (by rfl) ⟨340547, by rfl⟩ : syracuseStep 1816253 = 681095) (by norm_num)
theorem B1717957 : Blo 714321 1717957 := bbase (se 4 (by rfl) ⟨161058, by rfl⟩ : syracuseStep 1717957 = 322117) (by norm_num)
theorem B1357573 : Blo 714321 1357573 := bbase (se 4 (by rfl) ⟨127272, by rfl⟩ : syracuseStep 1357573 = 254545) (by norm_num)
theorem B1816445 : Blo 714321 1816445 := bbase (se 3 (by rfl) ⟨340583, by rfl⟩ : syracuseStep 1816445 = 681167) (by norm_num)
theorem B1161101 : Blo 714321 1161101 := bbase (se 3 (by rfl) ⟨217706, by rfl⟩ : syracuseStep 1161101 = 435413) (by norm_num)
theorem B1357717 : Blo 714321 1357717 := bbase (se 6 (by rfl) ⟨31821, by rfl⟩ : syracuseStep 1357717 = 63643) (by norm_num)
theorem B1357877 : Blo 714321 1357877 := bbase (se 5 (by rfl) ⟨63650, by rfl⟩ : syracuseStep 1357877 = 127301) (by norm_num)
theorem B1554509 : Blo 714321 1554509 := bbase (se 3 (by rfl) ⟨291470, by rfl⟩ : syracuseStep 1554509 = 582941) (by norm_num)
theorem B8697941 : Blo 714321 8697941 := bbase (se 8 (by rfl) ⟨50964, by rfl⟩ : syracuseStep 8697941 = 101929) (by norm_num)
theorem B3618917 : Blo 714321 3618917 := bbase (se 4 (by rfl) ⟨339273, by rfl⟩ : syracuseStep 3618917 = 678547) (by norm_num)
theorem B1358021 : Blo 714321 1358021 := bbase (se 4 (by rfl) ⟨127314, by rfl⟩ : syracuseStep 1358021 = 254629) (by norm_num)
theorem B1816789 : Blo 714321 1816789 := bbase (se 7 (by rfl) ⟨21290, by rfl⟩ : syracuseStep 1816789 = 42581) (by norm_num)
theorem B1816901 : Blo 714321 1816901 := bbase (se 4 (by rfl) ⟨170334, by rfl⟩ : syracuseStep 1816901 = 340669) (by norm_num)
theorem B1358309 : Blo 714321 1358309 := bbase (se 4 (by rfl) ⟨127341, by rfl⟩ : syracuseStep 1358309 = 254683) (by norm_num)
theorem B3062245 : Blo 714321 3062245 := bbase (se 4 (by rfl) ⟨287085, by rfl⟩ : syracuseStep 3062245 = 574171) (by norm_num)
theorem B1817093 : Blo 714321 1817093 := bbase (se 4 (by rfl) ⟨170352, by rfl⟩ : syracuseStep 1817093 = 340705) (by norm_num)
theorem B1358461 : Blo 714321 1358461 := bbase (se 3 (by rfl) ⟨254711, by rfl⟩ : syracuseStep 1358461 = 509423) (by norm_num)
theorem B1718957 : Blo 714321 1718957 := bbase (se 3 (by rfl) ⟨322304, by rfl⟩ : syracuseStep 1718957 = 644609) (by norm_num)
theorem B1817437 : Blo 714321 1817437 := bbase (se 3 (by rfl) ⟨340769, by rfl⟩ : syracuseStep 1817437 = 681539) (by norm_num)
theorem B1719149 : Blo 714321 1719149 := bbase (se 3 (by rfl) ⟨322340, by rfl⟩ : syracuseStep 1719149 = 644681) (by norm_num)
theorem B1358765 : Blo 714321 1358765 := bbase (se 3 (by rfl) ⟨254768, by rfl⟩ : syracuseStep 1358765 = 509537) (by norm_num)
theorem B1817549 : Blo 714321 1817549 := bbase (se 3 (by rfl) ⟨340790, by rfl⟩ : syracuseStep 1817549 = 681581) (by norm_num)
theorem B736337 : Blo 714321 736337 := bbase (se 2 (by rfl) ⟨276126, by rfl⟩ : syracuseStep 736337 = 552253) (by norm_num)
theorem B1817741 : Blo 714321 1817741 := bbase (se 3 (by rfl) ⟨340826, by rfl⟩ : syracuseStep 1817741 = 681653) (by norm_num)
theorem B3620213 : Blo 714321 3620213 := bbase (se 5 (by rfl) ⟨169697, by rfl⟩ : syracuseStep 3620213 = 339395) (by norm_num)
theorem B1293773 : Blo 714321 1293773 := bbase (se 3 (by rfl) ⟨242582, by rfl⟩ : syracuseStep 1293773 = 485165) (by norm_num)
theorem B1818085 : Blo 714321 1818085 := bbase (se 4 (by rfl) ⟨170445, by rfl⟩ : syracuseStep 1818085 = 340891) (by norm_num)
theorem B1818197 : Blo 714321 1818197 := bbase (se 8 (by rfl) ⟨10653, by rfl⟩ : syracuseStep 1818197 = 21307) (by norm_num)
theorem B736921 : Blo 714321 736921 := bbase (se 2 (by rfl) ⟨276345, by rfl⟩ : syracuseStep 736921 = 552691) (by norm_num)
theorem B1359517 : Blo 714321 1359517 := bbase (se 3 (by rfl) ⟨254909, by rfl⟩ : syracuseStep 1359517 = 509819) (by norm_num)
theorem B1359661 : Blo 714321 1359661 := bbase (se 3 (by rfl) ⟨254936, by rfl⟩ : syracuseStep 1359661 = 509873) (by norm_num)
theorem B1359821 : Blo 714321 1359821 := bbase (se 3 (by rfl) ⟨254966, by rfl⟩ : syracuseStep 1359821 = 509933) (by norm_num)
theorem B1359965 : Blo 714321 1359965 := bbase (se 3 (by rfl) ⟨254993, by rfl⟩ : syracuseStep 1359965 = 509987) (by norm_num)
theorem B6701173 : Blo 714321 6701173 := bbase (se 5 (by rfl) ⟨314117, by rfl⟩ : syracuseStep 6701173 = 628235) (by norm_num)
theorem B966925 : Blo 714321 966925 := bbase (se 3 (by rfl) ⟨181298, by rfl⟩ : syracuseStep 966925 = 362597) (by norm_num)
theorem B1360253 : Blo 714321 1360253 := bbase (se 3 (by rfl) ⟨255047, by rfl⟩ : syracuseStep 1360253 = 510095) (by norm_num)
theorem B5816789 : Blo 714321 5816789 := bbase (se 7 (by rfl) ⟨68165, by rfl⟩ : syracuseStep 5816789 = 136331) (by norm_num)
theorem B1360405 : Blo 714321 1360405 := bbase (se 6 (by rfl) ⟨31884, by rfl⟩ : syracuseStep 1360405 = 63769) (by norm_num)
theorem B3621509 : Blo 714321 3621509 := bbase (se 4 (by rfl) ⟨339516, by rfl⟩ : syracuseStep 3621509 = 679033) (by norm_num)
theorem B1721101 : Blo 714321 1721101 := bbase (se 3 (by rfl) ⟨322706, by rfl⟩ : syracuseStep 1721101 = 645413) (by norm_num)
theorem B3261221 : Blo 714321 3261221 := bbase (se 4 (by rfl) ⟨305739, by rfl⟩ : syracuseStep 3261221 = 611479) (by norm_num)
theorem B803641 : Blo 714321 803641 := bbase (se 2 (by rfl) ⟨301365, by rfl⟩ : syracuseStep 803641 = 602731) (by norm_num)
theorem B1360709 : Blo 714321 1360709 := bbase (se 4 (by rfl) ⟨127566, by rfl⟩ : syracuseStep 1360709 = 255133) (by norm_num)
theorem B803677 : Blo 714321 803677 := bbase (se 3 (by rfl) ⟨150689, by rfl⟩ : syracuseStep 803677 = 301379) (by norm_num)
theorem B803713 : Blo 714321 803713 := bbase (se 2 (by rfl) ⟨301392, by rfl⟩ : syracuseStep 803713 = 602785) (by norm_num)
theorem B803749 : Blo 714321 803749 := bbase (se 4 (by rfl) ⟨75351, by rfl⟩ : syracuseStep 803749 = 150703) (by norm_num)
theorem B803785 : Blo 714321 803785 := bbase (se 2 (by rfl) ⟨301419, by rfl⟩ : syracuseStep 803785 = 602839) (by norm_num)
theorem B15516629 : Blo 714321 15516629 := bbase (se 7 (by rfl) ⟨181835, by rfl⟩ : syracuseStep 15516629 = 363671) (by norm_num)
theorem B803821 : Blo 714321 803821 := bbase (se 3 (by rfl) ⟨150716, by rfl⟩ : syracuseStep 803821 = 301433) (by norm_num)
theorem B803857 : Blo 714321 803857 := bbase (se 2 (by rfl) ⟨301446, by rfl⟩ : syracuseStep 803857 = 602893) (by norm_num)
theorem B803893 : Blo 714321 803893 := bbase (se 5 (by rfl) ⟨37682, by rfl⟩ : syracuseStep 803893 = 75365) (by norm_num)
theorem B803929 : Blo 714321 803929 := bbase (se 2 (by rfl) ⟨301473, by rfl⟩ : syracuseStep 803929 = 602947) (by norm_num)
theorem B803965 : Blo 714321 803965 := bbase (se 3 (by rfl) ⟨150743, by rfl⟩ : syracuseStep 803965 = 301487) (by norm_num)
theorem B804001 : Blo 714321 804001 := bbase (se 2 (by rfl) ⟨301500, by rfl⟩ : syracuseStep 804001 = 603001) (by norm_num)
theorem B804037 : Blo 714321 804037 := bbase (se 4 (by rfl) ⟨75378, by rfl⟩ : syracuseStep 804037 = 150757) (by norm_num)
theorem B804073 : Blo 714321 804073 := bbase (se 2 (by rfl) ⟨301527, by rfl⟩ : syracuseStep 804073 = 603055) (by norm_num)
theorem B804109 : Blo 714321 804109 := bbase (se 3 (by rfl) ⟨150770, by rfl⟩ : syracuseStep 804109 = 301541) (by norm_num)
theorem B804145 : Blo 714321 804145 := bbase (se 2 (by rfl) ⟨301554, by rfl⟩ : syracuseStep 804145 = 603109) (by norm_num)
theorem B804181 : Blo 714321 804181 := bbase (se 12 (by rfl) ⟨294, by rfl⟩ : syracuseStep 804181 = 589) (by norm_num)
theorem B804217 : Blo 714321 804217 := bbase (se 2 (by rfl) ⟨301581, by rfl⟩ : syracuseStep 804217 = 603163) (by norm_num)
theorem B804253 : Blo 714321 804253 := bbase (se 3 (by rfl) ⟨150797, by rfl⟩ : syracuseStep 804253 = 301595) (by norm_num)
theorem B968125 : Blo 714321 968125 := bbase (se 3 (by rfl) ⟨181523, by rfl⟩ : syracuseStep 968125 = 363047) (by norm_num)
theorem B804289 : Blo 714321 804289 := bbase (se 2 (by rfl) ⟨301608, by rfl⟩ : syracuseStep 804289 = 603217) (by norm_num)
theorem B804325 : Blo 714321 804325 := bbase (se 4 (by rfl) ⟨75405, by rfl⟩ : syracuseStep 804325 = 150811) (by norm_num)
theorem B804361 : Blo 714321 804361 := bbase (se 2 (by rfl) ⟨301635, by rfl⟩ : syracuseStep 804361 = 603271) (by norm_num)
theorem B804397 : Blo 714321 804397 := bbase (se 3 (by rfl) ⟨150824, by rfl⟩ : syracuseStep 804397 = 301649) (by norm_num)
theorem B1361461 : Blo 714321 1361461 := bbase (se 5 (by rfl) ⟨63818, by rfl⟩ : syracuseStep 1361461 = 127637) (by norm_num)
theorem B804433 : Blo 714321 804433 := bbase (se 2 (by rfl) ⟨301662, by rfl⟩ : syracuseStep 804433 = 603325) (by norm_num)
theorem B804469 : Blo 714321 804469 := bbase (se 5 (by rfl) ⟨37709, by rfl⟩ : syracuseStep 804469 = 75419) (by norm_num)
theorem B968341 : Blo 714321 968341 := bbase (se 6 (by rfl) ⟨22695, by rfl⟩ : syracuseStep 968341 = 45391) (by norm_num)
theorem B804505 : Blo 714321 804505 := bbase (se 2 (by rfl) ⟨301689, by rfl⟩ : syracuseStep 804505 = 603379) (by norm_num)
theorem B804541 : Blo 714321 804541 := bbase (se 3 (by rfl) ⟨150851, by rfl⟩ : syracuseStep 804541 = 301703) (by norm_num)
theorem B1722053 : Blo 714321 1722053 := bbase (se 4 (by rfl) ⟨161442, by rfl⟩ : syracuseStep 1722053 = 322885) (by norm_num)
theorem B1361605 : Blo 714321 1361605 := bbase (se 4 (by rfl) ⟨127650, by rfl⟩ : syracuseStep 1361605 = 255301) (by norm_num)
theorem B804577 : Blo 714321 804577 := bbase (se 2 (by rfl) ⟨301716, by rfl⟩ : syracuseStep 804577 = 603433) (by norm_num)
theorem B1722109 : Blo 714321 1722109 := bbase (se 3 (by rfl) ⟨322895, by rfl⟩ : syracuseStep 1722109 = 645791) (by norm_num)
theorem B804613 : Blo 714321 804613 := bbase (se 4 (by rfl) ⟨75432, by rfl⟩ : syracuseStep 804613 = 150865) (by norm_num)
theorem B804649 : Blo 714321 804649 := bbase (se 2 (by rfl) ⟨301743, by rfl⟩ : syracuseStep 804649 = 603487) (by norm_num)
theorem B804685 : Blo 714321 804685 := bbase (se 3 (by rfl) ⟨150878, by rfl⟩ : syracuseStep 804685 = 301757) (by norm_num)
theorem B1361765 : Blo 714321 1361765 := bbase (se 4 (by rfl) ⟨127665, by rfl⟩ : syracuseStep 1361765 = 255331) (by norm_num)
theorem B804721 : Blo 714321 804721 := bbase (se 2 (by rfl) ⟨301770, by rfl⟩ : syracuseStep 804721 = 603541) (by norm_num)
theorem B804757 : Blo 714321 804757 := bbase (se 6 (by rfl) ⟨18861, by rfl⟩ : syracuseStep 804757 = 37723) (by norm_num)
theorem B3622805 : Blo 714321 3622805 := bbase (se 6 (by rfl) ⟨84909, by rfl⟩ : syracuseStep 3622805 = 169819) (by norm_num)
theorem B804793 : Blo 714321 804793 := bbase (se 2 (by rfl) ⟨301797, by rfl⟩ : syracuseStep 804793 = 603595) (by norm_num)
theorem B804829 : Blo 714321 804829 := bbase (se 3 (by rfl) ⟨150905, by rfl⟩ : syracuseStep 804829 = 301811) (by norm_num)
theorem B1361909 : Blo 714321 1361909 := bbase (se 5 (by rfl) ⟨63839, by rfl⟩ : syracuseStep 1361909 = 127679) (by norm_num)
theorem B804865 : Blo 714321 804865 := bbase (se 2 (by rfl) ⟨301824, by rfl⟩ : syracuseStep 804865 = 603649) (by norm_num)
theorem B804901 : Blo 714321 804901 := bbase (se 4 (by rfl) ⟨75459, by rfl⟩ : syracuseStep 804901 = 150919) (by norm_num)
theorem B804937 : Blo 714321 804937 := bbase (se 2 (by rfl) ⟨301851, by rfl⟩ : syracuseStep 804937 = 603703) (by norm_num)
theorem B804973 : Blo 714321 804973 := bbase (se 3 (by rfl) ⟨150932, by rfl⟩ : syracuseStep 804973 = 301865) (by norm_num)
theorem B1722485 : Blo 714321 1722485 := bbase (se 5 (by rfl) ⟨80741, by rfl⟩ : syracuseStep 1722485 = 161483) (by norm_num)
theorem B805009 : Blo 714321 805009 := bbase (se 2 (by rfl) ⟨301878, by rfl⟩ : syracuseStep 805009 = 603757) (by norm_num)
theorem B805045 : Blo 714321 805045 := bbase (se 5 (by rfl) ⟨37736, by rfl⟩ : syracuseStep 805045 = 75473) (by norm_num)
theorem B805081 : Blo 714321 805081 := bbase (se 2 (by rfl) ⟨301905, by rfl⟩ : syracuseStep 805081 = 603811) (by norm_num)
theorem B805117 : Blo 714321 805117 := bbase (se 3 (by rfl) ⟨150959, by rfl⟩ : syracuseStep 805117 = 301919) (by norm_num)
theorem B1362197 : Blo 714321 1362197 := bbase (se 6 (by rfl) ⟨31926, by rfl⟩ : syracuseStep 1362197 = 63853) (by norm_num)
theorem B805153 : Blo 714321 805153 := bbase (se 2 (by rfl) ⟨301932, by rfl⟩ : syracuseStep 805153 = 603865) (by norm_num)
theorem B805189 : Blo 714321 805189 := bbase (se 4 (by rfl) ⟨75486, by rfl⟩ : syracuseStep 805189 = 150973) (by norm_num)
theorem B1722725 : Blo 714321 1722725 := bbase (se 4 (by rfl) ⟨161505, by rfl⟩ : syracuseStep 1722725 = 323011) (by norm_num)
theorem B805225 : Blo 714321 805225 := bbase (se 2 (by rfl) ⟨301959, by rfl⟩ : syracuseStep 805225 = 603919) (by norm_num)
theorem B805261 : Blo 714321 805261 := bbase (se 3 (by rfl) ⟨150986, by rfl⟩ : syracuseStep 805261 = 301973) (by norm_num)
theorem B1362349 : Blo 714321 1362349 := bbase (se 3 (by rfl) ⟨255440, by rfl⟩ : syracuseStep 1362349 = 510881) (by norm_num)
theorem B805297 : Blo 714321 805297 := bbase (se 2 (by rfl) ⟨301986, by rfl⟩ : syracuseStep 805297 = 603973) (by norm_num)
theorem B805333 : Blo 714321 805333 := bbase (se 7 (by rfl) ⟨9437, by rfl⟩ : syracuseStep 805333 = 18875) (by norm_num)
theorem B805369 : Blo 714321 805369 := bbase (se 2 (by rfl) ⟨302013, by rfl⟩ : syracuseStep 805369 = 604027) (by norm_num)
theorem B805405 : Blo 714321 805405 := bbase (se 3 (by rfl) ⟨151013, by rfl⟩ : syracuseStep 805405 = 302027) (by norm_num)
theorem B2411045 : Blo 714321 2411045 := bbase (se 4 (by rfl) ⟨226035, by rfl⟩ : syracuseStep 2411045 = 452071) (by norm_num)
theorem B805441 : Blo 714321 805441 := bbase (se 2 (by rfl) ⟨302040, by rfl⟩ : syracuseStep 805441 = 604081) (by norm_num)
theorem B805477 : Blo 714321 805477 := bbase (se 4 (by rfl) ⟨75513, by rfl⟩ : syracuseStep 805477 = 151027) (by norm_num)
theorem B805513 : Blo 714321 805513 := bbase (se 2 (by rfl) ⟨302067, by rfl⟩ : syracuseStep 805513 = 604135) (by norm_num)
theorem B805549 : Blo 714321 805549 := bbase (se 3 (by rfl) ⟨151040, by rfl⟩ : syracuseStep 805549 = 302081) (by norm_num)
theorem B805585 : Blo 714321 805585 := bbase (se 2 (by rfl) ⟨302094, by rfl⟩ : syracuseStep 805585 = 604189) (by norm_num)
theorem B1362653 : Blo 714321 1362653 := bbase (se 3 (by rfl) ⟨255497, by rfl⟩ : syracuseStep 1362653 = 510995) (by norm_num)
theorem B805621 : Blo 714321 805621 := bbase (se 5 (by rfl) ⟨37763, by rfl⟩ : syracuseStep 805621 = 75527) (by norm_num)
theorem B805657 : Blo 714321 805657 := bbase (se 2 (by rfl) ⟨302121, by rfl⟩ : syracuseStep 805657 = 604243) (by norm_num)
theorem B969509 : Blo 714321 969509 := bbase (se 4 (by rfl) ⟨90891, by rfl⟩ : syracuseStep 969509 = 181783) (by norm_num)
theorem B805693 : Blo 714321 805693 := bbase (se 3 (by rfl) ⟨151067, by rfl⟩ : syracuseStep 805693 = 302135) (by norm_num)
theorem B805729 : Blo 714321 805729 := bbase (se 2 (by rfl) ⟨302148, by rfl⟩ : syracuseStep 805729 = 604297) (by norm_num)
theorem B1526629 : Blo 714321 1526629 := bbase (se 4 (by rfl) ⟨143121, by rfl⟩ : syracuseStep 1526629 = 286243) (by norm_num)
theorem B805765 : Blo 714321 805765 := bbase (se 4 (by rfl) ⟨75540, by rfl⟩ : syracuseStep 805765 = 151081) (by norm_num)
theorem B3492773 : Blo 714321 3492773 := bbase (se 4 (by rfl) ⟨327447, by rfl⟩ : syracuseStep 3492773 = 654895) (by norm_num)
theorem B805801 : Blo 714321 805801 := bbase (se 2 (by rfl) ⟨302175, by rfl⟩ : syracuseStep 805801 = 604351) (by norm_num)
theorem B904117 : Blo 714321 904117 := bbase (se 5 (by rfl) ⟨42380, by rfl⟩ : syracuseStep 904117 = 84761) (by norm_num)
theorem B805837 : Blo 714321 805837 := bbase (se 3 (by rfl) ⟨151094, by rfl⟩ : syracuseStep 805837 = 302189) (by norm_num)
theorem B2411477 : Blo 714321 2411477 := bbase (se 7 (by rfl) ⟨28259, by rfl⟩ : syracuseStep 2411477 = 56519) (by norm_num)
theorem B805873 : Blo 714321 805873 := bbase (se 2 (by rfl) ⟨302202, by rfl⟩ : syracuseStep 805873 = 604405) (by norm_num)
theorem B904213 : Blo 714321 904213 := bbase (se 6 (by rfl) ⟨21192, by rfl⟩ : syracuseStep 904213 = 42385) (by norm_num)
theorem B805909 : Blo 714321 805909 := bbase (se 6 (by rfl) ⟨18888, by rfl⟩ : syracuseStep 805909 = 37777) (by norm_num)
theorem B805945 : Blo 714321 805945 := bbase (se 2 (by rfl) ⟨302229, by rfl⟩ : syracuseStep 805945 = 604459) (by norm_num)
theorem B805981 : Blo 714321 805981 := bbase (se 3 (by rfl) ⟨151121, by rfl⟩ : syracuseStep 805981 = 302243) (by norm_num)
theorem B806017 : Blo 714321 806017 := bbase (se 2 (by rfl) ⟨302256, by rfl⟩ : syracuseStep 806017 = 604513) (by norm_num)
theorem B3624101 : Blo 714321 3624101 := bbase (se 4 (by rfl) ⟨339759, by rfl⟩ : syracuseStep 3624101 = 679519) (by norm_num)
theorem B806053 : Blo 714321 806053 := bbase (se 4 (by rfl) ⟨75567, by rfl⟩ : syracuseStep 806053 = 151135) (by norm_num)
theorem B904385 : Blo 714321 904385 := bbase (se 2 (by rfl) ⟨339144, by rfl⟩ : syracuseStep 904385 = 678289) (by norm_num)
theorem B806089 : Blo 714321 806089 := bbase (se 2 (by rfl) ⟨302283, by rfl⟩ : syracuseStep 806089 = 604567) (by norm_num)
theorem B1527005 : Blo 714321 1527005 := bbase (se 3 (by rfl) ⟨286313, by rfl⟩ : syracuseStep 1527005 = 572627) (by norm_num)
theorem B806125 : Blo 714321 806125 := bbase (se 3 (by rfl) ⟨151148, by rfl⟩ : syracuseStep 806125 = 302297) (by norm_num)
theorem B904441 : Blo 714321 904441 := bbase (se 2 (by rfl) ⟨339165, by rfl⟩ : syracuseStep 904441 = 678331) (by norm_num)
theorem B806161 : Blo 714321 806161 := bbase (se 2 (by rfl) ⟨302310, by rfl⟩ : syracuseStep 806161 = 604621) (by norm_num)
theorem B806197 : Blo 714321 806197 := bbase (se 5 (by rfl) ⟨37790, by rfl⟩ : syracuseStep 806197 = 75581) (by norm_num)
theorem B904537 : Blo 714321 904537 := bbase (se 2 (by rfl) ⟨339201, by rfl⟩ : syracuseStep 904537 = 678403) (by norm_num)
theorem B806233 : Blo 714321 806233 := bbase (se 2 (by rfl) ⟨302337, by rfl⟩ : syracuseStep 806233 = 604675) (by norm_num)
theorem B3067253 : Blo 714321 3067253 := bbase (se 5 (by rfl) ⟨143777, by rfl⟩ : syracuseStep 3067253 = 287555) (by norm_num)
theorem B806269 : Blo 714321 806269 := bbase (se 3 (by rfl) ⟨151175, by rfl⟩ : syracuseStep 806269 = 302351) (by norm_num)
theorem B2411909 : Blo 714321 2411909 := bbase (se 4 (by rfl) ⟨226116, by rfl⟩ : syracuseStep 2411909 = 452233) (by norm_num)
theorem B806305 : Blo 714321 806305 := bbase (se 2 (by rfl) ⟨302364, by rfl⟩ : syracuseStep 806305 = 604729) (by norm_num)
theorem B806341 : Blo 714321 806341 := bbase (se 4 (by rfl) ⟨75594, by rfl⟩ : syracuseStep 806341 = 151189) (by norm_num)
theorem B1363405 : Blo 714321 1363405 := bbase (se 3 (by rfl) ⟨255638, by rfl⟩ : syracuseStep 1363405 = 511277) (by norm_num)
theorem B806377 : Blo 714321 806377 := bbase (se 2 (by rfl) ⟨302391, by rfl⟩ : syracuseStep 806377 = 604783) (by norm_num)
theorem B904709 : Blo 714321 904709 := bbase (se 4 (by rfl) ⟨84816, by rfl⟩ : syracuseStep 904709 = 169633) (by norm_num)
theorem B806413 : Blo 714321 806413 := bbase (se 3 (by rfl) ⟨151202, by rfl⟩ : syracuseStep 806413 = 302405) (by norm_num)
theorem B806449 : Blo 714321 806449 := bbase (se 2 (by rfl) ⟨302418, by rfl⟩ : syracuseStep 806449 = 604837) (by norm_num)
theorem B904765 : Blo 714321 904765 := bbase (se 3 (by rfl) ⟨169643, by rfl⟩ : syracuseStep 904765 = 339287) (by norm_num)
theorem B970309 : Blo 714321 970309 := bbase (se 4 (by rfl) ⟨90966, by rfl⟩ : syracuseStep 970309 = 181933) (by norm_num)
theorem B806485 : Blo 714321 806485 := bbase (se 8 (by rfl) ⟨4725, by rfl⟩ : syracuseStep 806485 = 9451) (by norm_num)
theorem B1363549 : Blo 714321 1363549 := bbase (se 3 (by rfl) ⟨255665, by rfl⟩ : syracuseStep 1363549 = 511331) (by norm_num)
theorem B806521 : Blo 714321 806521 := bbase (se 2 (by rfl) ⟨302445, by rfl⟩ : syracuseStep 806521 = 604891) (by norm_num)
theorem B3067541 : Blo 714321 3067541 := bbase (se 6 (by rfl) ⟨71895, by rfl⟩ : syracuseStep 3067541 = 143791) (by norm_num)
theorem B904861 : Blo 714321 904861 := bbase (se 3 (by rfl) ⟨169661, by rfl⟩ : syracuseStep 904861 = 339323) (by norm_num)
theorem B806557 : Blo 714321 806557 := bbase (se 3 (by rfl) ⟨151229, by rfl⟩ : syracuseStep 806557 = 302459) (by norm_num)
theorem B806593 : Blo 714321 806593 := bbase (se 2 (by rfl) ⟨302472, by rfl⟩ : syracuseStep 806593 = 604945) (by norm_num)
theorem B2182853 : Blo 714321 2182853 := bbase (se 4 (by rfl) ⟨204642, by rfl⟩ : syracuseStep 2182853 = 409285) (by norm_num)
theorem B806629 : Blo 714321 806629 := bbase (se 4 (by rfl) ⟨75621, by rfl⟩ : syracuseStep 806629 = 151243) (by norm_num)
theorem B806665 : Blo 714321 806665 := bbase (se 2 (by rfl) ⟨302499, by rfl⟩ : syracuseStep 806665 = 604999) (by norm_num)
theorem B806701 : Blo 714321 806701 := bbase (se 3 (by rfl) ⟨151256, by rfl⟩ : syracuseStep 806701 = 302513) (by norm_num)
theorem B2412341 : Blo 714321 2412341 := bbase (se 5 (by rfl) ⟨113078, by rfl⟩ : syracuseStep 2412341 = 226157) (by norm_num)
theorem B905033 : Blo 714321 905033 := bbase (se 2 (by rfl) ⟨339387, by rfl⟩ : syracuseStep 905033 = 678775) (by norm_num)
theorem B806737 : Blo 714321 806737 := bbase (se 2 (by rfl) ⟨302526, by rfl⟩ : syracuseStep 806737 = 605053) (by norm_num)
theorem B2576245 : Blo 714321 2576245 := bbase (se 5 (by rfl) ⟨120761, by rfl⟩ : syracuseStep 2576245 = 241523) (by norm_num)
theorem B806773 : Blo 714321 806773 := bbase (se 5 (by rfl) ⟨37817, by rfl⟩ : syracuseStep 806773 = 75635) (by norm_num)
theorem B872317 : Blo 714321 872317 := bbase (se 3 (by rfl) ⟨163559, by rfl⟩ : syracuseStep 872317 = 327119) (by norm_num)
theorem B905089 : Blo 714321 905089 := bbase (se 2 (by rfl) ⟨339408, by rfl⟩ : syracuseStep 905089 = 678817) (by norm_num)
theorem B806809 : Blo 714321 806809 := bbase (se 2 (by rfl) ⟨302553, by rfl⟩ : syracuseStep 806809 = 605107) (by norm_num)
theorem B806845 : Blo 714321 806845 := bbase (se 3 (by rfl) ⟨151283, by rfl⟩ : syracuseStep 806845 = 302567) (by norm_num)
theorem B905185 : Blo 714321 905185 := bbase (se 2 (by rfl) ⟨339444, by rfl⟩ : syracuseStep 905185 = 678889) (by norm_num)
theorem B806881 : Blo 714321 806881 := bbase (se 2 (by rfl) ⟨302580, by rfl⟩ : syracuseStep 806881 = 605161) (by norm_num)
theorem B2576389 : Blo 714321 2576389 := bbase (se 4 (by rfl) ⟨241536, by rfl⟩ : syracuseStep 2576389 = 483073) (by norm_num)
theorem B806917 : Blo 714321 806917 := bbase (se 4 (by rfl) ⟨75648, by rfl⟩ : syracuseStep 806917 = 151297) (by norm_num)
theorem B774181 : Blo 714321 774181 := bbase (se 4 (by rfl) ⟨72579, by rfl⟩ : syracuseStep 774181 = 145159) (by norm_num)
theorem B806953 : Blo 714321 806953 := bbase (se 2 (by rfl) ⟨302607, by rfl⟩ : syracuseStep 806953 = 605215) (by norm_num)
theorem B806989 : Blo 714321 806989 := bbase (se 3 (by rfl) ⟨151310, by rfl⟩ : syracuseStep 806989 = 302621) (by norm_num)
theorem B9195605 : Blo 714321 9195605 := bbase (se 8 (by rfl) ⟨53880, by rfl⟩ : syracuseStep 9195605 = 107761) (by norm_num)
theorem B807025 : Blo 714321 807025 := bbase (se 2 (by rfl) ⟨302634, by rfl⟩ : syracuseStep 807025 = 605269) (by norm_num)
theorem B905357 : Blo 714321 905357 := bbase (se 3 (by rfl) ⟨169754, by rfl⟩ : syracuseStep 905357 = 339509) (by norm_num)
theorem B807061 : Blo 714321 807061 := bbase (se 6 (by rfl) ⟨18915, by rfl⟩ : syracuseStep 807061 = 37831) (by norm_num)
theorem B807097 : Blo 714321 807097 := bbase (se 2 (by rfl) ⟨302661, by rfl⟩ : syracuseStep 807097 = 605323) (by norm_num)
theorem B905413 : Blo 714321 905413 := bbase (se 4 (by rfl) ⟨84882, by rfl⟩ : syracuseStep 905413 = 169765) (by norm_num)
theorem B807133 : Blo 714321 807133 := bbase (se 3 (by rfl) ⟨151337, by rfl⟩ : syracuseStep 807133 = 302675) (by norm_num)
theorem B2412773 : Blo 714321 2412773 := bbase (se 4 (by rfl) ⟨226197, by rfl⟩ : syracuseStep 2412773 = 452395) (by norm_num)
theorem B807169 : Blo 714321 807169 := bbase (se 2 (by rfl) ⟨302688, by rfl⟩ : syracuseStep 807169 = 605377) (by norm_num)
theorem B905509 : Blo 714321 905509 := bbase (se 4 (by rfl) ⟨84891, by rfl⟩ : syracuseStep 905509 = 169783) (by norm_num)
theorem B807205 : Blo 714321 807205 := bbase (se 4 (by rfl) ⟨75675, by rfl⟩ : syracuseStep 807205 = 151351) (by norm_num)
theorem B807241 : Blo 714321 807241 := bbase (se 2 (by rfl) ⟨302715, by rfl⟩ : syracuseStep 807241 = 605431) (by norm_num)
theorem B807277 : Blo 714321 807277 := bbase (se 3 (by rfl) ⟨151364, by rfl⟩ : syracuseStep 807277 = 302729) (by norm_num)
theorem B3068293 : Blo 714321 3068293 := bbase (se 4 (by rfl) ⟨287652, by rfl⟩ : syracuseStep 3068293 = 575305) (by norm_num)
theorem B807313 : Blo 714321 807313 := bbase (se 2 (by rfl) ⟨302742, by rfl⟩ : syracuseStep 807313 = 605485) (by norm_num)
theorem B3625397 : Blo 714321 3625397 := bbase (se 5 (by rfl) ⟨169940, by rfl⟩ : syracuseStep 3625397 = 339881) (by norm_num)
theorem B807349 : Blo 714321 807349 := bbase (se 5 (by rfl) ⟨37844, by rfl⟩ : syracuseStep 807349 = 75689) (by norm_num)
theorem B905681 : Blo 714321 905681 := bbase (se 2 (by rfl) ⟨339630, by rfl⟩ : syracuseStep 905681 = 679261) (by norm_num)
theorem B807385 : Blo 714321 807385 := bbase (se 2 (by rfl) ⟨302769, by rfl⟩ : syracuseStep 807385 = 605539) (by norm_num)
theorem B807421 : Blo 714321 807421 := bbase (se 3 (by rfl) ⟨151391, by rfl⟩ : syracuseStep 807421 = 302783) (by norm_num)
theorem B905737 : Blo 714321 905737 := bbase (se 2 (by rfl) ⟨339651, by rfl⟩ : syracuseStep 905737 = 679303) (by norm_num)
theorem B807457 : Blo 714321 807457 := bbase (se 2 (by rfl) ⟨302796, by rfl⟩ : syracuseStep 807457 = 605593) (by norm_num)
theorem B807493 : Blo 714321 807493 := bbase (se 4 (by rfl) ⟨75702, by rfl⟩ : syracuseStep 807493 = 151405) (by norm_num)
theorem B16536149 : Blo 714321 16536149 := bbase (se 8 (by rfl) ⟨96891, by rfl⟩ : syracuseStep 16536149 = 193783) (by norm_num)
theorem B905833 : Blo 714321 905833 := bbase (se 2 (by rfl) ⟨339687, by rfl⟩ : syracuseStep 905833 = 679375) (by norm_num)
theorem B807529 : Blo 714321 807529 := bbase (se 2 (by rfl) ⟨302823, by rfl⟩ : syracuseStep 807529 = 605647) (by norm_num)
theorem B807565 : Blo 714321 807565 := bbase (se 3 (by rfl) ⟨151418, by rfl⟩ : syracuseStep 807565 = 302837) (by norm_num)
theorem B2413205 : Blo 714321 2413205 := bbase (se 6 (by rfl) ⟨56559, by rfl⟩ : syracuseStep 2413205 = 113119) (by norm_num)
theorem B807601 : Blo 714321 807601 := bbase (se 2 (by rfl) ⟨302850, by rfl⟩ : syracuseStep 807601 = 605701) (by norm_num)
theorem B807637 : Blo 714321 807637 := bbase (se 7 (by rfl) ⟨9464, by rfl⟩ : syracuseStep 807637 = 18929) (by norm_num)
theorem B807673 : Blo 714321 807673 := bbase (se 2 (by rfl) ⟨302877, by rfl⟩ : syracuseStep 807673 = 605755) (by norm_num)
theorem B906005 : Blo 714321 906005 := bbase (se 6 (by rfl) ⟨21234, by rfl⟩ : syracuseStep 906005 = 42469) (by norm_num)
theorem B807709 : Blo 714321 807709 := bbase (se 3 (by rfl) ⟨151445, by rfl⟩ : syracuseStep 807709 = 302891) (by norm_num)
theorem B807745 : Blo 714321 807745 := bbase (se 2 (by rfl) ⟨302904, by rfl⟩ : syracuseStep 807745 = 605809) (by norm_num)
theorem B1528645 : Blo 714321 1528645 := bbase (se 4 (by rfl) ⟨143310, by rfl⟩ : syracuseStep 1528645 = 286621) (by norm_num)
theorem B906061 : Blo 714321 906061 := bbase (se 3 (by rfl) ⟨169886, by rfl⟩ : syracuseStep 906061 = 339773) (by norm_num)
theorem B807781 : Blo 714321 807781 := bbase (se 4 (by rfl) ⟨75729, by rfl⟩ : syracuseStep 807781 = 151459) (by norm_num)
theorem B807817 : Blo 714321 807817 := bbase (se 2 (by rfl) ⟨302931, by rfl⟩ : syracuseStep 807817 = 605863) (by norm_num)
theorem B906157 : Blo 714321 906157 := bbase (se 3 (by rfl) ⟨169904, by rfl⟩ : syracuseStep 906157 = 339809) (by norm_num)
theorem B807853 : Blo 714321 807853 := bbase (se 3 (by rfl) ⟨151472, by rfl⟩ : syracuseStep 807853 = 302945) (by norm_num)
theorem B775117 : Blo 714321 775117 := bbase (se 3 (by rfl) ⟨145334, by rfl⟩ : syracuseStep 775117 = 290669) (by norm_num)
theorem B807889 : Blo 714321 807889 := bbase (se 2 (by rfl) ⟨302958, by rfl⟩ : syracuseStep 807889 = 605917) (by norm_num)
theorem B807925 : Blo 714321 807925 := bbase (se 5 (by rfl) ⟨37871, by rfl⟩ : syracuseStep 807925 = 75743) (by norm_num)
theorem B807961 : Blo 714321 807961 := bbase (se 2 (by rfl) ⟨302985, by rfl⟩ : syracuseStep 807961 = 605971) (by norm_num)
theorem B807997 : Blo 714321 807997 := bbase (se 3 (by rfl) ⟨151499, by rfl⟩ : syracuseStep 807997 = 302999) (by norm_num)
theorem B2413637 : Blo 714321 2413637 := bbase (se 4 (by rfl) ⟨226278, by rfl⟩ : syracuseStep 2413637 = 452557) (by norm_num)
theorem B906329 : Blo 714321 906329 := bbase (se 2 (by rfl) ⟨339873, by rfl⟩ : syracuseStep 906329 = 679747) (by norm_num)
theorem B808033 : Blo 714321 808033 := bbase (se 2 (by rfl) ⟨303012, by rfl⟩ : syracuseStep 808033 = 606025) (by norm_num)
theorem B808069 : Blo 714321 808069 := bbase (se 4 (by rfl) ⟨75756, by rfl⟩ : syracuseStep 808069 = 151513) (by norm_num)
theorem B906385 : Blo 714321 906385 := bbase (se 2 (by rfl) ⟨339894, by rfl⟩ : syracuseStep 906385 = 679789) (by norm_num)
theorem B808105 : Blo 714321 808105 := bbase (se 2 (by rfl) ⟨303039, by rfl⟩ : syracuseStep 808105 = 606079) (by norm_num)
theorem B906481 : Blo 714321 906481 := bbase (se 2 (by rfl) ⟨339930, by rfl⟩ : syracuseStep 906481 = 679861) (by norm_num)
theorem B2446613 : Blo 714321 2446613 := bbase (se 6 (by rfl) ⟨57342, by rfl⟩ : syracuseStep 2446613 = 114685) (by norm_num)
theorem B906653 : Blo 714321 906653 := bbase (se 3 (by rfl) ⟨169997, by rfl⟩ : syracuseStep 906653 = 339995) (by norm_num)
theorem B1725877 : Blo 714321 1725877 := bbase (se 5 (by rfl) ⟨80900, by rfl⟩ : syracuseStep 1725877 = 161801) (by norm_num)
theorem B906709 : Blo 714321 906709 := bbase (se 7 (by rfl) ⟨10625, by rfl⟩ : syracuseStep 906709 = 21251) (by norm_num)
theorem B2414069 : Blo 714321 2414069 := bbase (se 5 (by rfl) ⟨113159, by rfl⟩ : syracuseStep 2414069 = 226319) (by norm_num)
theorem B906805 : Blo 714321 906805 := bbase (se 5 (by rfl) ⟨42506, by rfl⟩ : syracuseStep 906805 = 85013) (by norm_num)
theorem B1529533 : Blo 714321 1529533 := bbase (se 3 (by rfl) ⟨286787, by rfl⟩ : syracuseStep 1529533 = 573575) (by norm_num)
theorem B3626693 : Blo 714321 3626693 := bbase (se 4 (by rfl) ⟨340002, by rfl⟩ : syracuseStep 3626693 = 680005) (by norm_num)
theorem B906977 : Blo 714321 906977 := bbase (se 2 (by rfl) ⟨340116, by rfl⟩ : syracuseStep 906977 = 680233) (by norm_num)
theorem B907033 : Blo 714321 907033 := bbase (se 2 (by rfl) ⟨340137, by rfl⟩ : syracuseStep 907033 = 680275) (by norm_num)
theorem B907129 : Blo 714321 907129 := bbase (se 2 (by rfl) ⟨340173, by rfl⟩ : syracuseStep 907129 = 680347) (by norm_num)
theorem B2414501 : Blo 714321 2414501 := bbase (se 4 (by rfl) ⟨226359, by rfl⟩ : syracuseStep 2414501 = 452719) (by norm_num)
theorem B907301 : Blo 714321 907301 := bbase (se 4 (by rfl) ⟨85059, by rfl⟩ : syracuseStep 907301 = 170119) (by norm_num)
theorem B907357 : Blo 714321 907357 := bbase (se 3 (by rfl) ⟨170129, by rfl⟩ : syracuseStep 907357 = 340259) (by norm_num)
theorem B4085909 : Blo 714321 4085909 := bbase (se 6 (by rfl) ⟨95763, by rfl⟩ : syracuseStep 4085909 = 191527) (by norm_num)
theorem B1530029 : Blo 714321 1530029 := bbase (se 3 (by rfl) ⟨286880, by rfl⟩ : syracuseStep 1530029 = 573761) (by norm_num)
theorem B907453 : Blo 714321 907453 := bbase (se 3 (by rfl) ⟨170147, by rfl⟩ : syracuseStep 907453 = 340295) (by norm_num)
theorem B2414933 : Blo 714321 2414933 := bbase (se 10 (by rfl) ⟨3537, by rfl⟩ : syracuseStep 2414933 = 7075) (by norm_num)
theorem B907625 : Blo 714321 907625 := bbase (se 2 (by rfl) ⟨340359, by rfl⟩ : syracuseStep 907625 = 680719) (by norm_num)
theorem B1071485 : Blo 714321 1071485 := bbase (se 3 (by rfl) ⟨200903, by rfl⟩ : syracuseStep 1071485 = 401807) (by norm_num)
theorem B1857925 : Blo 714321 1857925 := bbase (se 4 (by rfl) ⟨174180, by rfl⟩ : syracuseStep 1857925 = 348361) (by norm_num)
theorem B1071509 : Blo 714321 1071509 := bbase (se 6 (by rfl) ⟨25113, by rfl⟩ : syracuseStep 1071509 = 50227) (by norm_num)
theorem B907681 : Blo 714321 907681 := bbase (se 2 (by rfl) ⟨340380, by rfl⟩ : syracuseStep 907681 = 680761) (by norm_num)
theorem B1071533 : Blo 714321 1071533 := bbase (se 3 (by rfl) ⟨200912, by rfl⟩ : syracuseStep 1071533 = 401825) (by norm_num)
theorem B1071557 : Blo 714321 1071557 := bbase (se 4 (by rfl) ⟨100458, by rfl⟩ : syracuseStep 1071557 = 200917) (by norm_num)
theorem B1071581 : Blo 714321 1071581 := bbase (se 3 (by rfl) ⟨200921, by rfl⟩ : syracuseStep 1071581 = 401843) (by norm_num)
theorem B1071605 : Blo 714321 1071605 := bbase (se 5 (by rfl) ⟨50231, by rfl⟩ : syracuseStep 1071605 = 100463) (by norm_num)
theorem B907777 : Blo 714321 907777 := bbase (se 2 (by rfl) ⟨340416, by rfl⟩ : syracuseStep 907777 = 680833) (by norm_num)
theorem B1104389 : Blo 714321 1104389 := bbase (se 4 (by rfl) ⟨103536, by rfl⟩ : syracuseStep 1104389 = 207073) (by norm_num)
theorem B1071629 : Blo 714321 1071629 := bbase (se 3 (by rfl) ⟨200930, by rfl⟩ : syracuseStep 1071629 = 401861) (by norm_num)
theorem B1071653 : Blo 714321 1071653 := bbase (se 4 (by rfl) ⟨100467, by rfl⟩ : syracuseStep 1071653 = 200935) (by norm_num)
theorem B1071677 : Blo 714321 1071677 := bbase (se 3 (by rfl) ⟨200939, by rfl⟩ : syracuseStep 1071677 = 401879) (by norm_num)
theorem B2447941 : Blo 714321 2447941 := bbase (se 4 (by rfl) ⟨229494, by rfl⟩ : syracuseStep 2447941 = 458989) (by norm_num)
theorem B1071701 : Blo 714321 1071701 := bbase (se 8 (by rfl) ⟨6279, by rfl⟩ : syracuseStep 1071701 = 12559) (by norm_num)
theorem B1071725 : Blo 714321 1071725 := bbase (se 3 (by rfl) ⟨200948, by rfl⟩ : syracuseStep 1071725 = 401897) (by norm_num)
theorem B1071749 : Blo 714321 1071749 := bbase (se 4 (by rfl) ⟨100476, by rfl⟩ : syracuseStep 1071749 = 200953) (by norm_num)
theorem B1071773 : Blo 714321 1071773 := bbase (se 3 (by rfl) ⟨200957, by rfl⟩ : syracuseStep 1071773 = 401915) (by norm_num)
theorem B907949 : Blo 714321 907949 := bbase (se 3 (by rfl) ⟨170240, by rfl⟩ : syracuseStep 907949 = 340481) (by norm_num)
theorem B1071797 : Blo 714321 1071797 := bbase (se 5 (by rfl) ⟨50240, by rfl⟩ : syracuseStep 1071797 = 100481) (by norm_num)
theorem B1071821 : Blo 714321 1071821 := bbase (se 3 (by rfl) ⟨200966, by rfl⟩ : syracuseStep 1071821 = 401933) (by norm_num)
theorem B1071845 : Blo 714321 1071845 := bbase (se 4 (by rfl) ⟨100485, by rfl⟩ : syracuseStep 1071845 = 200971) (by norm_num)
theorem B908005 : Blo 714321 908005 := bbase (se 4 (by rfl) ⟨85125, by rfl⟩ : syracuseStep 908005 = 170251) (by norm_num)
theorem B1071869 : Blo 714321 1071869 := bbase (se 3 (by rfl) ⟨200975, by rfl⟩ : syracuseStep 1071869 = 401951) (by norm_num)
theorem B2415365 : Blo 714321 2415365 := bbase (se 4 (by rfl) ⟨226440, by rfl⟩ : syracuseStep 2415365 = 452881) (by norm_num)
theorem B1071893 : Blo 714321 1071893 := bbase (se 6 (by rfl) ⟨25122, by rfl⟩ : syracuseStep 1071893 = 50245) (by norm_num)
theorem B1071917 : Blo 714321 1071917 := bbase (se 3 (by rfl) ⟨200984, by rfl⟩ : syracuseStep 1071917 = 401969) (by norm_num)
theorem B1071941 : Blo 714321 1071941 := bbase (se 4 (by rfl) ⟨100494, by rfl⟩ : syracuseStep 1071941 = 200989) (by norm_num)
theorem B908101 : Blo 714321 908101 := bbase (se 4 (by rfl) ⟨85134, by rfl⟩ : syracuseStep 908101 = 170269) (by norm_num)
theorem B3103573 : Blo 714321 3103573 := bbase (se 9 (by rfl) ⟨9092, by rfl⟩ : syracuseStep 3103573 = 18185) (by norm_num)
theorem B1071965 : Blo 714321 1071965 := bbase (se 3 (by rfl) ⟨200993, by rfl⟩ : syracuseStep 1071965 = 401987) (by norm_num)
theorem B1071989 : Blo 714321 1071989 := bbase (se 5 (by rfl) ⟨50249, by rfl⟩ : syracuseStep 1071989 = 100499) (by norm_num)
theorem B1072013 : Blo 714321 1072013 := bbase (se 3 (by rfl) ⟨201002, by rfl⟩ : syracuseStep 1072013 = 402005) (by norm_num)
theorem B1072037 : Blo 714321 1072037 := bbase (se 4 (by rfl) ⟨100503, by rfl⟩ : syracuseStep 1072037 = 201007) (by norm_num)
theorem B5823413 : Blo 714321 5823413 := bbase (se 5 (by rfl) ⟨272972, by rfl⟩ : syracuseStep 5823413 = 545945) (by norm_num)
theorem B1072061 : Blo 714321 1072061 := bbase (se 3 (by rfl) ⟨201011, by rfl⟩ : syracuseStep 1072061 = 402023) (by norm_num)
theorem B1072085 : Blo 714321 1072085 := bbase (se 7 (by rfl) ⟨12563, by rfl⟩ : syracuseStep 1072085 = 25127) (by norm_num)
theorem B3627989 : Blo 714321 3627989 := bbase (se 7 (by rfl) ⟨42515, by rfl⟩ : syracuseStep 3627989 = 85031) (by norm_num)
theorem B1072109 : Blo 714321 1072109 := bbase (se 3 (by rfl) ⟨201020, by rfl⟩ : syracuseStep 1072109 = 402041) (by norm_num)
theorem B908273 : Blo 714321 908273 := bbase (se 2 (by rfl) ⟨340602, by rfl⟩ : syracuseStep 908273 = 681205) (by norm_num)
theorem B1072133 : Blo 714321 1072133 := bbase (se 4 (by rfl) ⟨100512, by rfl⟩ : syracuseStep 1072133 = 201025) (by norm_num)
theorem B1530893 : Blo 714321 1530893 := bbase (se 3 (by rfl) ⟨287042, by rfl⟩ : syracuseStep 1530893 = 574085) (by norm_num)
theorem B1072157 : Blo 714321 1072157 := bbase (se 3 (by rfl) ⟨201029, by rfl⟩ : syracuseStep 1072157 = 402059) (by norm_num)
theorem B908329 : Blo 714321 908329 := bbase (se 2 (by rfl) ⟨340623, by rfl⟩ : syracuseStep 908329 = 681247) (by norm_num)
theorem B1072181 : Blo 714321 1072181 := bbase (se 5 (by rfl) ⟨50258, by rfl⟩ : syracuseStep 1072181 = 100517) (by norm_num)
theorem B1072205 : Blo 714321 1072205 := bbase (se 3 (by rfl) ⟨201038, by rfl⟩ : syracuseStep 1072205 = 402077) (by norm_num)
theorem B1072229 : Blo 714321 1072229 := bbase (se 4 (by rfl) ⟨100521, by rfl⟩ : syracuseStep 1072229 = 201043) (by norm_num)
theorem B1072253 : Blo 714321 1072253 := bbase (se 3 (by rfl) ⟨201047, by rfl⟩ : syracuseStep 1072253 = 402095) (by norm_num)
theorem B908425 : Blo 714321 908425 := bbase (se 2 (by rfl) ⟨340659, by rfl⟩ : syracuseStep 908425 = 681319) (by norm_num)
theorem B1072277 : Blo 714321 1072277 := bbase (se 6 (by rfl) ⟨25131, by rfl⟩ : syracuseStep 1072277 = 50263) (by norm_num)
theorem B1531037 : Blo 714321 1531037 := bbase (se 3 (by rfl) ⟨287069, by rfl⟩ : syracuseStep 1531037 = 574139) (by norm_num)
theorem B1072301 : Blo 714321 1072301 := bbase (se 3 (by rfl) ⟨201056, by rfl⟩ : syracuseStep 1072301 = 402113) (by norm_num)
theorem B2415797 : Blo 714321 2415797 := bbase (se 5 (by rfl) ⟨113240, by rfl⟩ : syracuseStep 2415797 = 226481) (by norm_num)
theorem B1072325 : Blo 714321 1072325 := bbase (se 4 (by rfl) ⟨100530, by rfl⟩ : syracuseStep 1072325 = 201061) (by norm_num)
theorem B1072349 : Blo 714321 1072349 := bbase (se 3 (by rfl) ⟨201065, by rfl⟩ : syracuseStep 1072349 = 402131) (by norm_num)
theorem B1072373 : Blo 714321 1072373 := bbase (se 5 (by rfl) ⟨50267, by rfl⟩ : syracuseStep 1072373 = 100535) (by norm_num)
theorem B1072397 : Blo 714321 1072397 := bbase (se 3 (by rfl) ⟨201074, by rfl⟩ : syracuseStep 1072397 = 402149) (by norm_num)
theorem B1072421 : Blo 714321 1072421 := bbase (se 4 (by rfl) ⟨100539, by rfl⟩ : syracuseStep 1072421 = 201079) (by norm_num)
theorem B908597 : Blo 714321 908597 := bbase (se 5 (by rfl) ⟨42590, by rfl⟩ : syracuseStep 908597 = 85181) (by norm_num)
theorem B1072445 : Blo 714321 1072445 := bbase (se 3 (by rfl) ⟨201083, by rfl⟩ : syracuseStep 1072445 = 402167) (by norm_num)
theorem B1072469 : Blo 714321 1072469 := bbase (se 11 (by rfl) ⟨785, by rfl⟩ : syracuseStep 1072469 = 1571) (by norm_num)
theorem B1072493 : Blo 714321 1072493 := bbase (se 3 (by rfl) ⟨201092, by rfl⟩ : syracuseStep 1072493 = 402185) (by norm_num)
theorem B908653 : Blo 714321 908653 := bbase (se 3 (by rfl) ⟨170372, by rfl⟩ : syracuseStep 908653 = 340745) (by norm_num)
theorem B1072517 : Blo 714321 1072517 := bbase (se 4 (by rfl) ⟨100548, by rfl⟩ : syracuseStep 1072517 = 201097) (by norm_num)
theorem B3267989 : Blo 714321 3267989 := bbase (se 6 (by rfl) ⟨76593, by rfl⟩ : syracuseStep 3267989 = 153187) (by norm_num)
theorem B1072541 : Blo 714321 1072541 := bbase (se 3 (by rfl) ⟨201101, by rfl⟩ : syracuseStep 1072541 = 402203) (by norm_num)
theorem B1072565 : Blo 714321 1072565 := bbase (se 5 (by rfl) ⟨50276, by rfl⟩ : syracuseStep 1072565 = 100553) (by norm_num)
theorem B1072589 : Blo 714321 1072589 := bbase (se 3 (by rfl) ⟨201110, by rfl⟩ : syracuseStep 1072589 = 402221) (by norm_num)
theorem B908749 : Blo 714321 908749 := bbase (se 3 (by rfl) ⟨170390, by rfl⟩ : syracuseStep 908749 = 340781) (by norm_num)
theorem B1072613 : Blo 714321 1072613 := bbase (se 4 (by rfl) ⟨100557, by rfl⟩ : syracuseStep 1072613 = 201115) (by norm_num)
theorem B1072637 : Blo 714321 1072637 := bbase (se 3 (by rfl) ⟨201119, by rfl⟩ : syracuseStep 1072637 = 402239) (by norm_num)
theorem B1072661 : Blo 714321 1072661 := bbase (se 6 (by rfl) ⟨25140, by rfl⟩ : syracuseStep 1072661 = 50281) (by norm_num)
theorem B1072685 : Blo 714321 1072685 := bbase (se 3 (by rfl) ⟨201128, by rfl⟩ : syracuseStep 1072685 = 402257) (by norm_num)
theorem B1072709 : Blo 714321 1072709 := bbase (se 4 (by rfl) ⟨100566, by rfl⟩ : syracuseStep 1072709 = 201133) (by norm_num)
theorem B1072733 : Blo 714321 1072733 := bbase (se 3 (by rfl) ⟨201137, by rfl⟩ : syracuseStep 1072733 = 402275) (by norm_num)
theorem B2416229 : Blo 714321 2416229 := bbase (se 4 (by rfl) ⟨226521, by rfl⟩ : syracuseStep 2416229 = 453043) (by norm_num)
theorem B1072757 : Blo 714321 1072757 := bbase (se 5 (by rfl) ⟨50285, by rfl⟩ : syracuseStep 1072757 = 100571) (by norm_num)
theorem B908921 : Blo 714321 908921 := bbase (se 2 (by rfl) ⟨340845, by rfl⟩ : syracuseStep 908921 = 681691) (by norm_num)
theorem B1072781 : Blo 714321 1072781 := bbase (se 3 (by rfl) ⟨201146, by rfl⟩ : syracuseStep 1072781 = 402293) (by norm_num)
theorem B1072805 : Blo 714321 1072805 := bbase (se 4 (by rfl) ⟨100575, by rfl⟩ : syracuseStep 1072805 = 201151) (by norm_num)
theorem B908977 : Blo 714321 908977 := bbase (se 2 (by rfl) ⟨340866, by rfl⟩ : syracuseStep 908977 = 681733) (by norm_num)
theorem B1072829 : Blo 714321 1072829 := bbase (se 3 (by rfl) ⟨201155, by rfl⟩ : syracuseStep 1072829 = 402311) (by norm_num)
theorem B1892045 : Blo 714321 1892045 := bbase (se 3 (by rfl) ⟨354758, by rfl⟩ : syracuseStep 1892045 = 709517) (by norm_num)
theorem B1072853 : Blo 714321 1072853 := bbase (se 7 (by rfl) ⟨12572, by rfl⟩ : syracuseStep 1072853 = 25145) (by norm_num)
theorem B1072877 : Blo 714321 1072877 := bbase (se 3 (by rfl) ⟨201164, by rfl⟩ : syracuseStep 1072877 = 402329) (by norm_num)
theorem B1072901 : Blo 714321 1072901 := bbase (se 4 (by rfl) ⟨100584, by rfl⟩ : syracuseStep 1072901 = 201169) (by norm_num)
theorem B909073 : Blo 714321 909073 := bbase (se 2 (by rfl) ⟨340902, by rfl⟩ : syracuseStep 909073 = 681805) (by norm_num)
theorem B1072925 : Blo 714321 1072925 := bbase (se 3 (by rfl) ⟨201173, by rfl⟩ : syracuseStep 1072925 = 402347) (by norm_num)
theorem B1072949 : Blo 714321 1072949 := bbase (se 5 (by rfl) ⟨50294, by rfl⟩ : syracuseStep 1072949 = 100589) (by norm_num)
theorem B1072973 : Blo 714321 1072973 := bbase (se 3 (by rfl) ⟨201182, by rfl⟩ : syracuseStep 1072973 = 402365) (by norm_num)
theorem B88137557 : Blo 714321 88137557 := bbase (se 9 (by rfl) ⟨258215, by rfl⟩ : syracuseStep 88137557 = 516431) (by norm_num)
theorem B1072997 : Blo 714321 1072997 := bbase (se 4 (by rfl) ⟨100593, by rfl⟩ : syracuseStep 1072997 = 201187) (by norm_num)
theorem B1073021 : Blo 714321 1073021 := bbase (se 3 (by rfl) ⟨201191, by rfl⟩ : syracuseStep 1073021 = 402383) (by norm_num)
theorem B1531781 : Blo 714321 1531781 := bbase (se 4 (by rfl) ⟨143604, by rfl⟩ : syracuseStep 1531781 = 287209) (by norm_num)
theorem B1073045 : Blo 714321 1073045 := bbase (se 6 (by rfl) ⟨25149, by rfl⟩ : syracuseStep 1073045 = 50299) (by norm_num)
theorem B7364501 : Blo 714321 7364501 := bbase (se 6 (by rfl) ⟨172605, by rfl⟩ : syracuseStep 7364501 = 345211) (by norm_num)
theorem B1073069 : Blo 714321 1073069 := bbase (se 3 (by rfl) ⟨201200, by rfl⟩ : syracuseStep 1073069 = 402401) (by norm_num)
theorem B1630133 : Blo 714321 1630133 := bbase (se 5 (by rfl) ⟨76412, by rfl⟩ : syracuseStep 1630133 = 152825) (by norm_num)
theorem B1073093 : Blo 714321 1073093 := bbase (se 4 (by rfl) ⟨100602, by rfl⟩ : syracuseStep 1073093 = 201205) (by norm_num)
theorem B1073117 : Blo 714321 1073117 := bbase (se 3 (by rfl) ⟨201209, by rfl⟩ : syracuseStep 1073117 = 402419) (by norm_num)
theorem B1073141 : Blo 714321 1073141 := bbase (se 5 (by rfl) ⟨50303, by rfl⟩ : syracuseStep 1073141 = 100607) (by norm_num)
theorem B1073165 : Blo 714321 1073165 := bbase (se 3 (by rfl) ⟨201218, by rfl⟩ : syracuseStep 1073165 = 402437) (by norm_num)
theorem B2416661 : Blo 714321 2416661 := bbase (se 6 (by rfl) ⟨56640, by rfl⟩ : syracuseStep 2416661 = 113281) (by norm_num)
theorem B1073189 : Blo 714321 1073189 := bbase (se 4 (by rfl) ⟨100611, by rfl⟩ : syracuseStep 1073189 = 201223) (by norm_num)
theorem B1073213 : Blo 714321 1073213 := bbase (se 3 (by rfl) ⟨201227, by rfl⟩ : syracuseStep 1073213 = 402455) (by norm_num)
theorem B1073237 : Blo 714321 1073237 := bbase (se 8 (by rfl) ⟨6288, by rfl⟩ : syracuseStep 1073237 = 12577) (by norm_num)
theorem B1073261 : Blo 714321 1073261 := bbase (se 3 (by rfl) ⟨201236, by rfl⟩ : syracuseStep 1073261 = 402473) (by norm_num)
theorem B1073285 : Blo 714321 1073285 := bbase (se 4 (by rfl) ⟨100620, by rfl⟩ : syracuseStep 1073285 = 201241) (by norm_num)
theorem B1073309 : Blo 714321 1073309 := bbase (se 3 (by rfl) ⟨201245, by rfl⟩ : syracuseStep 1073309 = 402491) (by norm_num)
theorem B1073333 : Blo 714321 1073333 := bbase (se 5 (by rfl) ⟨50312, by rfl⟩ : syracuseStep 1073333 = 100625) (by norm_num)
theorem B1073357 : Blo 714321 1073357 := bbase (se 3 (by rfl) ⟨201254, by rfl⟩ : syracuseStep 1073357 = 402509) (by norm_num)
theorem B1073381 : Blo 714321 1073381 := bbase (se 4 (by rfl) ⟨100629, by rfl⟩ : syracuseStep 1073381 = 201259) (by norm_num)
theorem B3629285 : Blo 714321 3629285 := bbase (se 4 (by rfl) ⟨340245, by rfl⟩ : syracuseStep 3629285 = 680491) (by norm_num)
theorem B1073405 : Blo 714321 1073405 := bbase (se 3 (by rfl) ⟨201263, by rfl⟩ : syracuseStep 1073405 = 402527) (by norm_num)
theorem B3432725 : Blo 714321 3432725 := bbase (se 6 (by rfl) ⟨80454, by rfl⟩ : syracuseStep 3432725 = 160909) (by norm_num)
theorem B1073429 : Blo 714321 1073429 := bbase (se 6 (by rfl) ⟨25158, by rfl⟩ : syracuseStep 1073429 = 50317) (by norm_num)
theorem B1073453 : Blo 714321 1073453 := bbase (se 3 (by rfl) ⟨201272, by rfl⟩ : syracuseStep 1073453 = 402545) (by norm_num)
theorem B1073477 : Blo 714321 1073477 := bbase (se 4 (by rfl) ⟨100638, by rfl⟩ : syracuseStep 1073477 = 201277) (by norm_num)
theorem B1073501 : Blo 714321 1073501 := bbase (se 3 (by rfl) ⟨201281, by rfl⟩ : syracuseStep 1073501 = 402563) (by norm_num)
theorem B1073525 : Blo 714321 1073525 := bbase (se 5 (by rfl) ⟨50321, by rfl⟩ : syracuseStep 1073525 = 100643) (by norm_num)
theorem B1073549 : Blo 714321 1073549 := bbase (se 3 (by rfl) ⟨201290, by rfl⟩ : syracuseStep 1073549 = 402581) (by norm_num)
theorem B1073573 : Blo 714321 1073573 := bbase (se 4 (by rfl) ⟨100647, by rfl⟩ : syracuseStep 1073573 = 201295) (by norm_num)
theorem B1073597 : Blo 714321 1073597 := bbase (se 3 (by rfl) ⟨201299, by rfl⟩ : syracuseStep 1073597 = 402599) (by norm_num)
theorem B2417093 : Blo 714321 2417093 := bbase (se 4 (by rfl) ⟨226602, by rfl⟩ : syracuseStep 2417093 = 453205) (by norm_num)
theorem B1073621 : Blo 714321 1073621 := bbase (se 7 (by rfl) ⟨12581, by rfl⟩ : syracuseStep 1073621 = 25163) (by norm_num)
theorem B1073645 : Blo 714321 1073645 := bbase (se 3 (by rfl) ⟨201308, by rfl⟩ : syracuseStep 1073645 = 402617) (by norm_num)
theorem B1073669 : Blo 714321 1073669 := bbase (se 4 (by rfl) ⟨100656, by rfl⟩ : syracuseStep 1073669 = 201313) (by norm_num)
theorem B1073693 : Blo 714321 1073693 := bbase (se 3 (by rfl) ⟨201317, by rfl⟩ : syracuseStep 1073693 = 402635) (by norm_num)
theorem B1073717 : Blo 714321 1073717 := bbase (se 5 (by rfl) ⟨50330, by rfl⟩ : syracuseStep 1073717 = 100661) (by norm_num)
theorem B3269173 : Blo 714321 3269173 := bbase (se 5 (by rfl) ⟨153242, by rfl⟩ : syracuseStep 3269173 = 306485) (by norm_num)
theorem B1073741 : Blo 714321 1073741 := bbase (se 3 (by rfl) ⟨201326, by rfl⟩ : syracuseStep 1073741 = 402653) (by norm_num)
theorem B1073765 : Blo 714321 1073765 := bbase (se 4 (by rfl) ⟨100665, by rfl⟩ : syracuseStep 1073765 = 201331) (by norm_num)
theorem B1532533 : Blo 714321 1532533 := bbase (se 5 (by rfl) ⟨71837, by rfl⟩ : syracuseStep 1532533 = 143675) (by norm_num)
theorem B1073789 : Blo 714321 1073789 := bbase (se 3 (by rfl) ⟨201335, by rfl⟩ : syracuseStep 1073789 = 402671) (by norm_num)
theorem B1073813 : Blo 714321 1073813 := bbase (se 6 (by rfl) ⟨25167, by rfl⟩ : syracuseStep 1073813 = 50335) (by norm_num)
theorem B1073837 : Blo 714321 1073837 := bbase (se 3 (by rfl) ⟨201344, by rfl⟩ : syracuseStep 1073837 = 402689) (by norm_num)
theorem B1073861 : Blo 714321 1073861 := bbase (se 4 (by rfl) ⟨100674, by rfl⟩ : syracuseStep 1073861 = 201349) (by norm_num)
theorem B5432021 : Blo 714321 5432021 := bbase (se 7 (by rfl) ⟨63656, by rfl⟩ : syracuseStep 5432021 = 127313) (by norm_num)
theorem B1073885 : Blo 714321 1073885 := bbase (se 3 (by rfl) ⟨201353, by rfl⟩ : syracuseStep 1073885 = 402707) (by norm_num)
theorem B1073909 : Blo 714321 1073909 := bbase (se 5 (by rfl) ⟨50339, by rfl⟩ : syracuseStep 1073909 = 100679) (by norm_num)
theorem B1532677 : Blo 714321 1532677 := bbase (se 4 (by rfl) ⟨143688, by rfl⟩ : syracuseStep 1532677 = 287377) (by norm_num)
theorem B1073933 : Blo 714321 1073933 := bbase (se 3 (by rfl) ⟨201362, by rfl⟩ : syracuseStep 1073933 = 402725) (by norm_num)
theorem B3498773 : Blo 714321 3498773 := bbase (se 6 (by rfl) ⟨82002, by rfl⟩ : syracuseStep 3498773 = 164005) (by norm_num)
theorem B1073957 : Blo 714321 1073957 := bbase (se 4 (by rfl) ⟨100683, by rfl⟩ : syracuseStep 1073957 = 201367) (by norm_num)
theorem B1073981 : Blo 714321 1073981 := bbase (se 3 (by rfl) ⟨201371, by rfl⟩ : syracuseStep 1073981 = 402743) (by norm_num)
theorem B1074005 : Blo 714321 1074005 := bbase (se 9 (by rfl) ⟨3146, by rfl⟩ : syracuseStep 1074005 = 6293) (by norm_num)
theorem B19653461 : Blo 714321 19653461 := bbase (se 9 (by rfl) ⟨57578, by rfl⟩ : syracuseStep 19653461 = 115157) (by norm_num)
theorem B2909029 : Blo 714321 2909029 := bbase (se 4 (by rfl) ⟨272721, by rfl⟩ : syracuseStep 2909029 = 545443) (by norm_num)
theorem B1074029 : Blo 714321 1074029 := bbase (se 3 (by rfl) ⟨201380, by rfl⟩ : syracuseStep 1074029 = 402761) (by norm_num)
theorem B2417525 : Blo 714321 2417525 := bbase (se 5 (by rfl) ⟨113321, by rfl⟩ : syracuseStep 2417525 = 226643) (by norm_num)
theorem B1074053 : Blo 714321 1074053 := bbase (se 4 (by rfl) ⟨100692, by rfl⟩ : syracuseStep 1074053 = 201385) (by norm_num)
theorem B1074077 : Blo 714321 1074077 := bbase (se 3 (by rfl) ⟨201389, by rfl⟩ : syracuseStep 1074077 = 402779) (by norm_num)
theorem B1074101 : Blo 714321 1074101 := bbase (se 5 (by rfl) ⟨50348, by rfl⟩ : syracuseStep 1074101 = 100697) (by norm_num)
theorem B1074125 : Blo 714321 1074125 := bbase (se 3 (by rfl) ⟨201398, by rfl⟩ : syracuseStep 1074125 = 402797) (by norm_num)
theorem B1074149 : Blo 714321 1074149 := bbase (se 4 (by rfl) ⟨100701, by rfl⟩ : syracuseStep 1074149 = 201403) (by norm_num)
theorem B1074173 : Blo 714321 1074173 := bbase (se 3 (by rfl) ⟨201407, by rfl⟩ : syracuseStep 1074173 = 402815) (by norm_num)
theorem B1074197 : Blo 714321 1074197 := bbase (se 6 (by rfl) ⟨25176, by rfl⟩ : syracuseStep 1074197 = 50353) (by norm_num)
theorem B1074221 : Blo 714321 1074221 := bbase (se 3 (by rfl) ⟨201416, by rfl⟩ : syracuseStep 1074221 = 402833) (by norm_num)
theorem B1074245 : Blo 714321 1074245 := bbase (se 4 (by rfl) ⟨100710, by rfl⟩ : syracuseStep 1074245 = 201421) (by norm_num)
theorem B943193 : Blo 714321 943193 := bbase (se 2 (by rfl) ⟨353697, by rfl⟩ : syracuseStep 943193 = 707395) (by norm_num)
theorem B1074269 : Blo 714321 1074269 := bbase (se 3 (by rfl) ⟨201425, by rfl⟩ : syracuseStep 1074269 = 402851) (by norm_num)
theorem B1074293 : Blo 714321 1074293 := bbase (se 5 (by rfl) ⟨50357, by rfl⟩ : syracuseStep 1074293 = 100715) (by norm_num)
theorem B1533053 : Blo 714321 1533053 := bbase (se 3 (by rfl) ⟨287447, by rfl⟩ : syracuseStep 1533053 = 574895) (by norm_num)
theorem B1074317 : Blo 714321 1074317 := bbase (se 3 (by rfl) ⟨201434, by rfl⟩ : syracuseStep 1074317 = 402869) (by norm_num)
theorem B1074341 : Blo 714321 1074341 := bbase (se 4 (by rfl) ⟨100719, by rfl⟩ : syracuseStep 1074341 = 201439) (by norm_num)
theorem B1074365 : Blo 714321 1074365 := bbase (se 3 (by rfl) ⟨201443, by rfl⟩ : syracuseStep 1074365 = 402887) (by norm_num)
theorem B1074389 : Blo 714321 1074389 := bbase (se 7 (by rfl) ⟨12590, by rfl⟩ : syracuseStep 1074389 = 25181) (by norm_num)
theorem B1074413 : Blo 714321 1074413 := bbase (se 3 (by rfl) ⟨201452, by rfl⟩ : syracuseStep 1074413 = 402905) (by norm_num)
theorem B1205509 : Blo 714321 1205509 := bbase (se 4 (by rfl) ⟨113016, by rfl⟩ : syracuseStep 1205509 = 226033) (by norm_num)
theorem B1074437 : Blo 714321 1074437 := bbase (se 4 (by rfl) ⟨100728, by rfl⟩ : syracuseStep 1074437 = 201457) (by norm_num)
theorem B1074461 : Blo 714321 1074461 := bbase (se 3 (by rfl) ⟨201461, by rfl⟩ : syracuseStep 1074461 = 402923) (by norm_num)
theorem B2417957 : Blo 714321 2417957 := bbase (se 4 (by rfl) ⟨226683, by rfl⟩ : syracuseStep 2417957 = 453367) (by norm_num)
theorem B1074485 : Blo 714321 1074485 := bbase (se 5 (by rfl) ⟨50366, by rfl⟩ : syracuseStep 1074485 = 100733) (by norm_num)
theorem B1074509 : Blo 714321 1074509 := bbase (se 3 (by rfl) ⟨201470, by rfl⟩ : syracuseStep 1074509 = 402941) (by norm_num)
theorem B1205597 : Blo 714321 1205597 := bbase (se 3 (by rfl) ⟨226049, by rfl⟩ : syracuseStep 1205597 = 452099) (by norm_num)
theorem B1074533 : Blo 714321 1074533 := bbase (se 4 (by rfl) ⟨100737, by rfl⟩ : syracuseStep 1074533 = 201475) (by norm_num)
theorem B1074557 : Blo 714321 1074557 := bbase (se 3 (by rfl) ⟨201479, by rfl⟩ : syracuseStep 1074557 = 402959) (by norm_num)
theorem B1074581 : Blo 714321 1074581 := bbase (se 6 (by rfl) ⟨25185, by rfl⟩ : syracuseStep 1074581 = 50371) (by norm_num)
theorem B1074605 : Blo 714321 1074605 := bbase (se 3 (by rfl) ⟨201488, by rfl⟩ : syracuseStep 1074605 = 402977) (by norm_num)
theorem B1074629 : Blo 714321 1074629 := bbase (se 4 (by rfl) ⟨100746, by rfl⟩ : syracuseStep 1074629 = 201493) (by norm_num)
theorem B1205725 : Blo 714321 1205725 := bbase (se 3 (by rfl) ⟨226073, by rfl⟩ : syracuseStep 1205725 = 452147) (by norm_num)
theorem B1074653 : Blo 714321 1074653 := bbase (se 3 (by rfl) ⟨201497, by rfl⟩ : syracuseStep 1074653 = 402995) (by norm_num)
theorem B1533421 : Blo 714321 1533421 := bbase (se 3 (by rfl) ⟨287516, by rfl⟩ : syracuseStep 1533421 = 575033) (by norm_num)
theorem B1074677 : Blo 714321 1074677 := bbase (se 5 (by rfl) ⟨50375, by rfl⟩ : syracuseStep 1074677 = 100751) (by norm_num)
theorem B3630581 : Blo 714321 3630581 := bbase (se 5 (by rfl) ⟨170183, by rfl⟩ : syracuseStep 3630581 = 340367) (by norm_num)
theorem B1467917 : Blo 714321 1467917 := bbase (se 3 (by rfl) ⟨275234, by rfl⟩ : syracuseStep 1467917 = 550469) (by norm_num)
theorem B1074701 : Blo 714321 1074701 := bbase (se 3 (by rfl) ⟨201506, by rfl⟩ : syracuseStep 1074701 = 403013) (by norm_num)
theorem B1074725 : Blo 714321 1074725 := bbase (se 4 (by rfl) ⟨100755, by rfl⟩ : syracuseStep 1074725 = 201511) (by norm_num)
theorem B1205813 : Blo 714321 1205813 := bbase (se 5 (by rfl) ⟨56522, by rfl⟩ : syracuseStep 1205813 = 113045) (by norm_num)
theorem B1074749 : Blo 714321 1074749 := bbase (se 3 (by rfl) ⟨201515, by rfl⟩ : syracuseStep 1074749 = 403031) (by norm_num)
theorem B3434069 : Blo 714321 3434069 := bbase (se 8 (by rfl) ⟨20121, by rfl⟩ : syracuseStep 3434069 = 40243) (by norm_num)
theorem B1074773 : Blo 714321 1074773 := bbase (se 8 (by rfl) ⟨6297, by rfl⟩ : syracuseStep 1074773 = 12595) (by norm_num)
theorem B1074797 : Blo 714321 1074797 := bbase (se 3 (by rfl) ⟨201524, by rfl⟩ : syracuseStep 1074797 = 403049) (by norm_num)
theorem B1074821 : Blo 714321 1074821 := bbase (se 4 (by rfl) ⟨100764, by rfl⟩ : syracuseStep 1074821 = 201529) (by norm_num)
theorem B1074845 : Blo 714321 1074845 := bbase (se 3 (by rfl) ⟨201533, by rfl⟩ : syracuseStep 1074845 = 403067) (by norm_num)
theorem B1205941 : Blo 714321 1205941 := bbase (se 5 (by rfl) ⟨56528, by rfl⟩ : syracuseStep 1205941 = 113057) (by norm_num)
theorem B1074869 : Blo 714321 1074869 := bbase (se 5 (by rfl) ⟨50384, by rfl⟩ : syracuseStep 1074869 = 100769) (by norm_num)
theorem B1074893 : Blo 714321 1074893 := bbase (se 3 (by rfl) ⟨201542, by rfl⟩ : syracuseStep 1074893 = 403085) (by norm_num)
theorem B2418389 : Blo 714321 2418389 := bbase (se 7 (by rfl) ⟨28340, by rfl⟩ : syracuseStep 2418389 = 56681) (by norm_num)
theorem B1074917 : Blo 714321 1074917 := bbase (se 4 (by rfl) ⟨100773, by rfl⟩ : syracuseStep 1074917 = 201547) (by norm_num)
theorem B1074941 : Blo 714321 1074941 := bbase (se 3 (by rfl) ⟨201551, by rfl⟩ : syracuseStep 1074941 = 403103) (by norm_num)
theorem B1206029 : Blo 714321 1206029 := bbase (se 3 (by rfl) ⟨226130, by rfl⟩ : syracuseStep 1206029 = 452261) (by norm_num)
theorem B1074965 : Blo 714321 1074965 := bbase (se 6 (by rfl) ⟨25194, by rfl⟩ : syracuseStep 1074965 = 50389) (by norm_num)
theorem B1074989 : Blo 714321 1074989 := bbase (se 3 (by rfl) ⟨201560, by rfl⟩ : syracuseStep 1074989 = 403121) (by norm_num)
theorem B1075013 : Blo 714321 1075013 := bbase (se 4 (by rfl) ⟨100782, by rfl⟩ : syracuseStep 1075013 = 201565) (by norm_num)
theorem B1075037 : Blo 714321 1075037 := bbase (se 3 (by rfl) ⟨201569, by rfl⟩ : syracuseStep 1075037 = 403139) (by norm_num)
theorem B2713445 : Blo 714321 2713445 := bbase (se 4 (by rfl) ⟨254385, by rfl⟩ : syracuseStep 2713445 = 508771) (by norm_num)
theorem B1075061 : Blo 714321 1075061 := bbase (se 5 (by rfl) ⟨50393, by rfl⟩ : syracuseStep 1075061 = 100787) (by norm_num)
theorem B1206157 : Blo 714321 1206157 := bbase (se 3 (by rfl) ⟨226154, by rfl⟩ : syracuseStep 1206157 = 452309) (by norm_num)
theorem B1075085 : Blo 714321 1075085 := bbase (se 3 (by rfl) ⟨201578, by rfl⟩ : syracuseStep 1075085 = 403157) (by norm_num)
theorem B1075109 : Blo 714321 1075109 := bbase (se 4 (by rfl) ⟨100791, by rfl⟩ : syracuseStep 1075109 = 201583) (by norm_num)
theorem B1075133 : Blo 714321 1075133 := bbase (se 3 (by rfl) ⟨201587, by rfl⟩ : syracuseStep 1075133 = 403175) (by norm_num)
theorem B1075157 : Blo 714321 1075157 := bbase (se 7 (by rfl) ⟨12599, by rfl⟩ : syracuseStep 1075157 = 25199) (by norm_num)
theorem B1206245 : Blo 714321 1206245 := bbase (se 4 (by rfl) ⟨113085, by rfl⟩ : syracuseStep 1206245 = 226171) (by norm_num)
theorem B1075181 : Blo 714321 1075181 := bbase (se 3 (by rfl) ⟨201596, by rfl⟩ : syracuseStep 1075181 = 403193) (by norm_num)
theorem B1075205 : Blo 714321 1075205 := bbase (se 4 (by rfl) ⟨100800, by rfl⟩ : syracuseStep 1075205 = 201601) (by norm_num)
theorem B1075229 : Blo 714321 1075229 := bbase (se 3 (by rfl) ⟨201605, by rfl⟩ : syracuseStep 1075229 = 403211) (by norm_num)
theorem B1075253 : Blo 714321 1075253 := bbase (se 5 (by rfl) ⟨50402, by rfl⟩ : syracuseStep 1075253 = 100805) (by norm_num)
theorem B1075277 : Blo 714321 1075277 := bbase (se 3 (by rfl) ⟨201614, by rfl⟩ : syracuseStep 1075277 = 403229) (by norm_num)
theorem B1206373 : Blo 714321 1206373 := bbase (se 4 (by rfl) ⟨113097, by rfl⟩ : syracuseStep 1206373 = 226195) (by norm_num)
theorem B1075301 : Blo 714321 1075301 := bbase (se 4 (by rfl) ⟨100809, by rfl⟩ : syracuseStep 1075301 = 201619) (by norm_num)
theorem B1075325 : Blo 714321 1075325 := bbase (se 3 (by rfl) ⟨201623, by rfl⟩ : syracuseStep 1075325 = 403247) (by norm_num)
theorem B2713733 : Blo 714321 2713733 := bbase (se 4 (by rfl) ⟨254412, by rfl⟩ : syracuseStep 2713733 = 508825) (by norm_num)
theorem B2418821 : Blo 714321 2418821 := bbase (se 4 (by rfl) ⟨226764, by rfl⟩ : syracuseStep 2418821 = 453529) (by norm_num)
theorem B1075349 : Blo 714321 1075349 := bbase (se 6 (by rfl) ⟨25203, by rfl⟩ : syracuseStep 1075349 = 50407) (by norm_num)
theorem B1075373 : Blo 714321 1075373 := bbase (se 3 (by rfl) ⟨201632, by rfl⟩ : syracuseStep 1075373 = 403265) (by norm_num)
theorem B1206461 : Blo 714321 1206461 := bbase (se 3 (by rfl) ⟨226211, by rfl⟩ : syracuseStep 1206461 = 452423) (by norm_num)
theorem B1075397 : Blo 714321 1075397 := bbase (se 4 (by rfl) ⟨100818, by rfl⟩ : syracuseStep 1075397 = 201637) (by norm_num)
theorem B1075421 : Blo 714321 1075421 := bbase (se 3 (by rfl) ⟨201641, by rfl⟩ : syracuseStep 1075421 = 403283) (by norm_num)
theorem B1075445 : Blo 714321 1075445 := bbase (se 5 (by rfl) ⟨50411, by rfl⟩ : syracuseStep 1075445 = 100823) (by norm_num)
theorem B1075469 : Blo 714321 1075469 := bbase (se 3 (by rfl) ⟨201650, by rfl⟩ : syracuseStep 1075469 = 403301) (by norm_num)
theorem B1075493 : Blo 714321 1075493 := bbase (se 4 (by rfl) ⟨100827, by rfl⟩ : syracuseStep 1075493 = 201655) (by norm_num)
theorem B1206589 : Blo 714321 1206589 := bbase (se 3 (by rfl) ⟨226235, by rfl⟩ : syracuseStep 1206589 = 452471) (by norm_num)
theorem B1075517 : Blo 714321 1075517 := bbase (se 3 (by rfl) ⟨201659, by rfl⟩ : syracuseStep 1075517 = 403319) (by norm_num)
theorem B1075541 : Blo 714321 1075541 := bbase (se 10 (by rfl) ⟨1575, by rfl⟩ : syracuseStep 1075541 = 3151) (by norm_num)
theorem B1075565 : Blo 714321 1075565 := bbase (se 3 (by rfl) ⟨201668, by rfl⟩ : syracuseStep 1075565 = 403337) (by norm_num)
theorem B1075589 : Blo 714321 1075589 := bbase (se 4 (by rfl) ⟨100836, by rfl⟩ : syracuseStep 1075589 = 201673) (by norm_num)
theorem B1206677 : Blo 714321 1206677 := bbase (se 6 (by rfl) ⟨28281, by rfl⟩ : syracuseStep 1206677 = 56563) (by norm_num)
theorem B1075613 : Blo 714321 1075613 := bbase (se 3 (by rfl) ⟨201677, by rfl⟩ : syracuseStep 1075613 = 403355) (by norm_num)
theorem B1075637 : Blo 714321 1075637 := bbase (se 5 (by rfl) ⟨50420, by rfl⟩ : syracuseStep 1075637 = 100841) (by norm_num)
theorem B1075661 : Blo 714321 1075661 := bbase (se 3 (by rfl) ⟨201686, by rfl⟩ : syracuseStep 1075661 = 403373) (by norm_num)
theorem B1075685 : Blo 714321 1075685 := bbase (se 4 (by rfl) ⟨100845, by rfl⟩ : syracuseStep 1075685 = 201691) (by norm_num)
theorem B1075709 : Blo 714321 1075709 := bbase (se 3 (by rfl) ⟨201695, by rfl⟩ : syracuseStep 1075709 = 403391) (by norm_num)
theorem B1206805 : Blo 714321 1206805 := bbase (se 6 (by rfl) ⟨28284, by rfl⟩ : syracuseStep 1206805 = 56569) (by norm_num)
theorem B1075733 : Blo 714321 1075733 := bbase (se 6 (by rfl) ⟨25212, by rfl⟩ : syracuseStep 1075733 = 50425) (by norm_num)
theorem B1075757 : Blo 714321 1075757 := bbase (se 3 (by rfl) ⟨201704, by rfl⟩ : syracuseStep 1075757 = 403409) (by norm_num)
theorem B2419253 : Blo 714321 2419253 := bbase (se 5 (by rfl) ⟨113402, by rfl⟩ : syracuseStep 2419253 = 226805) (by norm_num)
theorem B1075781 : Blo 714321 1075781 := bbase (se 4 (by rfl) ⟨100854, by rfl⟩ : syracuseStep 1075781 = 201709) (by norm_num)
theorem B1075805 : Blo 714321 1075805 := bbase (se 3 (by rfl) ⟨201713, by rfl⟩ : syracuseStep 1075805 = 403427) (by norm_num)
theorem B1206893 : Blo 714321 1206893 := bbase (se 3 (by rfl) ⟨226292, by rfl⟩ : syracuseStep 1206893 = 452585) (by norm_num)
theorem B1075829 : Blo 714321 1075829 := bbase (se 5 (by rfl) ⟨50429, by rfl⟩ : syracuseStep 1075829 = 100859) (by norm_num)
theorem B1075853 : Blo 714321 1075853 := bbase (se 3 (by rfl) ⟨201722, by rfl⟩ : syracuseStep 1075853 = 403445) (by norm_num)
theorem B1075877 : Blo 714321 1075877 := bbase (se 4 (by rfl) ⟨100863, by rfl⟩ : syracuseStep 1075877 = 201727) (by norm_num)
theorem B1075901 : Blo 714321 1075901 := bbase (se 3 (by rfl) ⟨201731, by rfl⟩ : syracuseStep 1075901 = 403463) (by norm_num)
theorem B1075925 : Blo 714321 1075925 := bbase (se 7 (by rfl) ⟨12608, by rfl⟩ : syracuseStep 1075925 = 25217) (by norm_num)
theorem B1207021 : Blo 714321 1207021 := bbase (se 3 (by rfl) ⟨226316, by rfl⟩ : syracuseStep 1207021 = 452633) (by norm_num)
theorem B1075949 : Blo 714321 1075949 := bbase (se 3 (by rfl) ⟨201740, by rfl⟩ : syracuseStep 1075949 = 403481) (by norm_num)
theorem B1075973 : Blo 714321 1075973 := bbase (se 4 (by rfl) ⟨100872, by rfl⟩ : syracuseStep 1075973 = 201745) (by norm_num)
theorem B3631877 : Blo 714321 3631877 := bbase (se 4 (by rfl) ⟨340488, by rfl⟩ : syracuseStep 3631877 = 680977) (by norm_num)
theorem B1075997 : Blo 714321 1075997 := bbase (se 3 (by rfl) ⟨201749, by rfl⟩ : syracuseStep 1075997 = 403499) (by norm_num)
theorem B1076021 : Blo 714321 1076021 := bbase (se 5 (by rfl) ⟨50438, by rfl⟩ : syracuseStep 1076021 = 100877) (by norm_num)
theorem B1207109 : Blo 714321 1207109 := bbase (se 4 (by rfl) ⟨113166, by rfl⟩ : syracuseStep 1207109 = 226333) (by norm_num)
theorem B1076045 : Blo 714321 1076045 := bbase (se 3 (by rfl) ⟨201758, by rfl⟩ : syracuseStep 1076045 = 403517) (by norm_num)
theorem B1076069 : Blo 714321 1076069 := bbase (se 4 (by rfl) ⟨100881, by rfl⟩ : syracuseStep 1076069 = 201763) (by norm_num)
theorem B1076093 : Blo 714321 1076093 := bbase (se 3 (by rfl) ⟨201767, by rfl⟩ : syracuseStep 1076093 = 403535) (by norm_num)
theorem B1076117 : Blo 714321 1076117 := bbase (se 6 (by rfl) ⟨25221, by rfl⟩ : syracuseStep 1076117 = 50443) (by norm_num)
theorem B1076141 : Blo 714321 1076141 := bbase (se 3 (by rfl) ⟨201776, by rfl⟩ : syracuseStep 1076141 = 403553) (by norm_num)
theorem B1207237 : Blo 714321 1207237 := bbase (se 4 (by rfl) ⟨113178, by rfl⟩ : syracuseStep 1207237 = 226357) (by norm_num)
theorem B1076165 : Blo 714321 1076165 := bbase (se 4 (by rfl) ⟨100890, by rfl⟩ : syracuseStep 1076165 = 201781) (by norm_num)
theorem B1076189 : Blo 714321 1076189 := bbase (se 3 (by rfl) ⟨201785, by rfl⟩ : syracuseStep 1076189 = 403571) (by norm_num)
theorem B3435493 : Blo 714321 3435493 := bbase (se 4 (by rfl) ⟨322077, by rfl⟩ : syracuseStep 3435493 = 644155) (by norm_num)
theorem B2419685 : Blo 714321 2419685 := bbase (se 4 (by rfl) ⟨226845, by rfl⟩ : syracuseStep 2419685 = 453691) (by norm_num)
theorem B1076213 : Blo 714321 1076213 := bbase (se 5 (by rfl) ⟨50447, by rfl⟩ : syracuseStep 1076213 = 100895) (by norm_num)
theorem B1076237 : Blo 714321 1076237 := bbase (se 3 (by rfl) ⟨201794, by rfl⟩ : syracuseStep 1076237 = 403589) (by norm_num)
theorem B1207325 : Blo 714321 1207325 := bbase (se 3 (by rfl) ⟨226373, by rfl⟩ : syracuseStep 1207325 = 452747) (by norm_num)
theorem B1076261 : Blo 714321 1076261 := bbase (se 4 (by rfl) ⟨100899, by rfl⟩ : syracuseStep 1076261 = 201799) (by norm_num)
theorem B1076285 : Blo 714321 1076285 := bbase (se 3 (by rfl) ⟨201803, by rfl⟩ : syracuseStep 1076285 = 403607) (by norm_num)
theorem B1076309 : Blo 714321 1076309 := bbase (se 8 (by rfl) ⟨6306, by rfl⟩ : syracuseStep 1076309 = 12613) (by norm_num)
theorem B1076333 : Blo 714321 1076333 := bbase (se 3 (by rfl) ⟨201812, by rfl⟩ : syracuseStep 1076333 = 403625) (by norm_num)
theorem B1076357 : Blo 714321 1076357 := bbase (se 4 (by rfl) ⟨100908, by rfl⟩ : syracuseStep 1076357 = 201817) (by norm_num)
theorem B1207453 : Blo 714321 1207453 := bbase (se 3 (by rfl) ⟨226397, by rfl⟩ : syracuseStep 1207453 = 452795) (by norm_num)
theorem B1076381 : Blo 714321 1076381 := bbase (se 3 (by rfl) ⟨201821, by rfl⟩ : syracuseStep 1076381 = 403643) (by norm_num)
theorem B1076405 : Blo 714321 1076405 := bbase (se 5 (by rfl) ⟨50456, by rfl⟩ : syracuseStep 1076405 = 100913) (by norm_num)
theorem B1076429 : Blo 714321 1076429 := bbase (se 3 (by rfl) ⟨201830, by rfl⟩ : syracuseStep 1076429 = 403661) (by norm_num)
theorem B1076453 : Blo 714321 1076453 := bbase (se 4 (by rfl) ⟨100917, by rfl⟩ : syracuseStep 1076453 = 201835) (by norm_num)
theorem B1207541 : Blo 714321 1207541 := bbase (se 5 (by rfl) ⟨56603, by rfl⟩ : syracuseStep 1207541 = 113207) (by norm_num)
theorem B1076477 : Blo 714321 1076477 := bbase (se 3 (by rfl) ⟨201839, by rfl⟩ : syracuseStep 1076477 = 403679) (by norm_num)
theorem B1076501 : Blo 714321 1076501 := bbase (se 6 (by rfl) ⟨25230, by rfl⟩ : syracuseStep 1076501 = 50461) (by norm_num)
theorem B2714917 : Blo 714321 2714917 := bbase (se 4 (by rfl) ⟨254523, by rfl⟩ : syracuseStep 2714917 = 509047) (by norm_num)
theorem B1076525 : Blo 714321 1076525 := bbase (se 3 (by rfl) ⟨201848, by rfl⟩ : syracuseStep 1076525 = 403697) (by norm_num)
theorem B3108149 : Blo 714321 3108149 := bbase (se 5 (by rfl) ⟨145694, by rfl⟩ : syracuseStep 3108149 = 291389) (by norm_num)
theorem B1076549 : Blo 714321 1076549 := bbase (se 4 (by rfl) ⟨100926, by rfl⟩ : syracuseStep 1076549 = 201853) (by norm_num)
theorem B1076573 : Blo 714321 1076573 := bbase (se 3 (by rfl) ⟨201857, by rfl⟩ : syracuseStep 1076573 = 403715) (by norm_num)
theorem B1633637 : Blo 714321 1633637 := bbase (se 4 (by rfl) ⟨153153, by rfl⟩ : syracuseStep 1633637 = 306307) (by norm_num)
theorem B1207669 : Blo 714321 1207669 := bbase (se 5 (by rfl) ⟨56609, by rfl⟩ : syracuseStep 1207669 = 113219) (by norm_num)
theorem B1076597 : Blo 714321 1076597 := bbase (se 5 (by rfl) ⟨50465, by rfl⟩ : syracuseStep 1076597 = 100931) (by norm_num)
theorem B1076621 : Blo 714321 1076621 := bbase (se 3 (by rfl) ⟨201866, by rfl⟩ : syracuseStep 1076621 = 403733) (by norm_num)
theorem B2420117 : Blo 714321 2420117 := bbase (se 6 (by rfl) ⟨56721, by rfl⟩ : syracuseStep 2420117 = 113443) (by norm_num)
theorem B1076645 : Blo 714321 1076645 := bbase (se 4 (by rfl) ⟨100935, by rfl⟩ : syracuseStep 1076645 = 201871) (by norm_num)
theorem B1076669 : Blo 714321 1076669 := bbase (se 3 (by rfl) ⟨201875, by rfl⟩ : syracuseStep 1076669 = 403751) (by norm_num)
theorem B1207757 : Blo 714321 1207757 := bbase (se 3 (by rfl) ⟨226454, by rfl⟩ : syracuseStep 1207757 = 452909) (by norm_num)
theorem B1076693 : Blo 714321 1076693 := bbase (se 7 (by rfl) ⟨12617, by rfl⟩ : syracuseStep 1076693 = 25235) (by norm_num)
theorem B1076717 : Blo 714321 1076717 := bbase (se 3 (by rfl) ⟨201884, by rfl⟩ : syracuseStep 1076717 = 403769) (by norm_num)
theorem B1076741 : Blo 714321 1076741 := bbase (se 4 (by rfl) ⟨100944, by rfl⟩ : syracuseStep 1076741 = 201889) (by norm_num)
theorem B1076765 : Blo 714321 1076765 := bbase (se 3 (by rfl) ⟨201893, by rfl⟩ : syracuseStep 1076765 = 403787) (by norm_num)
theorem B1076789 : Blo 714321 1076789 := bbase (se 5 (by rfl) ⟨50474, by rfl⟩ : syracuseStep 1076789 = 100949) (by norm_num)
theorem B1207885 : Blo 714321 1207885 := bbase (se 3 (by rfl) ⟨226478, by rfl⟩ : syracuseStep 1207885 = 452957) (by norm_num)
theorem B1076813 : Blo 714321 1076813 := bbase (se 3 (by rfl) ⟨201902, by rfl⟩ : syracuseStep 1076813 = 403805) (by norm_num)
theorem B2715221 : Blo 714321 2715221 := bbase (se 8 (by rfl) ⟨15909, by rfl⟩ : syracuseStep 2715221 = 31819) (by norm_num)
theorem B1076837 : Blo 714321 1076837 := bbase (se 4 (by rfl) ⟨100953, by rfl⟩ : syracuseStep 1076837 = 201907) (by norm_num)
theorem B1076861 : Blo 714321 1076861 := bbase (se 3 (by rfl) ⟨201911, by rfl⟩ : syracuseStep 1076861 = 403823) (by norm_num)
theorem B1076885 : Blo 714321 1076885 := bbase (se 6 (by rfl) ⟨25239, by rfl⟩ : syracuseStep 1076885 = 50479) (by norm_num)
theorem B1207973 : Blo 714321 1207973 := bbase (se 4 (by rfl) ⟨113247, by rfl⟩ : syracuseStep 1207973 = 226495) (by norm_num)
theorem B1076909 : Blo 714321 1076909 := bbase (se 3 (by rfl) ⟨201920, by rfl⟩ : syracuseStep 1076909 = 403841) (by norm_num)
theorem B1076933 : Blo 714321 1076933 := bbase (se 4 (by rfl) ⟨100962, by rfl⟩ : syracuseStep 1076933 = 201925) (by norm_num)
theorem B1076957 : Blo 714321 1076957 := bbase (se 3 (by rfl) ⟨201929, by rfl⟩ : syracuseStep 1076957 = 403859) (by norm_num)
theorem B1076981 : Blo 714321 1076981 := bbase (se 5 (by rfl) ⟨50483, by rfl⟩ : syracuseStep 1076981 = 100967) (by norm_num)
theorem B1077005 : Blo 714321 1077005 := bbase (se 3 (by rfl) ⟨201938, by rfl⟩ : syracuseStep 1077005 = 403877) (by norm_num)
theorem B1208101 : Blo 714321 1208101 := bbase (se 4 (by rfl) ⟨113259, by rfl⟩ : syracuseStep 1208101 = 226519) (by norm_num)
theorem B1077029 : Blo 714321 1077029 := bbase (se 4 (by rfl) ⟨100971, by rfl⟩ : syracuseStep 1077029 = 201943) (by norm_num)
theorem B1077053 : Blo 714321 1077053 := bbase (se 3 (by rfl) ⟨201947, by rfl⟩ : syracuseStep 1077053 = 403895) (by norm_num)
theorem B2420549 : Blo 714321 2420549 := bbase (se 4 (by rfl) ⟨226926, by rfl⟩ : syracuseStep 2420549 = 453853) (by norm_num)
theorem B1077077 : Blo 714321 1077077 := bbase (se 9 (by rfl) ⟨3155, by rfl⟩ : syracuseStep 1077077 = 6311) (by norm_num)
theorem B2289509 : Blo 714321 2289509 := bbase (se 4 (by rfl) ⟨214641, by rfl⟩ : syracuseStep 2289509 = 429283) (by norm_num)
theorem B1077101 : Blo 714321 1077101 := bbase (se 3 (by rfl) ⟨201956, by rfl⟩ : syracuseStep 1077101 = 403913) (by norm_num)
theorem B1208189 : Blo 714321 1208189 := bbase (se 3 (by rfl) ⟨226535, by rfl⟩ : syracuseStep 1208189 = 453071) (by norm_num)
theorem B1077125 : Blo 714321 1077125 := bbase (se 4 (by rfl) ⟨100980, by rfl⟩ : syracuseStep 1077125 = 201961) (by norm_num)
theorem B1077149 : Blo 714321 1077149 := bbase (se 3 (by rfl) ⟨201965, by rfl⟩ : syracuseStep 1077149 = 403931) (by norm_num)
theorem B1077173 : Blo 714321 1077173 := bbase (se 5 (by rfl) ⟨50492, by rfl⟩ : syracuseStep 1077173 = 100985) (by norm_num)
theorem B1568717 : Blo 714321 1568717 := bbase (se 3 (by rfl) ⟨294134, by rfl⟩ : syracuseStep 1568717 = 588269) (by norm_num)
theorem B1077197 : Blo 714321 1077197 := bbase (se 3 (by rfl) ⟨201974, by rfl⟩ : syracuseStep 1077197 = 403949) (by norm_num)
theorem B1077221 : Blo 714321 1077221 := bbase (se 4 (by rfl) ⟨100989, by rfl⟩ : syracuseStep 1077221 = 201979) (by norm_num)
theorem B1208317 : Blo 714321 1208317 := bbase (se 3 (by rfl) ⟨226559, by rfl⟩ : syracuseStep 1208317 = 453119) (by norm_num)
theorem B1077245 : Blo 714321 1077245 := bbase (se 3 (by rfl) ⟨201983, by rfl⟩ : syracuseStep 1077245 = 403967) (by norm_num)
theorem B3633173 : Blo 714321 3633173 := bbase (se 6 (by rfl) ⟨85152, by rfl⟩ : syracuseStep 3633173 = 170305) (by norm_num)
theorem B1077269 : Blo 714321 1077269 := bbase (se 6 (by rfl) ⟨25248, by rfl⟩ : syracuseStep 1077269 = 50497) (by norm_num)
theorem B1077293 : Blo 714321 1077293 := bbase (se 3 (by rfl) ⟨201992, by rfl⟩ : syracuseStep 1077293 = 403985) (by norm_num)
theorem B1077317 : Blo 714321 1077317 := bbase (se 4 (by rfl) ⟨100998, by rfl⟩ : syracuseStep 1077317 = 201997) (by norm_num)
theorem B1208405 : Blo 714321 1208405 := bbase (se 8 (by rfl) ⟨7080, by rfl⟩ : syracuseStep 1208405 = 14161) (by norm_num)
theorem B1077341 : Blo 714321 1077341 := bbase (se 3 (by rfl) ⟨202001, by rfl⟩ : syracuseStep 1077341 = 404003) (by norm_num)
theorem B1077365 : Blo 714321 1077365 := bbase (se 5 (by rfl) ⟨50501, by rfl⟩ : syracuseStep 1077365 = 101003) (by norm_num)
theorem B1077389 : Blo 714321 1077389 := bbase (se 3 (by rfl) ⟨202010, by rfl⟩ : syracuseStep 1077389 = 404021) (by norm_num)
theorem B1077413 : Blo 714321 1077413 := bbase (se 4 (by rfl) ⟨101007, by rfl⟩ : syracuseStep 1077413 = 202015) (by norm_num)
theorem B1077437 : Blo 714321 1077437 := bbase (se 3 (by rfl) ⟨202019, by rfl⟩ : syracuseStep 1077437 = 404039) (by norm_num)
theorem B1208533 : Blo 714321 1208533 := bbase (se 7 (by rfl) ⟨14162, by rfl⟩ : syracuseStep 1208533 = 28325) (by norm_num)
theorem B1077461 : Blo 714321 1077461 := bbase (se 7 (by rfl) ⟨12626, by rfl⟩ : syracuseStep 1077461 = 25253) (by norm_num)
theorem B2420981 : Blo 714321 2420981 := bbase (se 5 (by rfl) ⟨113483, by rfl⟩ : syracuseStep 2420981 = 226967) (by norm_num)
theorem B1208621 : Blo 714321 1208621 := bbase (se 3 (by rfl) ⟨226616, by rfl⟩ : syracuseStep 1208621 = 453233) (by norm_num)
theorem B1208749 : Blo 714321 1208749 := bbase (se 3 (by rfl) ⟨226640, by rfl⟩ : syracuseStep 1208749 = 453281) (by norm_num)
theorem B4583861 : Blo 714321 4583861 := bbase (se 5 (by rfl) ⟨214868, by rfl⟩ : syracuseStep 4583861 = 429737) (by norm_num)
theorem B1208837 : Blo 714321 1208837 := bbase (se 4 (by rfl) ⟨113328, by rfl⟩ : syracuseStep 1208837 = 226657) (by norm_num)
theorem B2585125 : Blo 714321 2585125 := bbase (se 4 (by rfl) ⟨242355, by rfl⟩ : syracuseStep 2585125 = 484711) (by norm_num)
theorem B1208965 : Blo 714321 1208965 := bbase (se 4 (by rfl) ⟨113340, by rfl⟩ : syracuseStep 1208965 = 226681) (by norm_num)
theorem B2323109 : Blo 714321 2323109 := bbase (se 4 (by rfl) ⟨217791, by rfl⟩ : syracuseStep 2323109 = 435583) (by norm_num)
theorem B2421413 : Blo 714321 2421413 := bbase (se 4 (by rfl) ⟨227007, by rfl⟩ : syracuseStep 2421413 = 454015) (by norm_num)
theorem B1209053 : Blo 714321 1209053 := bbase (se 3 (by rfl) ⟨226697, by rfl⟩ : syracuseStep 1209053 = 453395) (by norm_num)
theorem B1635061 : Blo 714321 1635061 := bbase (se 5 (by rfl) ⟨76643, by rfl⟩ : syracuseStep 1635061 = 153287) (by norm_num)
theorem B1209181 : Blo 714321 1209181 := bbase (se 3 (by rfl) ⟨226721, by rfl⟩ : syracuseStep 1209181 = 453443) (by norm_num)
theorem B1209269 : Blo 714321 1209269 := bbase (se 5 (by rfl) ⟨56684, by rfl⟩ : syracuseStep 1209269 = 113369) (by norm_num)
theorem B1209397 : Blo 714321 1209397 := bbase (se 5 (by rfl) ⟨56690, by rfl⟩ : syracuseStep 1209397 = 113381) (by norm_num)
theorem B2421845 : Blo 714321 2421845 := bbase (se 8 (by rfl) ⟨14190, by rfl⟩ : syracuseStep 2421845 = 28381) (by norm_num)
theorem B1209485 : Blo 714321 1209485 := bbase (se 3 (by rfl) ⟨226778, by rfl⟩ : syracuseStep 1209485 = 453557) (by norm_num)
theorem B6124693 : Blo 714321 6124693 := bbase (se 6 (by rfl) ⟨143547, by rfl⟩ : syracuseStep 6124693 = 287095) (by norm_num)
theorem B1209613 : Blo 714321 1209613 := bbase (se 3 (by rfl) ⟨226802, by rfl⟩ : syracuseStep 1209613 = 453605) (by norm_num)
theorem B1766677 : Blo 714321 1766677 := bbase (se 6 (by rfl) ⟨41406, by rfl⟩ : syracuseStep 1766677 = 82813) (by norm_num)
theorem B3634469 : Blo 714321 3634469 := bbase (se 4 (by rfl) ⟨340731, by rfl⟩ : syracuseStep 3634469 = 681463) (by norm_num)
theorem B1209701 : Blo 714321 1209701 := bbase (se 4 (by rfl) ⟨113409, by rfl⟩ : syracuseStep 1209701 = 226819) (by norm_num)
theorem B1209829 : Blo 714321 1209829 := bbase (se 4 (by rfl) ⟨113421, by rfl⟩ : syracuseStep 1209829 = 226843) (by norm_num)
theorem B1144325 : Blo 714321 1144325 := bbase (se 4 (by rfl) ⟨107280, by rfl⟩ : syracuseStep 1144325 = 214561) (by norm_num)
theorem B2422277 : Blo 714321 2422277 := bbase (se 4 (by rfl) ⟨227088, by rfl⟩ : syracuseStep 2422277 = 454177) (by norm_num)
theorem B5174837 : Blo 714321 5174837 := bbase (se 5 (by rfl) ⟨242570, by rfl⟩ : syracuseStep 5174837 = 485141) (by norm_num)
theorem B1209917 : Blo 714321 1209917 := bbase (se 3 (by rfl) ⟨226859, by rfl⟩ : syracuseStep 1209917 = 453719) (by norm_num)
theorem B3929717 : Blo 714321 3929717 := bbase (se 5 (by rfl) ⟨184205, by rfl⟩ : syracuseStep 3929717 = 368411) (by norm_num)
theorem B2717333 : Blo 714321 2717333 := bbase (se 6 (by rfl) ⟨63687, by rfl⟩ : syracuseStep 2717333 = 127375) (by norm_num)
theorem B1210045 : Blo 714321 1210045 := bbase (se 3 (by rfl) ⟨226883, by rfl⟩ : syracuseStep 1210045 = 453767) (by norm_num)
theorem B1210133 : Blo 714321 1210133 := bbase (se 6 (by rfl) ⟨28362, by rfl⟩ : syracuseStep 1210133 = 56725) (by norm_num)
theorem B1210261 : Blo 714321 1210261 := bbase (se 6 (by rfl) ⟨28365, by rfl⟩ : syracuseStep 1210261 = 56731) (by norm_num)
theorem B1144741 : Blo 714321 1144741 := bbase (se 4 (by rfl) ⟨107319, by rfl⟩ : syracuseStep 1144741 = 214639) (by norm_num)
theorem B2717621 : Blo 714321 2717621 := bbase (se 5 (by rfl) ⟨127388, by rfl⟩ : syracuseStep 2717621 = 254777) (by norm_num)
theorem B2422709 : Blo 714321 2422709 := bbase (se 5 (by rfl) ⟨113564, by rfl⟩ : syracuseStep 2422709 = 227129) (by norm_num)
theorem B2947013 : Blo 714321 2947013 := bbase (se 4 (by rfl) ⟨276282, by rfl⟩ : syracuseStep 2947013 = 552565) (by norm_num)
theorem B1210349 : Blo 714321 1210349 := bbase (se 3 (by rfl) ⟨226940, by rfl⟩ : syracuseStep 1210349 = 453881) (by norm_num)
theorem B1210477 : Blo 714321 1210477 := bbase (se 3 (by rfl) ⟨226964, by rfl⟩ : syracuseStep 1210477 = 453929) (by norm_num)
theorem B1308853 : Blo 714321 1308853 := bbase (se 5 (by rfl) ⟨61352, by rfl⟩ : syracuseStep 1308853 = 122705) (by norm_num)
theorem B1210565 : Blo 714321 1210565 := bbase (se 4 (by rfl) ⟨113490, by rfl⟩ : syracuseStep 1210565 = 226981) (by norm_num)
theorem B6715669 : Blo 714321 6715669 := bbase (se 6 (by rfl) ⟨157398, by rfl⟩ : syracuseStep 6715669 = 314797) (by norm_num)
theorem B1210693 : Blo 714321 1210693 := bbase (se 4 (by rfl) ⟨113502, by rfl⟩ : syracuseStep 1210693 = 227005) (by norm_num)
theorem B2423141 : Blo 714321 2423141 := bbase (se 4 (by rfl) ⟨227169, by rfl⟩ : syracuseStep 2423141 = 454339) (by norm_num)
theorem B1210781 : Blo 714321 1210781 := bbase (se 3 (by rfl) ⟨227021, by rfl⟩ : syracuseStep 1210781 = 454043) (by norm_num)
theorem B981445 : Blo 714321 981445 := bbase (se 4 (by rfl) ⟨92010, by rfl⟩ : syracuseStep 981445 = 184021) (by norm_num)
theorem B1210909 : Blo 714321 1210909 := bbase (se 3 (by rfl) ⟨227045, by rfl⟩ : syracuseStep 1210909 = 454091) (by norm_num)
theorem B3635765 : Blo 714321 3635765 := bbase (se 5 (by rfl) ⟨170426, by rfl⟩ : syracuseStep 3635765 = 340853) (by norm_num)
theorem B883289 : Blo 714321 883289 := bbase (se 2 (by rfl) ⟨331233, by rfl⟩ : syracuseStep 883289 = 662467) (by norm_num)
theorem B1210997 : Blo 714321 1210997 := bbase (se 5 (by rfl) ⟨56765, by rfl⟩ : syracuseStep 1210997 = 113531) (by norm_num)
theorem B1211125 : Blo 714321 1211125 := bbase (se 5 (by rfl) ⟨56771, by rfl⟩ : syracuseStep 1211125 = 113543) (by norm_num)
theorem B2423573 : Blo 714321 2423573 := bbase (se 6 (by rfl) ⟨56802, by rfl⟩ : syracuseStep 2423573 = 113605) (by norm_num)
theorem B1473317 : Blo 714321 1473317 := bbase (se 4 (by rfl) ⟨138123, by rfl⟩ : syracuseStep 1473317 = 276247) (by norm_num)
theorem B1145677 : Blo 714321 1145677 := bbase (se 3 (by rfl) ⟨214814, by rfl⟩ : syracuseStep 1145677 = 429629) (by norm_num)
theorem B1211213 : Blo 714321 1211213 := bbase (se 3 (by rfl) ⟨227102, by rfl⟩ : syracuseStep 1211213 = 454205) (by norm_num)
theorem B1375133 : Blo 714321 1375133 := bbase (se 3 (by rfl) ⟨257837, by rfl⟩ : syracuseStep 1375133 = 515675) (by norm_num)
theorem B1211341 : Blo 714321 1211341 := bbase (se 3 (by rfl) ⟨227126, by rfl⟩ : syracuseStep 1211341 = 454253) (by norm_num)
theorem B9796565 : Blo 714321 9796565 := bbase (se 7 (by rfl) ⟨114803, by rfl⟩ : syracuseStep 9796565 = 229607) (by norm_num)
theorem B1211429 : Blo 714321 1211429 := bbase (se 4 (by rfl) ⟨113571, by rfl⟩ : syracuseStep 1211429 = 227143) (by norm_num)
theorem B916561 : Blo 714321 916561 := bbase (se 2 (by rfl) ⟨343710, by rfl⟩ : syracuseStep 916561 = 687421) (by norm_num)
theorem B2718805 : Blo 714321 2718805 := bbase (se 8 (by rfl) ⟨15930, by rfl⟩ : syracuseStep 2718805 = 31861) (by norm_num)
theorem B6126677 : Blo 714321 6126677 := bbase (se 8 (by rfl) ⟨35898, by rfl⟩ : syracuseStep 6126677 = 71797) (by norm_num)
theorem B785533 : Blo 714321 785533 := bbase (se 3 (by rfl) ⟨147287, by rfl⟩ : syracuseStep 785533 = 294575) (by norm_num)
theorem B1211557 : Blo 714321 1211557 := bbase (se 4 (by rfl) ⟨113583, by rfl⟩ : syracuseStep 1211557 = 227167) (by norm_num)
theorem B2424005 : Blo 714321 2424005 := bbase (se 4 (by rfl) ⟨227250, by rfl⟩ : syracuseStep 2424005 = 454501) (by norm_num)
theorem B1211645 : Blo 714321 1211645 := bbase (se 3 (by rfl) ⟨227183, by rfl⟩ : syracuseStep 1211645 = 454367) (by norm_num)
theorem B2456837 : Blo 714321 2456837 := bbase (se 4 (by rfl) ⟨230328, by rfl⟩ : syracuseStep 2456837 = 460657) (by norm_num)
theorem B1637653 : Blo 714321 1637653 := bbase (se 6 (by rfl) ⟨38382, by rfl⟩ : syracuseStep 1637653 = 76765) (by norm_num)
theorem B4914485 : Blo 714321 4914485 := bbase (se 5 (by rfl) ⟨230366, by rfl⟩ : syracuseStep 4914485 = 460733) (by norm_num)
theorem B1211773 : Blo 714321 1211773 := bbase (se 3 (by rfl) ⟨227207, by rfl⟩ : syracuseStep 1211773 = 454415) (by norm_num)
theorem B2719109 : Blo 714321 2719109 := bbase (se 4 (by rfl) ⟨254916, by rfl⟩ : syracuseStep 2719109 = 509833) (by norm_num)
theorem B1211861 : Blo 714321 1211861 := bbase (se 7 (by rfl) ⟨14201, by rfl⟩ : syracuseStep 1211861 = 28403) (by norm_num)
theorem B1834517 : Blo 714321 1834517 := bbase (se 6 (by rfl) ⟨42996, by rfl⟩ : syracuseStep 1834517 = 85993) (by norm_num)
theorem B1211989 : Blo 714321 1211989 := bbase (se 8 (by rfl) ⟨7101, by rfl⟩ : syracuseStep 1211989 = 14203) (by norm_num)
theorem B1212077 : Blo 714321 1212077 := bbase (se 3 (by rfl) ⟨227264, by rfl⟩ : syracuseStep 1212077 = 454529) (by norm_num)
theorem B2293429 : Blo 714321 2293429 := bbase (se 5 (by rfl) ⟨107504, by rfl⟩ : syracuseStep 2293429 = 215009) (by norm_num)
theorem B3440357 : Blo 714321 3440357 := bbase (se 4 (by rfl) ⟨322533, by rfl⟩ : syracuseStep 3440357 = 645067) (by norm_num)
theorem B2293685 : Blo 714321 2293685 := bbase (se 5 (by rfl) ⟨107516, by rfl⟩ : syracuseStep 2293685 = 215033) (by norm_num)
theorem B1146869 : Blo 714321 1146869 := bbase (se 5 (by rfl) ⟨53759, by rfl⟩ : syracuseStep 1146869 = 107519) (by norm_num)
theorem B1245235 : Blo 714321 1245235 := bstep (se 1 (by rfl) ⟨933926, by rfl⟩ : syracuseStep 1245235 = 1867853) B1867853
theorem B4128965 : Blo 714321 4128965 := bstep (se 4 (by rfl) ⟨387090, by rfl⟩ : syracuseStep 4128965 = 774181) B774181
theorem B2326801 : Blo 714321 2326801 := bstep (se 2 (by rfl) ⟨872550, by rfl⟩ : syracuseStep 2326801 = 1745101) B1745101
theorem B1933645 : Blo 714321 1933645 := bstep (se 3 (by rfl) ⟨362558, by rfl⟩ : syracuseStep 1933645 = 725117) B725117
theorem B4358897 : Blo 714321 4358897 := bstep (se 2 (by rfl) ⟨1634586, by rfl⟩ : syracuseStep 4358897 = 3269173) B3269173
theorem B2294659 : Blo 714321 2294659 := bstep (se 1 (by rfl) ⟨1720994, by rfl⟩ : syracuseStep 2294659 = 3441989) B3441989
theorem B1967075 : Blo 714321 1967075 := bstep (se 1 (by rfl) ⟨1475306, by rfl⟩ : syracuseStep 1967075 = 2950613) B2950613
theorem B2294801 : Blo 714321 2294801 := bstep (se 2 (by rfl) ⟨860550, by rfl⟩ : syracuseStep 2294801 = 1721101) B1721101
theorem B1148035 : Blo 714321 1148035 := bstep (se 1 (by rfl) ⟨861026, by rfl⟩ : syracuseStep 1148035 = 1722053) B1722053
theorem B4588805 : Blo 714321 4588805 := bstep (se 4 (by rfl) ⟨430200, by rfl⟩ : syracuseStep 4588805 = 860401) B860401
theorem B1934605 : Blo 714321 1934605 := bstep (se 3 (by rfl) ⟨362738, by rfl⟩ : syracuseStep 1934605 = 725477) B725477
theorem B1836611 : Blo 714321 1836611 := bstep (se 1 (by rfl) ⟨1377458, by rfl⟩ : syracuseStep 1836611 = 2754917) B2754917
theorem B1148483 : Blo 714321 1148483 := bstep (se 1 (by rfl) ⟨861362, by rfl⟩ : syracuseStep 1148483 = 1722725) B1722725
theorem B1607345 : Blo 714321 1607345 := bstep (se 2 (by rfl) ⟨602754, by rfl⟩ : syracuseStep 1607345 = 1205509) B1205509
theorem B3671729 : Blo 714321 3671729 := bstep (se 2 (by rfl) ⟨1376898, by rfl⟩ : syracuseStep 3671729 = 2753797) B2753797
theorem B1607363 : Blo 714321 1607363 := bstep (se 1 (by rfl) ⟨1205522, by rfl⟩ : syracuseStep 1607363 = 2411045) B2411045
theorem B2328515 : Blo 714321 2328515 := bstep (se 1 (by rfl) ⟨1746386, by rfl⟩ : syracuseStep 2328515 = 3492773) B3492773
theorem B1607633 : Blo 714321 1607633 := bstep (se 2 (by rfl) ⟨602862, by rfl⟩ : syracuseStep 1607633 = 1205725) B1205725
theorem B1607651 : Blo 714321 1607651 := bstep (se 1 (by rfl) ⟨1205738, by rfl⟩ : syracuseStep 1607651 = 2411477) B2411477
theorem B1149041 : Blo 714321 1149041 := bstep (se 2 (by rfl) ⟨430890, by rfl⟩ : syracuseStep 1149041 = 861781) B861781
theorem B1837187 : Blo 714321 1837187 := bstep (se 1 (by rfl) ⟨1377890, by rfl⟩ : syracuseStep 1837187 = 2755781) B2755781
theorem B1018003 : Blo 714321 1018003 := bstep (se 1 (by rfl) ⟨763502, by rfl⟩ : syracuseStep 1018003 = 1527005) B1527005
theorem B1607921 : Blo 714321 1607921 := bstep (se 2 (by rfl) ⟨602970, by rfl⟩ : syracuseStep 1607921 = 1205941) B1205941
theorem B1607939 : Blo 714321 1607939 := bstep (se 1 (by rfl) ⟨1205954, by rfl⟩ : syracuseStep 1607939 = 2411909) B2411909
theorem B1378627 : Blo 714321 1378627 := bstep (se 1 (by rfl) ⟨1033970, by rfl⟩ : syracuseStep 1378627 = 2067941) B2067941
theorem B2296145 : Blo 714321 2296145 := bstep (se 2 (by rfl) ⟨861054, by rfl⟩ : syracuseStep 2296145 = 1722109) B1722109
theorem B1149265 : Blo 714321 1149265 := bstep (se 2 (by rfl) ⟨430974, by rfl⟩ : syracuseStep 1149265 = 861949) B861949
theorem B1378691 : Blo 714321 1378691 := bstep (se 1 (by rfl) ⟨1034018, by rfl⟩ : syracuseStep 1378691 = 2068037) B2068037
theorem B1149329 : Blo 714321 1149329 := bstep (se 2 (by rfl) ⟨430998, by rfl⟩ : syracuseStep 1149329 = 861997) B861997
theorem B2394541 : Blo 714321 2394541 := bstep (se 3 (by rfl) ⟨448976, by rfl⟩ : syracuseStep 2394541 = 897953) B897953
theorem B1608209 : Blo 714321 1608209 := bstep (se 2 (by rfl) ⟨603078, by rfl⟩ : syracuseStep 1608209 = 1206157) B1206157
theorem B1149457 : Blo 714321 1149457 := bstep (se 2 (by rfl) ⟨431046, by rfl⟩ : syracuseStep 1149457 = 862093) B862093
theorem B1608227 : Blo 714321 1608227 := bstep (se 1 (by rfl) ⟨1206170, by rfl⟩ : syracuseStep 1608227 = 2412341) B2412341
theorem B3672611 : Blo 714321 3672611 := bstep (se 1 (by rfl) ⟨2754458, by rfl⟩ : syracuseStep 3672611 = 5508917) B5508917
theorem B2722481 : Blo 714321 2722481 := bstep (se 2 (by rfl) ⟨1020930, by rfl⟩ : syracuseStep 2722481 = 2041861) B2041861
theorem B6130403 : Blo 714321 6130403 := bstep (se 1 (by rfl) ⟨4597802, by rfl⟩ : syracuseStep 6130403 = 9195605) B9195605
theorem B1608497 : Blo 714321 1608497 := bstep (se 2 (by rfl) ⟨603186, by rfl⟩ : syracuseStep 1608497 = 1206373) B1206373
theorem B1608515 : Blo 714321 1608515 := bstep (se 1 (by rfl) ⟨1206386, by rfl⟩ : syracuseStep 1608515 = 2412773) B2412773
theorem B1608785 : Blo 714321 1608785 := bstep (se 2 (by rfl) ⟨603294, by rfl⟩ : syracuseStep 1608785 = 1206589) B1206589
theorem B1608803 : Blo 714321 1608803 := bstep (se 1 (by rfl) ⟨1206602, by rfl⟩ : syracuseStep 1608803 = 2413205) B2413205
theorem B4590755 : Blo 714321 4590755 := bstep (se 1 (by rfl) ⟨3443066, by rfl⟩ : syracuseStep 4590755 = 6886133) B6886133
theorem B724147 : Blo 714321 724147 := bstep (se 1 (by rfl) ⟨543110, by rfl⟩ : syracuseStep 724147 = 1086221) B1086221
theorem B1117363 : Blo 714321 1117363 := bstep (se 1 (by rfl) ⟨838022, by rfl⟩ : syracuseStep 1117363 = 1676045) B1676045
theorem B2297069 : Blo 714321 2297069 := bstep (se 3 (by rfl) ⟨430700, by rfl⟩ : syracuseStep 2297069 = 861401) B861401
theorem B1019137 : Blo 714321 1019137 := bstep (se 2 (by rfl) ⟨382176, by rfl⟩ : syracuseStep 1019137 = 764353) B764353
theorem B920851 : Blo 714321 920851 := bstep (se 1 (by rfl) ⟨690638, by rfl⟩ : syracuseStep 920851 = 1381277) B1381277
theorem B1019233 : Blo 714321 1019233 := bstep (se 2 (by rfl) ⟨382212, by rfl⟩ : syracuseStep 1019233 = 764425) B764425
theorem B1609073 : Blo 714321 1609073 := bstep (se 2 (by rfl) ⟨603402, by rfl⟩ : syracuseStep 1609073 = 1206805) B1206805
theorem B724339 : Blo 714321 724339 := bstep (se 1 (by rfl) ⟨543254, by rfl⟩ : syracuseStep 724339 = 1086509) B1086509
theorem B1609091 : Blo 714321 1609091 := bstep (se 1 (by rfl) ⟨1206818, by rfl⟩ : syracuseStep 1609091 = 2413637) B2413637
theorem B2297261 : Blo 714321 2297261 := bstep (se 3 (by rfl) ⟨430736, by rfl⟩ : syracuseStep 2297261 = 861473) B861473
theorem B2035277 : Blo 714321 2035277 := bstep (se 3 (by rfl) ⟨381614, by rfl⟩ : syracuseStep 2035277 = 763229) B763229
theorem B1609361 : Blo 714321 1609361 := bstep (se 2 (by rfl) ⟨603510, by rfl⟩ : syracuseStep 1609361 = 1207021) B1207021
theorem B1609379 : Blo 714321 1609379 := bstep (se 1 (by rfl) ⟨1207034, by rfl⟩ : syracuseStep 1609379 = 2414069) B2414069
theorem B1937105 : Blo 714321 1937105 := bstep (se 2 (by rfl) ⟨726414, by rfl⟩ : syracuseStep 1937105 = 1452829) B1452829
theorem B2035459 : Blo 714321 2035459 := bstep (se 1 (by rfl) ⟨1526594, by rfl⟩ : syracuseStep 2035459 = 3053189) B3053189
theorem B2035505 : Blo 714321 2035505 := bstep (se 2 (by rfl) ⟨763314, by rfl⟩ : syracuseStep 2035505 = 1526629) B1526629
theorem B1019729 : Blo 714321 1019729 := bstep (se 2 (by rfl) ⟨382398, by rfl⟩ : syracuseStep 1019729 = 764797) B764797
theorem B1609649 : Blo 714321 1609649 := bstep (se 2 (by rfl) ⟨603618, by rfl⟩ : syracuseStep 1609649 = 1207237) B1207237
theorem B1609667 : Blo 714321 1609667 := bstep (se 1 (by rfl) ⟨1207250, by rfl⟩ : syracuseStep 1609667 = 2414501) B2414501
theorem B3051533 : Blo 714321 3051533 := bstep (se 3 (by rfl) ⟨572162, by rfl⟩ : syracuseStep 3051533 = 1144325) B1144325
theorem B8163341 : Blo 714321 8163341 := bstep (se 3 (by rfl) ⟨1530626, by rfl⟩ : syracuseStep 8163341 = 3061253) B3061253
theorem B2723939 : Blo 714321 2723939 := bstep (se 1 (by rfl) ⟨2042954, by rfl⟩ : syracuseStep 2723939 = 4085909) B4085909
theorem B1609937 : Blo 714321 1609937 := bstep (se 2 (by rfl) ⟨603726, by rfl⟩ : syracuseStep 1609937 = 1207453) B1207453
theorem B1609955 : Blo 714321 1609955 := bstep (se 1 (by rfl) ⟨1207466, by rfl⟩ : syracuseStep 1609955 = 2414933) B2414933
theorem B1937677 : Blo 714321 1937677 := bstep (se 3 (by rfl) ⟨363314, by rfl⟩ : syracuseStep 1937677 = 726629) B726629
theorem B1610225 : Blo 714321 1610225 := bstep (se 2 (by rfl) ⟨603834, by rfl⟩ : syracuseStep 1610225 = 1207669) B1207669
theorem B1610243 : Blo 714321 1610243 := bstep (se 1 (by rfl) ⟨1207682, by rfl⟩ : syracuseStep 1610243 = 2415365) B2415365
theorem B1938001 : Blo 714321 1938001 := bstep (se 2 (by rfl) ⟨726750, by rfl⟩ : syracuseStep 1938001 = 1453501) B1453501
theorem B1020595 : Blo 714321 1020595 := bstep (se 1 (by rfl) ⟨765446, by rfl⟩ : syracuseStep 1020595 = 1530893) B1530893
theorem B1610513 : Blo 714321 1610513 := bstep (se 2 (by rfl) ⟨603942, by rfl⟩ : syracuseStep 1610513 = 1207885) B1207885
theorem B1020691 : Blo 714321 1020691 := bstep (se 1 (by rfl) ⟨765518, by rfl⟩ : syracuseStep 1020691 = 1531037) B1531037
theorem B1610531 : Blo 714321 1610531 := bstep (se 1 (by rfl) ⟨1207898, by rfl⟩ : syracuseStep 1610531 = 2415797) B2415797
theorem B1610801 : Blo 714321 1610801 := bstep (se 2 (by rfl) ⟨604050, by rfl⟩ : syracuseStep 1610801 = 1208101) B1208101
theorem B1610819 : Blo 714321 1610819 := bstep (se 1 (by rfl) ⟨1208114, by rfl⟩ : syracuseStep 1610819 = 2416229) B2416229
theorem B2724941 : Blo 714321 2724941 := bstep (se 3 (by rfl) ⟨510926, by rfl⟩ : syracuseStep 2724941 = 1021853) B1021853
theorem B2299043 : Blo 714321 2299043 := bstep (se 1 (by rfl) ⟨1724282, by rfl⟩ : syracuseStep 2299043 = 3448565) B3448565
theorem B2036963 : Blo 714321 2036963 := bstep (se 1 (by rfl) ⟨1527722, by rfl⟩ : syracuseStep 2036963 = 3055445) B3055445
theorem B58758371 : Blo 714321 58758371 := bstep (se 1 (by rfl) ⟨44068778, by rfl⟩ : syracuseStep 58758371 = 88137557) B88137557
theorem B1021187 : Blo 714321 1021187 := bstep (se 1 (by rfl) ⟨765890, by rfl⟩ : syracuseStep 1021187 = 1531781) B1531781
theorem B3872069 : Blo 714321 3872069 := bstep (se 4 (by rfl) ⟨363006, by rfl⟩ : syracuseStep 3872069 = 726013) B726013
theorem B1611089 : Blo 714321 1611089 := bstep (se 2 (by rfl) ⟨604158, by rfl⟩ : syracuseStep 1611089 = 1208317) B1208317
theorem B1611107 : Blo 714321 1611107 := bstep (se 1 (by rfl) ⟨1208330, by rfl⟩ : syracuseStep 1611107 = 2416661) B2416661
theorem B4068913 : Blo 714321 4068913 := bstep (se 2 (by rfl) ⟨1525842, by rfl⟩ : syracuseStep 4068913 = 3051685) B3051685
theorem B1611377 : Blo 714321 1611377 := bstep (se 2 (by rfl) ⟨604266, by rfl⟩ : syracuseStep 1611377 = 1208533) B1208533
theorem B1611395 : Blo 714321 1611395 := bstep (se 1 (by rfl) ⟨1208546, by rfl⟩ : syracuseStep 1611395 = 2417093) B2417093
theorem B4593293 : Blo 714321 4593293 := bstep (se 3 (by rfl) ⟨861242, by rfl⟩ : syracuseStep 4593293 = 1722485) B1722485
theorem B4888325 : Blo 714321 4888325 := bstep (se 4 (by rfl) ⟨458280, by rfl⟩ : syracuseStep 4888325 = 916561) B916561
theorem B1021825 : Blo 714321 1021825 := bstep (se 2 (by rfl) ⟨383184, by rfl⟩ : syracuseStep 1021825 = 766369) B766369
theorem B1611665 : Blo 714321 1611665 := bstep (se 2 (by rfl) ⟨604374, by rfl⟩ : syracuseStep 1611665 = 1208749) B1208749
theorem B1611683 : Blo 714321 1611683 := bstep (se 1 (by rfl) ⟨1208762, by rfl⟩ : syracuseStep 1611683 = 2417525) B2417525
theorem B727075 : Blo 714321 727075 := bstep (se 1 (by rfl) ⟨545306, by rfl⟩ : syracuseStep 727075 = 1090613) B1090613
theorem B3446833 : Blo 714321 3446833 := bstep (se 2 (by rfl) ⟨1292562, by rfl⟩ : syracuseStep 3446833 = 2585125) B2585125
theorem B1611953 : Blo 714321 1611953 := bstep (se 2 (by rfl) ⟨604482, by rfl⟩ : syracuseStep 1611953 = 1208965) B1208965
theorem B1611971 : Blo 714321 1611971 := bstep (se 1 (by rfl) ⟨1208978, by rfl⟩ : syracuseStep 1611971 = 2417957) B2417957
theorem B1022161 : Blo 714321 1022161 := bstep (se 2 (by rfl) ⟨383310, by rfl⟩ : syracuseStep 1022161 = 766621) B766621
theorem B1808689 : Blo 714321 1808689 := bstep (se 2 (by rfl) ⟨678258, by rfl⟩ : syracuseStep 1808689 = 1356517) B1356517
theorem B858451 : Blo 714321 858451 := bstep (se 1 (by rfl) ⟨643838, by rfl⟩ : syracuseStep 858451 = 1287677) B1287677
theorem B2038193 : Blo 714321 2038193 := bstep (se 2 (by rfl) ⟨764322, by rfl⟩ : syracuseStep 2038193 = 1528645) B1528645
theorem B1612241 : Blo 714321 1612241 := bstep (se 2 (by rfl) ⟨604590, by rfl⟩ : syracuseStep 1612241 = 1209181) B1209181
theorem B1612259 : Blo 714321 1612259 := bstep (se 1 (by rfl) ⟨1209194, by rfl⟩ : syracuseStep 1612259 = 2418389) B2418389
theorem B5446115 : Blo 714321 5446115 := bstep (se 1 (by rfl) ⟨4084586, by rfl⟩ : syracuseStep 5446115 = 8169173) B8169173
theorem B1808963 : Blo 714321 1808963 := bstep (se 1 (by rfl) ⟨1356722, by rfl⟩ : syracuseStep 1808963 = 2713445) B2713445
theorem B1940141 : Blo 714321 1940141 := bstep (se 3 (by rfl) ⟨363776, by rfl⟩ : syracuseStep 1940141 = 727553) B727553
theorem B1612529 : Blo 714321 1612529 := bstep (se 2 (by rfl) ⟨604698, by rfl⟩ : syracuseStep 1612529 = 1209397) B1209397
theorem B1809155 : Blo 714321 1809155 := bstep (se 1 (by rfl) ⟨1356866, by rfl⟩ : syracuseStep 1809155 = 2713733) B2713733
theorem B1612547 : Blo 714321 1612547 := bstep (se 1 (by rfl) ⟨1209410, by rfl⟩ : syracuseStep 1612547 = 2418821) B2418821
theorem B1022753 : Blo 714321 1022753 := bstep (se 2 (by rfl) ⟨383532, by rfl⟩ : syracuseStep 1022753 = 767065) B767065
theorem B8166257 : Blo 714321 8166257 := bstep (se 2 (by rfl) ⟨3062346, by rfl⟩ : syracuseStep 8166257 = 6124693) B6124693
theorem B4070371 : Blo 714321 4070371 := bstep (se 1 (by rfl) ⟨3052778, by rfl⟩ : syracuseStep 4070371 = 6105557) B6105557
theorem B1612817 : Blo 714321 1612817 := bstep (se 2 (by rfl) ⟨604806, by rfl⟩ : syracuseStep 1612817 = 1209613) B1209613
theorem B859171 : Blo 714321 859171 := bstep (se 1 (by rfl) ⟨644378, by rfl⟩ : syracuseStep 859171 = 1288757) B1288757
theorem B1612835 : Blo 714321 1612835 := bstep (se 1 (by rfl) ⟨1209626, by rfl⟩ : syracuseStep 1612835 = 2419253) B2419253
theorem B859267 : Blo 714321 859267 := bstep (se 1 (by rfl) ⟨644450, by rfl⟩ : syracuseStep 859267 = 1288901) B1288901
theorem B2727053 : Blo 714321 2727053 := bstep (se 3 (by rfl) ⟨511322, by rfl⟩ : syracuseStep 2727053 = 1022645) B1022645
theorem B2301169 : Blo 714321 2301169 := bstep (se 2 (by rfl) ⟨862938, by rfl⟩ : syracuseStep 2301169 = 1725877) B1725877
theorem B1613105 : Blo 714321 1613105 := bstep (se 2 (by rfl) ⟨604914, by rfl⟩ : syracuseStep 1613105 = 1209829) B1209829
theorem B1613123 : Blo 714321 1613123 := bstep (se 1 (by rfl) ⟨1209842, by rfl⟩ : syracuseStep 1613123 = 2419685) B2419685
theorem B7839089 : Blo 714321 7839089 := bstep (se 2 (by rfl) ⟨2939658, by rfl⟩ : syracuseStep 7839089 = 5879317) B5879317
theorem B4070897 : Blo 714321 4070897 := bstep (se 2 (by rfl) ⟨1526586, by rfl⟩ : syracuseStep 4070897 = 3053173) B3053173
theorem B2072099 : Blo 714321 2072099 := bstep (se 1 (by rfl) ⟨1554074, by rfl⟩ : syracuseStep 2072099 = 3108149) B3108149
theorem B1089091 : Blo 714321 1089091 := bstep (se 1 (by rfl) ⟨816818, by rfl⟩ : syracuseStep 1089091 = 1633637) B1633637
theorem B1613393 : Blo 714321 1613393 := bstep (se 2 (by rfl) ⟨605022, by rfl⟩ : syracuseStep 1613393 = 1210045) B1210045
theorem B1613411 : Blo 714321 1613411 := bstep (se 1 (by rfl) ⟨1210058, by rfl⟩ : syracuseStep 1613411 = 2420117) B2420117
theorem B1810097 : Blo 714321 1810097 := bstep (se 2 (by rfl) ⟨678786, by rfl⟩ : syracuseStep 1810097 = 1357573) B1357573
theorem B1810147 : Blo 714321 1810147 := bstep (se 1 (by rfl) ⟨1357610, by rfl⟩ : syracuseStep 1810147 = 2715221) B2715221
theorem B2039651 : Blo 714321 2039651 := bstep (se 1 (by rfl) ⟨1529738, by rfl⟩ : syracuseStep 2039651 = 3059477) B3059477
theorem B1810289 : Blo 714321 1810289 := bstep (se 2 (by rfl) ⟨678858, by rfl⟩ : syracuseStep 1810289 = 1357717) B1357717
theorem B1613681 : Blo 714321 1613681 := bstep (se 2 (by rfl) ⟨605130, by rfl⟩ : syracuseStep 1613681 = 1210261) B1210261
theorem B1613699 : Blo 714321 1613699 := bstep (se 1 (by rfl) ⟨1210274, by rfl⟩ : syracuseStep 1613699 = 2420549) B2420549
theorem B1613969 : Blo 714321 1613969 := bstep (se 2 (by rfl) ⟨605238, by rfl⟩ : syracuseStep 1613969 = 1210477) B1210477
theorem B1613987 : Blo 714321 1613987 := bstep (se 1 (by rfl) ⟨1210490, by rfl⟩ : syracuseStep 1613987 = 2420981) B2420981
theorem B1745137 : Blo 714321 1745137 := bstep (se 2 (by rfl) ⟨654426, by rfl⟩ : syracuseStep 1745137 = 1308853) B1308853
theorem B3055907 : Blo 714321 3055907 := bstep (se 1 (by rfl) ⟨2291930, by rfl⟩ : syracuseStep 3055907 = 4583861) B4583861
theorem B8954225 : Blo 714321 8954225 := bstep (se 2 (by rfl) ⟨3357834, by rfl⟩ : syracuseStep 8954225 = 6715669) B6715669
theorem B1614257 : Blo 714321 1614257 := bstep (se 2 (by rfl) ⟨605346, by rfl⟩ : syracuseStep 1614257 = 1210693) B1210693
theorem B1548739 : Blo 714321 1548739 := bstep (se 1 (by rfl) ⟨1161554, by rfl⟩ : syracuseStep 1548739 = 2323109) B2323109
theorem B1450435 : Blo 714321 1450435 := bstep (se 1 (by rfl) ⟨1087826, by rfl⟩ : syracuseStep 1450435 = 2175653) B2175653
theorem B1614275 : Blo 714321 1614275 := bstep (se 1 (by rfl) ⟨1210706, by rfl⟩ : syracuseStep 1614275 = 2421413) B2421413
theorem B2040461 : Blo 714321 2040461 := bstep (se 3 (by rfl) ⟨382586, by rfl⟩ : syracuseStep 2040461 = 765173) B765173
theorem B1614545 : Blo 714321 1614545 := bstep (se 2 (by rfl) ⟨605454, by rfl⟩ : syracuseStep 1614545 = 1210909) B1210909
theorem B1614563 : Blo 714321 1614563 := bstep (se 1 (by rfl) ⟨1210922, by rfl⟩ : syracuseStep 1614563 = 2421845) B2421845
theorem B2040653 : Blo 714321 2040653 := bstep (se 3 (by rfl) ⟨382622, by rfl⟩ : syracuseStep 2040653 = 765245) B765245
theorem B1811281 : Blo 714321 1811281 := bstep (se 2 (by rfl) ⟨679230, by rfl⟩ : syracuseStep 1811281 = 1358461) B1358461
theorem B4072355 : Blo 714321 4072355 := bstep (se 1 (by rfl) ⟨3054266, by rfl⟩ : syracuseStep 4072355 = 6108533) B6108533
theorem B1614833 : Blo 714321 1614833 := bstep (se 2 (by rfl) ⟨605562, by rfl⟩ : syracuseStep 1614833 = 1211125) B1211125
theorem B1614851 : Blo 714321 1614851 := bstep (se 1 (by rfl) ⟨1211138, by rfl⟩ : syracuseStep 1614851 = 2422277) B2422277
theorem B3449891 : Blo 714321 3449891 := bstep (se 1 (by rfl) ⟨2587418, by rfl⟩ : syracuseStep 3449891 = 5174837) B5174837
theorem B1811555 : Blo 714321 1811555 := bstep (se 1 (by rfl) ⟨1358666, by rfl⟩ : syracuseStep 1811555 = 2717333) B2717333
theorem B3450061 : Blo 714321 3450061 := bstep (se 3 (by rfl) ⟨646886, by rfl⟩ : syracuseStep 3450061 = 1293773) B1293773
theorem B1615121 : Blo 714321 1615121 := bstep (se 2 (by rfl) ⟨605670, by rfl⟩ : syracuseStep 1615121 = 1211341) B1211341
theorem B1811747 : Blo 714321 1811747 := bstep (se 1 (by rfl) ⟨1358810, by rfl⟩ : syracuseStep 1811747 = 2717621) B2717621
theorem B1615139 : Blo 714321 1615139 := bstep (se 1 (by rfl) ⟨1211354, by rfl⟩ : syracuseStep 1615139 = 2422709) B2422709
theorem B1615409 : Blo 714321 1615409 := bstep (se 2 (by rfl) ⟨605778, by rfl⟩ : syracuseStep 1615409 = 1211557) B1211557
theorem B1615427 : Blo 714321 1615427 := bstep (se 1 (by rfl) ⟨1211570, by rfl⟩ : syracuseStep 1615427 = 2423141) B2423141
theorem B2041645 : Blo 714321 2041645 := bstep (se 3 (by rfl) ⟨382808, by rfl⟩ : syracuseStep 2041645 = 765617) B765617
theorem B1615697 : Blo 714321 1615697 := bstep (se 2 (by rfl) ⟨605886, by rfl⟩ : syracuseStep 1615697 = 1211773) B1211773
theorem B1615715 : Blo 714321 1615715 := bstep (se 1 (by rfl) ⟨1211786, by rfl⟩ : syracuseStep 1615715 = 2423573) B2423573
theorem B6531043 : Blo 714321 6531043 := bstep (se 1 (by rfl) ⟨4898282, by rfl⟩ : syracuseStep 6531043 = 9796565) B9796565
theorem B1615985 : Blo 714321 1615985 := bstep (se 2 (by rfl) ⟨605994, by rfl⟩ : syracuseStep 1615985 = 1211989) B1211989
theorem B1616003 : Blo 714321 1616003 := bstep (se 1 (by rfl) ⟨1212002, by rfl⟩ : syracuseStep 1616003 = 2424005) B2424005
theorem B1812689 : Blo 714321 1812689 := bstep (se 2 (by rfl) ⟨679758, by rfl⟩ : syracuseStep 1812689 = 1359517) B1359517
theorem B3057905 : Blo 714321 3057905 := bstep (se 2 (by rfl) ⟨1146714, by rfl⟩ : syracuseStep 3057905 = 2293429) B2293429
theorem B1812739 : Blo 714321 1812739 := bstep (se 1 (by rfl) ⟨1359554, by rfl⟩ : syracuseStep 1812739 = 2719109) B2719109
theorem B1223011 : Blo 714321 1223011 := bstep (se 1 (by rfl) ⟨917258, by rfl⟩ : syracuseStep 1223011 = 1834517) B1834517
theorem B1812881 : Blo 714321 1812881 := bstep (se 2 (by rfl) ⟨679830, by rfl⟩ : syracuseStep 1812881 = 1359661) B1359661
theorem B2238929 : Blo 714321 2238929 := bstep (se 2 (by rfl) ⟨839598, by rfl⟩ : syracuseStep 2238929 = 1679197) B1679197
theorem B1452593 : Blo 714321 1452593 := bstep (se 2 (by rfl) ⟨544722, by rfl⟩ : syracuseStep 1452593 = 1089445) B1089445
theorem B764579 : Blo 714321 764579 := bstep (se 1 (by rfl) ⟨573434, by rfl⟩ : syracuseStep 764579 = 1146869) B1146869
theorem B4074245 : Blo 714321 4074245 := bstep (se 4 (by rfl) ⟨381960, by rfl⟩ : syracuseStep 4074245 = 763921) B763921
theorem B3877859 : Blo 714321 3877859 := bstep (se 1 (by rfl) ⟨2908394, by rfl⟩ : syracuseStep 3877859 = 5816789) B5816789
theorem B1289233 : Blo 714321 1289233 := bstep (se 2 (by rfl) ⟨483462, by rfl⟩ : syracuseStep 1289233 = 966925) B966925
theorem B3058829 : Blo 714321 3058829 := bstep (se 3 (by rfl) ⟨573530, by rfl⟩ : syracuseStep 3058829 = 1147061) B1147061
theorem B2174147 : Blo 714321 2174147 := bstep (se 1 (by rfl) ⟨1630610, by rfl⟩ : syracuseStep 2174147 = 3261221) B3261221
theorem B1813873 : Blo 714321 1813873 := bstep (se 2 (by rfl) ⟨680202, by rfl⟩ : syracuseStep 1813873 = 1360405) B1360405
theorem B2043377 : Blo 714321 2043377 := bstep (se 2 (by rfl) ⟨766266, by rfl⟩ : syracuseStep 2043377 = 1532533) B1532533
theorem B1814147 : Blo 714321 1814147 := bstep (se 1 (by rfl) ⟨1360610, by rfl⟩ : syracuseStep 1814147 = 2721221) B2721221
theorem B2043569 : Blo 714321 2043569 := bstep (se 2 (by rfl) ⟨766338, by rfl⟩ : syracuseStep 2043569 = 1532677) B1532677
theorem B5451461 : Blo 714321 5451461 := bstep (se 4 (by rfl) ⟨511074, by rfl⟩ : syracuseStep 5451461 = 1022149) B1022149
theorem B1224401 : Blo 714321 1224401 := bstep (se 2 (by rfl) ⟨459150, by rfl⟩ : syracuseStep 1224401 = 918301) B918301
theorem B1290019 : Blo 714321 1290019 := bstep (se 1 (by rfl) ⟨967514, by rfl⟩ : syracuseStep 1290019 = 1935029) B1935029
theorem B3878705 : Blo 714321 3878705 := bstep (se 2 (by rfl) ⟨1454514, by rfl⟩ : syracuseStep 3878705 = 2909029) B2909029
theorem B1814339 : Blo 714321 1814339 := bstep (se 1 (by rfl) ⟨1360754, by rfl⟩ : syracuseStep 1814339 = 2721509) B2721509
theorem B3878725 : Blo 714321 3878725 := bstep (se 4 (by rfl) ⟨363630, by rfl⟩ : syracuseStep 3878725 = 727261) B727261
theorem B1224641 : Blo 714321 1224641 := bstep (se 2 (by rfl) ⟨459240, by rfl⟩ : syracuseStep 1224641 = 918481) B918481
theorem B6697073 : Blo 714321 6697073 := bstep (se 2 (by rfl) ⟨2511402, by rfl⟩ : syracuseStep 6697073 = 5022805) B5022805
theorem B3616973 : Blo 714321 3616973 := bstep (se 3 (by rfl) ⟨678182, by rfl⟩ : syracuseStep 3616973 = 1356365) B1356365
theorem B1290659 : Blo 714321 1290659 := bstep (se 1 (by rfl) ⟨967994, by rfl⟩ : syracuseStep 1290659 = 1935989) B1935989
theorem B1716689 : Blo 714321 1716689 := bstep (se 2 (by rfl) ⟨643758, by rfl⟩ : syracuseStep 1716689 = 1287517) B1287517
theorem B1356259 : Blo 714321 1356259 := bstep (se 1 (by rfl) ⟨1017194, by rfl⟩ : syracuseStep 1356259 = 2034389) B2034389
theorem B1290833 : Blo 714321 1290833 := bstep (se 2 (by rfl) ⟨484062, by rfl⟩ : syracuseStep 1290833 = 968125) B968125
theorem B1356419 : Blo 714321 1356419 := bstep (se 1 (by rfl) ⟨1017314, by rfl⟩ : syracuseStep 1356419 = 2034629) B2034629
theorem B766595 : Blo 714321 766595 := bstep (se 1 (by rfl) ⟨574946, by rfl⟩ : syracuseStep 766595 = 1149893) B1149893
theorem B2044561 : Blo 714321 2044561 := bstep (se 2 (by rfl) ⟨766710, by rfl⟩ : syracuseStep 2044561 = 1533421) B1533421
theorem B1815281 : Blo 714321 1815281 := bstep (se 2 (by rfl) ⟨680730, by rfl⟩ : syracuseStep 1815281 = 1361461) B1361461
theorem B1815331 : Blo 714321 1815331 := bstep (se 1 (by rfl) ⟨1361498, by rfl⟩ : syracuseStep 1815331 = 2722997) B2722997
theorem B1291121 : Blo 714321 1291121 := bstep (se 2 (by rfl) ⟨484170, by rfl⟩ : syracuseStep 1291121 = 968341) B968341
theorem B2044835 : Blo 714321 2044835 := bstep (se 1 (by rfl) ⟨1533626, by rfl⟩ : syracuseStep 2044835 = 3067253) B3067253
theorem B1815473 : Blo 714321 1815473 := bstep (se 2 (by rfl) ⟨680802, by rfl⟩ : syracuseStep 1815473 = 1361605) B1361605
theorem B4600901 : Blo 714321 4600901 := bstep (se 4 (by rfl) ⟨431334, by rfl⟩ : syracuseStep 4600901 = 862669) B862669
theorem B2045027 : Blo 714321 2045027 := bstep (se 1 (by rfl) ⟨1533770, by rfl⟩ : syracuseStep 2045027 = 3067541) B3067541
theorem B1225859 : Blo 714321 1225859 := bstep (se 1 (by rfl) ⟨919394, by rfl⟩ : syracuseStep 1225859 = 1838789) B1838789
theorem B1455235 : Blo 714321 1455235 := bstep (se 1 (by rfl) ⟨1091426, by rfl⟩ : syracuseStep 1455235 = 2182853) B2182853
theorem B1357489 : Blo 714321 1357489 := bstep (se 2 (by rfl) ⟨509058, by rfl⟩ : syracuseStep 1357489 = 1018117) B1018117
theorem B11024099 : Blo 714321 11024099 := bstep (se 1 (by rfl) ⟨8268074, by rfl⟩ : syracuseStep 11024099 = 16536149) B16536149
theorem B3880781 : Blo 714321 3880781 := bstep (se 3 (by rfl) ⟨727646, by rfl⟩ : syracuseStep 3880781 = 1455293) B1455293
theorem B1816465 : Blo 714321 1816465 := bstep (se 2 (by rfl) ⟨681174, by rfl⟩ : syracuseStep 1816465 = 1362349) B1362349
theorem B1063057 : Blo 714321 1063057 := bstep (se 2 (by rfl) ⟨398646, by rfl⟩ : syracuseStep 1063057 = 797293) B797293
theorem B1816739 : Blo 714321 1816739 := bstep (se 1 (by rfl) ⟨1362554, by rfl⟩ : syracuseStep 1816739 = 2725109) B2725109
theorem B3061937 : Blo 714321 3061937 := bstep (se 2 (by rfl) ⟨1148226, by rfl⟩ : syracuseStep 3061937 = 2296453) B2296453
theorem B1816931 : Blo 714321 1816931 := bstep (se 1 (by rfl) ⟨1362698, by rfl⟩ : syracuseStep 1816931 = 2725397) B2725397
theorem B1292707 : Blo 714321 1292707 := bstep (se 1 (by rfl) ⟨969530, by rfl⟩ : syracuseStep 1292707 = 1939061) B1939061
theorem B1358545 : Blo 714321 1358545 := bstep (se 2 (by rfl) ⟨509454, by rfl⟩ : syracuseStep 1358545 = 1018909) B1018909
theorem B736259 : Blo 714321 736259 := bstep (se 1 (by rfl) ⟨552194, by rfl⟩ : syracuseStep 736259 = 1104389) B1104389
theorem B3619889 : Blo 714321 3619889 := bstep (se 2 (by rfl) ⟨1357458, by rfl⟩ : syracuseStep 3619889 = 2714917) B2714917
theorem B1358947 : Blo 714321 1358947 := bstep (se 1 (by rfl) ⟨1019210, by rfl⟩ : syracuseStep 1358947 = 2038421) B2038421
theorem B1358993 : Blo 714321 1358993 := bstep (se 2 (by rfl) ⟨509622, by rfl⟩ : syracuseStep 1358993 = 1019245) B1019245
theorem B1817873 : Blo 714321 1817873 := bstep (se 2 (by rfl) ⟨681702, by rfl⟩ : syracuseStep 1817873 = 1363405) B1363405
theorem B3882275 : Blo 714321 3882275 := bstep (se 1 (by rfl) ⟨2911706, by rfl⟩ : syracuseStep 3882275 = 5823413) B5823413
theorem B1817923 : Blo 714321 1817923 := bstep (se 1 (by rfl) ⟨1363442, by rfl⟩ : syracuseStep 1817923 = 2726885) B2726885
theorem B966001 : Blo 714321 966001 := bstep (se 2 (by rfl) ⟨362250, by rfl⟩ : syracuseStep 966001 = 724501) B724501
theorem B3063203 : Blo 714321 3063203 := bstep (se 1 (by rfl) ⟨2297402, by rfl⟩ : syracuseStep 3063203 = 4594805) B4594805
theorem B1359281 : Blo 714321 1359281 := bstep (se 2 (by rfl) ⟨509730, by rfl⟩ : syracuseStep 1359281 = 1019461) B1019461
theorem B1293745 : Blo 714321 1293745 := bstep (se 2 (by rfl) ⟨485154, by rfl⟩ : syracuseStep 1293745 = 970309) B970309
theorem B1818065 : Blo 714321 1818065 := bstep (se 2 (by rfl) ⟨681774, by rfl⟩ : syracuseStep 1818065 = 1363549) B1363549
theorem B2178659 : Blo 714321 2178659 := bstep (se 1 (by rfl) ⟨1633994, by rfl⟩ : syracuseStep 2178659 = 3267989) B3267989
theorem B966449 : Blo 714321 966449 := bstep (se 2 (by rfl) ⟨362418, by rfl⟩ : syracuseStep 966449 = 724837) B724837
theorem B1261363 : Blo 714321 1261363 := bstep (se 1 (by rfl) ⟨946022, by rfl⟩ : syracuseStep 1261363 = 1892045) B1892045
theorem B1163089 : Blo 714321 1163089 := bstep (se 2 (by rfl) ⟨436158, by rfl⟩ : syracuseStep 1163089 = 872317) B872317
theorem B1360003 : Blo 714321 1360003 := bstep (se 1 (by rfl) ⟨1020002, by rfl⟩ : syracuseStep 1360003 = 2040005) B2040005
theorem B4145357 : Blo 714321 4145357 := bstep (se 3 (by rfl) ⟨777254, by rfl⟩ : syracuseStep 4145357 = 1554509) B1554509
theorem B5161229 : Blo 714321 5161229 := bstep (se 3 (by rfl) ⟨967730, by rfl⟩ : syracuseStep 5161229 = 1935461) B1935461
theorem B966979 : Blo 714321 966979 := bstep (se 1 (by rfl) ⟨725234, by rfl⟩ : syracuseStep 966979 = 1450469) B1450469
theorem B967043 : Blo 714321 967043 := bstep (se 1 (by rfl) ⟨725282, by rfl⟩ : syracuseStep 967043 = 1450565) B1450565
theorem B4080077 : Blo 714321 4080077 := bstep (se 3 (by rfl) ⟨765014, by rfl⟩ : syracuseStep 4080077 = 1530029) B1530029
theorem B3621347 : Blo 714321 3621347 := bstep (se 1 (by rfl) ⟨2716010, by rfl⟩ : syracuseStep 3621347 = 5432021) B5432021
theorem B5161457 : Blo 714321 5161457 := bstep (se 2 (by rfl) ⟨1935546, by rfl⟩ : syracuseStep 5161457 = 3871093) B3871093
theorem B15483413 : Blo 714321 15483413 := bstep (se 6 (by rfl) ⟨362892, by rfl⟩ : syracuseStep 15483413 = 725785) B725785
theorem B1360451 : Blo 714321 1360451 := bstep (se 1 (by rfl) ⟨1020338, by rfl⟩ : syracuseStep 1360451 = 2040677) B2040677
theorem B1360739 : Blo 714321 1360739 := bstep (se 1 (by rfl) ⟨1020554, by rfl⟩ : syracuseStep 1360739 = 2041109) B2041109
theorem B803731 : Blo 714321 803731 := bstep (se 1 (by rfl) ⟨602798, by rfl⟩ : syracuseStep 803731 = 1205597) B1205597
theorem B2180081 : Blo 714321 2180081 := bstep (se 2 (by rfl) ⟨817530, by rfl⟩ : syracuseStep 2180081 = 1635061) B1635061
theorem B803875 : Blo 714321 803875 := bstep (se 1 (by rfl) ⟨602906, by rfl⟩ : syracuseStep 803875 = 1205813) B1205813
theorem B804019 : Blo 714321 804019 := bstep (se 1 (by rfl) ⟨603014, by rfl⟩ : syracuseStep 804019 = 1206029) B1206029
theorem B5817541 : Blo 714321 5817541 := bstep (se 4 (by rfl) ⟨545394, by rfl⟩ : syracuseStep 5817541 = 1090789) B1090789
theorem B3622157 : Blo 714321 3622157 := bstep (se 3 (by rfl) ⟨679154, by rfl⟩ : syracuseStep 3622157 = 1358309) B1358309
theorem B1033489 : Blo 714321 1033489 := bstep (se 2 (by rfl) ⟨387558, by rfl⟩ : syracuseStep 1033489 = 775117) B775117
theorem B804163 : Blo 714321 804163 := bstep (se 1 (by rfl) ⟨603122, by rfl⟩ : syracuseStep 804163 = 1206245) B1206245
theorem B804307 : Blo 714321 804307 := bstep (se 1 (by rfl) ⟨603230, by rfl⟩ : syracuseStep 804307 = 1206461) B1206461
theorem B5817827 : Blo 714321 5817827 := bstep (se 1 (by rfl) ⟨4363370, by rfl⟩ : syracuseStep 5817827 = 8726741) B8726741
theorem B804451 : Blo 714321 804451 := bstep (se 1 (by rfl) ⟨603338, by rfl⟩ : syracuseStep 804451 = 1206677) B1206677
theorem B804595 : Blo 714321 804595 := bstep (se 1 (by rfl) ⟨603446, by rfl⟩ : syracuseStep 804595 = 1206893) B1206893
theorem B1361681 : Blo 714321 1361681 := bstep (se 2 (by rfl) ⟨510630, by rfl⟩ : syracuseStep 1361681 = 1021261) B1021261
theorem B66209557 : Blo 714321 66209557 := bstep (se 6 (by rfl) ⟨1551786, by rfl⟩ : syracuseStep 66209557 = 3103573) B3103573
theorem B804739 : Blo 714321 804739 := bstep (se 1 (by rfl) ⟨603554, by rfl⟩ : syracuseStep 804739 = 1207109) B1207109
theorem B804883 : Blo 714321 804883 := bstep (se 1 (by rfl) ⟨603662, by rfl⟩ : syracuseStep 804883 = 1207325) B1207325
theorem B805027 : Blo 714321 805027 := bstep (se 1 (by rfl) ⟨603770, by rfl⟩ : syracuseStep 805027 = 1207541) B1207541
theorem B69552341 : Blo 714321 69552341 := bstep (se 7 (by rfl) ⟨815066, by rfl⟩ : syracuseStep 69552341 = 1630133) B1630133
theorem B805171 : Blo 714321 805171 := bstep (se 1 (by rfl) ⟨603878, by rfl⟩ : syracuseStep 805171 = 1207757) B1207757
theorem B2410883 : Blo 714321 2410883 := bstep (se 1 (by rfl) ⟨1808162, by rfl⟩ : syracuseStep 2410883 = 3616325) B3616325
theorem B805315 : Blo 714321 805315 := bstep (se 1 (by rfl) ⟨603986, by rfl⟩ : syracuseStep 805315 = 1207973) B1207973
theorem B1165763 : Blo 714321 1165763 := bstep (se 1 (by rfl) ⟨874322, by rfl⟩ : syracuseStep 1165763 = 1748645) B1748645
theorem B969185 : Blo 714321 969185 := bstep (se 2 (by rfl) ⟨363444, by rfl⟩ : syracuseStep 969185 = 726889) B726889
theorem B1526321 : Blo 714321 1526321 := bstep (se 2 (by rfl) ⟨572370, by rfl⟩ : syracuseStep 1526321 = 1144741) B1144741
theorem B1526339 : Blo 714321 1526339 := bstep (se 1 (by rfl) ⟨1144754, by rfl⟩ : syracuseStep 1526339 = 2289509) B2289509
theorem B805459 : Blo 714321 805459 := bstep (se 1 (by rfl) ⟨604094, by rfl⟩ : syracuseStep 805459 = 1208189) B1208189
theorem B4082309 : Blo 714321 4082309 := bstep (se 4 (by rfl) ⟨382716, by rfl⟩ : syracuseStep 4082309 = 765433) B765433
theorem B2411153 : Blo 714321 2411153 := bstep (se 2 (by rfl) ⟨904182, by rfl⟩ : syracuseStep 2411153 = 1808365) B1808365
theorem B1362577 : Blo 714321 1362577 := bstep (se 2 (by rfl) ⟨510966, by rfl⟩ : syracuseStep 1362577 = 1021933) B1021933
theorem B805603 : Blo 714321 805603 := bstep (se 1 (by rfl) ⟨604202, by rfl⟩ : syracuseStep 805603 = 1208405) B1208405
theorem B1362737 : Blo 714321 1362737 := bstep (se 2 (by rfl) ⟨511026, by rfl⟩ : syracuseStep 1362737 = 1022053) B1022053
theorem B805747 : Blo 714321 805747 := bstep (se 1 (by rfl) ⟨604310, by rfl⟩ : syracuseStep 805747 = 1208621) B1208621
theorem B969617 : Blo 714321 969617 := bstep (se 2 (by rfl) ⟨363606, by rfl⟩ : syracuseStep 969617 = 727213) B727213
theorem B8145845 : Blo 714321 8145845 := bstep (se 5 (by rfl) ⟨381836, by rfl⟩ : syracuseStep 8145845 = 763673) B763673
theorem B805891 : Blo 714321 805891 := bstep (se 1 (by rfl) ⟨604418, by rfl⟩ : syracuseStep 805891 = 1208837) B1208837
theorem B5426189 : Blo 714321 5426189 := bstep (se 3 (by rfl) ⟨1017410, by rfl⟩ : syracuseStep 5426189 = 2034821) B2034821
theorem B3066893 : Blo 714321 3066893 := bstep (se 3 (by rfl) ⟨575042, by rfl⟩ : syracuseStep 3066893 = 1150085) B1150085
theorem B969779 : Blo 714321 969779 := bstep (se 1 (by rfl) ⟨727334, by rfl⟩ : syracuseStep 969779 = 1454669) B1454669
theorem B806035 : Blo 714321 806035 := bstep (se 1 (by rfl) ⟨604526, by rfl⟩ : syracuseStep 806035 = 1209053) B1209053
theorem B2411693 : Blo 714321 2411693 := bstep (se 3 (by rfl) ⟨452192, by rfl⟩ : syracuseStep 2411693 = 904385) B904385
theorem B2477233 : Blo 714321 2477233 := bstep (se 2 (by rfl) ⟨928962, by rfl⟩ : syracuseStep 2477233 = 1857925) B1857925
theorem B1363139 : Blo 714321 1363139 := bstep (se 1 (by rfl) ⟨1022354, by rfl⟩ : syracuseStep 1363139 = 2044709) B2044709
theorem B2411747 : Blo 714321 2411747 := bstep (se 1 (by rfl) ⟨1808810, by rfl⟩ : syracuseStep 2411747 = 3617621) B3617621
theorem B806179 : Blo 714321 806179 := bstep (se 1 (by rfl) ⟨604634, by rfl⟩ : syracuseStep 806179 = 1209269) B1209269
theorem B4082993 : Blo 714321 4082993 := bstep (se 2 (by rfl) ⟨1531122, by rfl⟩ : syracuseStep 4082993 = 3062245) B3062245
theorem B904547 : Blo 714321 904547 := bstep (se 1 (by rfl) ⟨678410, by rfl⟩ : syracuseStep 904547 = 1356821) B1356821
theorem B3263921 : Blo 714321 3263921 := bstep (se 2 (by rfl) ⟨1223970, by rfl⟩ : syracuseStep 3263921 = 2447941) B2447941
theorem B806323 : Blo 714321 806323 := bstep (se 1 (by rfl) ⟨604742, by rfl⟩ : syracuseStep 806323 = 1209485) B1209485
theorem B2412017 : Blo 714321 2412017 := bstep (se 2 (by rfl) ⟨904506, by rfl⟩ : syracuseStep 2412017 = 1809013) B1809013
theorem B806467 : Blo 714321 806467 := bstep (se 1 (by rfl) ⟨604850, by rfl⟩ : syracuseStep 806467 = 1209701) B1209701
theorem B970417 : Blo 714321 970417 := bstep (se 2 (by rfl) ⟨363906, by rfl⟩ : syracuseStep 970417 = 727813) B727813
theorem B806611 : Blo 714321 806611 := bstep (se 1 (by rfl) ⟨604958, by rfl⟩ : syracuseStep 806611 = 1209917) B1209917
theorem B1527569 : Blo 714321 1527569 := bstep (se 2 (by rfl) ⟨572838, by rfl⟩ : syracuseStep 1527569 = 1145677) B1145677
theorem B806755 : Blo 714321 806755 := bstep (se 1 (by rfl) ⟨605066, by rfl⟩ : syracuseStep 806755 = 1210133) B1210133
theorem B774067 : Blo 714321 774067 := bstep (se 1 (by rfl) ⟨580550, by rfl⟩ : syracuseStep 774067 = 1161101) B1161101
theorem B806899 : Blo 714321 806899 := bstep (se 1 (by rfl) ⟨605174, by rfl⟩ : syracuseStep 806899 = 1210349) B1210349
theorem B2412557 : Blo 714321 2412557 := bstep (se 3 (by rfl) ⟨452354, by rfl⟩ : syracuseStep 2412557 = 904709) B904709
theorem B905251 : Blo 714321 905251 := bstep (se 1 (by rfl) ⟨678938, by rfl⟩ : syracuseStep 905251 = 1357877) B1357877
theorem B2412611 : Blo 714321 2412611 := bstep (se 1 (by rfl) ⟨1809458, by rfl⟩ : syracuseStep 2412611 = 3618917) B3618917
theorem B3625073 : Blo 714321 3625073 := bstep (se 2 (by rfl) ⟨1359402, by rfl⟩ : syracuseStep 3625073 = 2718805) B2718805
theorem B905347 : Blo 714321 905347 := bstep (se 1 (by rfl) ⟨679010, by rfl⟩ : syracuseStep 905347 = 1358021) B1358021
theorem B807043 : Blo 714321 807043 := bstep (se 1 (by rfl) ⟨605282, by rfl⟩ : syracuseStep 807043 = 1210565) B1210565
theorem B807187 : Blo 714321 807187 := bstep (se 1 (by rfl) ⟨605390, by rfl⟩ : syracuseStep 807187 = 1210781) B1210781
theorem B2412881 : Blo 714321 2412881 := bstep (se 2 (by rfl) ⟨904830, by rfl⟩ : syracuseStep 2412881 = 1809661) B1809661
theorem B2183537 : Blo 714321 2183537 := bstep (se 2 (by rfl) ⟨818826, by rfl⟩ : syracuseStep 2183537 = 1637653) B1637653
theorem B807331 : Blo 714321 807331 := bstep (se 1 (by rfl) ⟨605498, by rfl⟩ : syracuseStep 807331 = 1210997) B1210997
theorem B807475 : Blo 714321 807475 := bstep (se 1 (by rfl) ⟨605606, by rfl⟩ : syracuseStep 807475 = 1211213) B1211213
theorem B905843 : Blo 714321 905843 := bstep (se 1 (by rfl) ⟨679382, by rfl⟩ : syracuseStep 905843 = 1358765) B1358765
theorem B807619 : Blo 714321 807619 := bstep (se 1 (by rfl) ⟨605714, by rfl⟩ : syracuseStep 807619 = 1211429) B1211429
theorem B4084451 : Blo 714321 4084451 := bstep (se 1 (by rfl) ⟨3063338, by rfl⟩ : syracuseStep 4084451 = 6126677) B6126677
theorem B807763 : Blo 714321 807763 := bstep (se 1 (by rfl) ⟨605822, by rfl⟩ : syracuseStep 807763 = 1211645) B1211645
theorem B2413421 : Blo 714321 2413421 := bstep (se 3 (by rfl) ⟨452516, by rfl⟩ : syracuseStep 2413421 = 905033) B905033
theorem B2413475 : Blo 714321 2413475 := bstep (se 1 (by rfl) ⟨1810106, by rfl⟩ : syracuseStep 2413475 = 3620213) B3620213
theorem B807907 : Blo 714321 807907 := bstep (se 1 (by rfl) ⟨605930, by rfl⟩ : syracuseStep 807907 = 1211861) B1211861
theorem B808051 : Blo 714321 808051 := bstep (se 1 (by rfl) ⟨606038, by rfl⟩ : syracuseStep 808051 = 1212077) B1212077
theorem B2413745 : Blo 714321 2413745 := bstep (se 2 (by rfl) ⟨905154, by rfl⟩ : syracuseStep 2413745 = 1810309) B1810309
theorem B6870257 : Blo 714321 6870257 := bstep (se 2 (by rfl) ⟨2576346, by rfl⟩ : syracuseStep 6870257 = 5152693) B5152693
theorem B1529123 : Blo 714321 1529123 := bstep (se 1 (by rfl) ⟨1146842, by rfl⟩ : syracuseStep 1529123 = 2293685) B2293685
theorem B906547 : Blo 714321 906547 := bstep (se 1 (by rfl) ⟨679910, by rfl⟩ : syracuseStep 906547 = 1359821) B1359821
theorem B2446733 : Blo 714321 2446733 := bstep (se 3 (by rfl) ⟨458762, by rfl⟩ : syracuseStep 2446733 = 917525) B917525
theorem B906643 : Blo 714321 906643 := bstep (se 1 (by rfl) ⟨679982, by rfl⟩ : syracuseStep 906643 = 1359965) B1359965
theorem B3626531 : Blo 714321 3626531 := bstep (se 1 (by rfl) ⟨2719898, by rfl⟩ : syracuseStep 3626531 = 5439797) B5439797
theorem B2414285 : Blo 714321 2414285 := bstep (se 3 (by rfl) ⟨452678, by rfl⟩ : syracuseStep 2414285 = 905357) B905357
theorem B2414339 : Blo 714321 2414339 := bstep (se 1 (by rfl) ⟨1810754, by rfl⟩ : syracuseStep 2414339 = 3621509) B3621509
theorem B5429105 : Blo 714321 5429105 := bstep (se 2 (by rfl) ⟨2035914, by rfl⟩ : syracuseStep 5429105 = 4071829) B4071829
theorem B907139 : Blo 714321 907139 := bstep (se 1 (by rfl) ⟨680354, by rfl⟩ : syracuseStep 907139 = 1360709) B1360709
theorem B35739589 : Blo 714321 35739589 := bstep (se 4 (by rfl) ⟨3350586, by rfl⟩ : syracuseStep 35739589 = 6701173) B6701173
theorem B10344419 : Blo 714321 10344419 := bstep (se 1 (by rfl) ⟨7758314, by rfl⟩ : syracuseStep 10344419 = 15516629) B15516629
theorem B2414609 : Blo 714321 2414609 := bstep (se 2 (by rfl) ⟨905478, by rfl⟩ : syracuseStep 2414609 = 1810957) B1810957
theorem B3627341 : Blo 714321 3627341 := bstep (se 3 (by rfl) ⟨680126, by rfl⟩ : syracuseStep 3627341 = 1360253) B1360253
theorem B1071491 : Blo 714321 1071491 := bstep (se 1 (by rfl) ⟨803618, by rfl⟩ : syracuseStep 1071491 = 1607237) B1607237
theorem B2447747 : Blo 714321 2447747 := bstep (se 1 (by rfl) ⟨1835810, by rfl⟩ : syracuseStep 2447747 = 3671621) B3671621
theorem B1071521 : Blo 714321 1071521 := bstep (se 2 (by rfl) ⟨401820, by rfl⟩ : syracuseStep 1071521 = 803641) B803641
theorem B1071539 : Blo 714321 1071539 := bstep (se 1 (by rfl) ⟨803654, by rfl⟩ : syracuseStep 1071539 = 1607309) B1607309
theorem B1071569 : Blo 714321 1071569 := bstep (se 2 (by rfl) ⟨401838, by rfl⟩ : syracuseStep 1071569 = 803677) B803677
theorem B1071587 : Blo 714321 1071587 := bstep (se 1 (by rfl) ⟨803690, by rfl⟩ : syracuseStep 1071587 = 1607381) B1607381
theorem B1071617 : Blo 714321 1071617 := bstep (se 2 (by rfl) ⟨401856, by rfl⟩ : syracuseStep 1071617 = 803713) B803713
theorem B1071635 : Blo 714321 1071635 := bstep (se 1 (by rfl) ⟨803726, by rfl⟩ : syracuseStep 1071635 = 1607453) B1607453
theorem B2415149 : Blo 714321 2415149 := bstep (se 3 (by rfl) ⟨452840, by rfl⟩ : syracuseStep 2415149 = 905681) B905681
theorem B1071665 : Blo 714321 1071665 := bstep (se 2 (by rfl) ⟨401874, by rfl⟩ : syracuseStep 1071665 = 803749) B803749
theorem B1071683 : Blo 714321 1071683 := bstep (se 1 (by rfl) ⟨803762, by rfl⟩ : syracuseStep 1071683 = 1607525) B1607525
theorem B907843 : Blo 714321 907843 := bstep (se 1 (by rfl) ⟨680882, by rfl⟩ : syracuseStep 907843 = 1361765) B1361765
theorem B1071713 : Blo 714321 1071713 := bstep (se 2 (by rfl) ⟨401892, by rfl⟩ : syracuseStep 1071713 = 803785) B803785
theorem B2415203 : Blo 714321 2415203 := bstep (se 1 (by rfl) ⟨1811402, by rfl⟩ : syracuseStep 2415203 = 3622805) B3622805
theorem B1071731 : Blo 714321 1071731 := bstep (se 1 (by rfl) ⟨803798, by rfl⟩ : syracuseStep 1071731 = 1607597) B1607597
theorem B4414085 : Blo 714321 4414085 := bstep (se 4 (by rfl) ⟨413820, by rfl⟩ : syracuseStep 4414085 = 827641) B827641
theorem B1071761 : Blo 714321 1071761 := bstep (se 2 (by rfl) ⟨401910, by rfl⟩ : syracuseStep 1071761 = 803821) B803821
theorem B1071779 : Blo 714321 1071779 := bstep (se 1 (by rfl) ⟨803834, by rfl⟩ : syracuseStep 1071779 = 1607669) B1607669
theorem B907939 : Blo 714321 907939 := bstep (se 1 (by rfl) ⟨680954, by rfl⟩ : syracuseStep 907939 = 1361909) B1361909
theorem B1071809 : Blo 714321 1071809 := bstep (se 2 (by rfl) ⟨401928, by rfl⟩ : syracuseStep 1071809 = 803857) B803857
theorem B1071827 : Blo 714321 1071827 := bstep (se 1 (by rfl) ⟨803870, by rfl⟩ : syracuseStep 1071827 = 1607741) B1607741
theorem B1071857 : Blo 714321 1071857 := bstep (se 2 (by rfl) ⟨401946, by rfl⟩ : syracuseStep 1071857 = 803893) B803893
theorem B1071875 : Blo 714321 1071875 := bstep (se 1 (by rfl) ⟨803906, by rfl⟩ : syracuseStep 1071875 = 1607813) B1607813
theorem B1071905 : Blo 714321 1071905 := bstep (se 2 (by rfl) ⟨401964, by rfl⟩ : syracuseStep 1071905 = 803929) B803929
theorem B1071923 : Blo 714321 1071923 := bstep (se 1 (by rfl) ⟨803942, by rfl⟩ : syracuseStep 1071923 = 1607885) B1607885
theorem B1071953 : Blo 714321 1071953 := bstep (se 2 (by rfl) ⟨401982, by rfl⟩ : syracuseStep 1071953 = 803965) B803965
theorem B1071971 : Blo 714321 1071971 := bstep (se 1 (by rfl) ⟨803978, by rfl⟩ : syracuseStep 1071971 = 1607957) B1607957
theorem B2415473 : Blo 714321 2415473 := bstep (se 2 (by rfl) ⟨905802, by rfl⟩ : syracuseStep 2415473 = 1811605) B1811605
theorem B1072001 : Blo 714321 1072001 := bstep (se 2 (by rfl) ⟨402000, by rfl⟩ : syracuseStep 1072001 = 804001) B804001
theorem B1072019 : Blo 714321 1072019 := bstep (se 1 (by rfl) ⟨804014, by rfl⟩ : syracuseStep 1072019 = 1608029) B1608029
theorem B1072049 : Blo 714321 1072049 := bstep (se 2 (by rfl) ⟨402018, by rfl⟩ : syracuseStep 1072049 = 804037) B804037
theorem B1072067 : Blo 714321 1072067 := bstep (se 1 (by rfl) ⟨804050, by rfl⟩ : syracuseStep 1072067 = 1608101) B1608101
theorem B1072097 : Blo 714321 1072097 := bstep (se 2 (by rfl) ⟨402036, by rfl⟩ : syracuseStep 1072097 = 804073) B804073
theorem B1072115 : Blo 714321 1072115 := bstep (se 1 (by rfl) ⟨804086, by rfl⟩ : syracuseStep 1072115 = 1608173) B1608173
theorem B1072145 : Blo 714321 1072145 := bstep (se 2 (by rfl) ⟨402054, by rfl⟩ : syracuseStep 1072145 = 804109) B804109
theorem B1072163 : Blo 714321 1072163 := bstep (se 1 (by rfl) ⟨804122, by rfl⟩ : syracuseStep 1072163 = 1608245) B1608245
theorem B1072193 : Blo 714321 1072193 := bstep (se 2 (by rfl) ⟨402072, by rfl⟩ : syracuseStep 1072193 = 804145) B804145
theorem B1072211 : Blo 714321 1072211 := bstep (se 1 (by rfl) ⟨804158, by rfl⟩ : syracuseStep 1072211 = 1608317) B1608317
theorem B1072241 : Blo 714321 1072241 := bstep (se 2 (by rfl) ⟨402090, by rfl⟩ : syracuseStep 1072241 = 804181) B804181
theorem B1072259 : Blo 714321 1072259 := bstep (se 1 (by rfl) ⟨804194, by rfl⟩ : syracuseStep 1072259 = 1608389) B1608389
theorem B908435 : Blo 714321 908435 := bstep (se 1 (by rfl) ⟨681326, by rfl⟩ : syracuseStep 908435 = 1362653) B1362653
theorem B1072289 : Blo 714321 1072289 := bstep (se 2 (by rfl) ⟨402108, by rfl⟩ : syracuseStep 1072289 = 804217) B804217
theorem B1072307 : Blo 714321 1072307 := bstep (se 1 (by rfl) ⟨804230, by rfl⟩ : syracuseStep 1072307 = 1608461) B1608461
theorem B1072337 : Blo 714321 1072337 := bstep (se 2 (by rfl) ⟨402126, by rfl⟩ : syracuseStep 1072337 = 804253) B804253
theorem B1072355 : Blo 714321 1072355 := bstep (se 1 (by rfl) ⟨804266, by rfl⟩ : syracuseStep 1072355 = 1608533) B1608533
theorem B1072385 : Blo 714321 1072385 := bstep (se 2 (by rfl) ⟨402144, by rfl⟩ : syracuseStep 1072385 = 804289) B804289
theorem B1072403 : Blo 714321 1072403 := bstep (se 1 (by rfl) ⟨804302, by rfl⟩ : syracuseStep 1072403 = 1608605) B1608605
theorem B1072433 : Blo 714321 1072433 := bstep (se 2 (by rfl) ⟨402162, by rfl⟩ : syracuseStep 1072433 = 804325) B804325
theorem B1072451 : Blo 714321 1072451 := bstep (se 1 (by rfl) ⟨804338, by rfl⟩ : syracuseStep 1072451 = 1608677) B1608677
theorem B1072481 : Blo 714321 1072481 := bstep (se 2 (by rfl) ⟨402180, by rfl⟩ : syracuseStep 1072481 = 804361) B804361
theorem B1072499 : Blo 714321 1072499 := bstep (se 1 (by rfl) ⟨804374, by rfl⟩ : syracuseStep 1072499 = 1608749) B1608749
theorem B2416013 : Blo 714321 2416013 := bstep (se 3 (by rfl) ⟨453002, by rfl⟩ : syracuseStep 2416013 = 906005) B906005
theorem B9330061 : Blo 714321 9330061 := bstep (se 3 (by rfl) ⟨1749386, by rfl⟩ : syracuseStep 9330061 = 3498773) B3498773
theorem B1072529 : Blo 714321 1072529 := bstep (se 2 (by rfl) ⟨402198, by rfl⟩ : syracuseStep 1072529 = 804397) B804397
theorem B1072547 : Blo 714321 1072547 := bstep (se 1 (by rfl) ⟨804410, by rfl⟩ : syracuseStep 1072547 = 1608821) B1608821
theorem B1072577 : Blo 714321 1072577 := bstep (se 2 (by rfl) ⟨402216, by rfl⟩ : syracuseStep 1072577 = 804433) B804433
theorem B2416067 : Blo 714321 2416067 := bstep (se 1 (by rfl) ⟨1812050, by rfl⟩ : syracuseStep 2416067 = 3624101) B3624101
theorem B1531345 : Blo 714321 1531345 := bstep (se 2 (by rfl) ⟨574254, by rfl⟩ : syracuseStep 1531345 = 1148509) B1148509
theorem B1072595 : Blo 714321 1072595 := bstep (se 1 (by rfl) ⟨804446, by rfl⟩ : syracuseStep 1072595 = 1608893) B1608893
theorem B1072625 : Blo 714321 1072625 := bstep (se 2 (by rfl) ⟨402234, by rfl⟩ : syracuseStep 1072625 = 804469) B804469
theorem B1072643 : Blo 714321 1072643 := bstep (se 1 (by rfl) ⟨804482, by rfl⟩ : syracuseStep 1072643 = 1608965) B1608965
theorem B1072673 : Blo 714321 1072673 := bstep (se 2 (by rfl) ⟨402252, by rfl⟩ : syracuseStep 1072673 = 804505) B804505
theorem B1072691 : Blo 714321 1072691 := bstep (se 1 (by rfl) ⟨804518, by rfl⟩ : syracuseStep 1072691 = 1609037) B1609037
theorem B5103173 : Blo 714321 5103173 := bstep (se 4 (by rfl) ⟨478422, by rfl⟩ : syracuseStep 5103173 = 956845) B956845
theorem B1072721 : Blo 714321 1072721 := bstep (se 2 (by rfl) ⟨402270, by rfl⟩ : syracuseStep 1072721 = 804541) B804541
theorem B1072739 : Blo 714321 1072739 := bstep (se 1 (by rfl) ⟨804554, by rfl⟩ : syracuseStep 1072739 = 1609109) B1609109
theorem B1072769 : Blo 714321 1072769 := bstep (se 2 (by rfl) ⟨402288, by rfl⟩ : syracuseStep 1072769 = 804577) B804577
theorem B1072787 : Blo 714321 1072787 := bstep (se 1 (by rfl) ⟨804590, by rfl⟩ : syracuseStep 1072787 = 1609181) B1609181
theorem B1072817 : Blo 714321 1072817 := bstep (se 2 (by rfl) ⟨402306, by rfl⟩ : syracuseStep 1072817 = 804613) B804613
theorem B1072835 : Blo 714321 1072835 := bstep (se 1 (by rfl) ⟨804626, by rfl⟩ : syracuseStep 1072835 = 1609253) B1609253
theorem B2416337 : Blo 714321 2416337 := bstep (se 2 (by rfl) ⟨906126, by rfl⟩ : syracuseStep 2416337 = 1812253) B1812253
theorem B1072865 : Blo 714321 1072865 := bstep (se 2 (by rfl) ⟨402324, by rfl⟩ : syracuseStep 1072865 = 804649) B804649
theorem B1072883 : Blo 714321 1072883 := bstep (se 1 (by rfl) ⟨804662, by rfl⟩ : syracuseStep 1072883 = 1609325) B1609325
theorem B1072913 : Blo 714321 1072913 := bstep (se 2 (by rfl) ⟨402342, by rfl⟩ : syracuseStep 1072913 = 804685) B804685
theorem B1072931 : Blo 714321 1072931 := bstep (se 1 (by rfl) ⟨804698, by rfl⟩ : syracuseStep 1072931 = 1609397) B1609397
theorem B1072961 : Blo 714321 1072961 := bstep (se 2 (by rfl) ⟨402360, by rfl⟩ : syracuseStep 1072961 = 804721) B804721
theorem B1072979 : Blo 714321 1072979 := bstep (se 1 (by rfl) ⟨804734, by rfl⟩ : syracuseStep 1072979 = 1609469) B1609469
theorem B1073009 : Blo 714321 1073009 := bstep (se 2 (by rfl) ⟨402378, by rfl⟩ : syracuseStep 1073009 = 804757) B804757
theorem B1073027 : Blo 714321 1073027 := bstep (se 1 (by rfl) ⟨804770, by rfl⟩ : syracuseStep 1073027 = 1609541) B1609541
theorem B4087685 : Blo 714321 4087685 := bstep (se 4 (by rfl) ⟨383220, by rfl⟩ : syracuseStep 4087685 = 766441) B766441
theorem B1073057 : Blo 714321 1073057 := bstep (se 2 (by rfl) ⟨402396, by rfl⟩ : syracuseStep 1073057 = 804793) B804793
theorem B1073075 : Blo 714321 1073075 := bstep (se 1 (by rfl) ⟨804806, by rfl⟩ : syracuseStep 1073075 = 1609613) B1609613
theorem B1073105 : Blo 714321 1073105 := bstep (se 2 (by rfl) ⟨402414, by rfl⟩ : syracuseStep 1073105 = 804829) B804829
theorem B1073123 : Blo 714321 1073123 := bstep (se 1 (by rfl) ⟨804842, by rfl⟩ : syracuseStep 1073123 = 1609685) B1609685
theorem B7757795 : Blo 714321 7757795 := bstep (se 1 (by rfl) ⟨5818346, by rfl⟩ : syracuseStep 7757795 = 11636693) B11636693
theorem B1073153 : Blo 714321 1073153 := bstep (se 2 (by rfl) ⟨402432, by rfl⟩ : syracuseStep 1073153 = 804865) B804865
theorem B1073171 : Blo 714321 1073171 := bstep (se 1 (by rfl) ⟨804878, by rfl⟩ : syracuseStep 1073171 = 1609757) B1609757
theorem B1073201 : Blo 714321 1073201 := bstep (se 2 (by rfl) ⟨402450, by rfl⟩ : syracuseStep 1073201 = 804901) B804901
theorem B1073219 : Blo 714321 1073219 := bstep (se 1 (by rfl) ⟨804914, by rfl⟩ : syracuseStep 1073219 = 1609829) B1609829
theorem B1073249 : Blo 714321 1073249 := bstep (se 2 (by rfl) ⟨402468, by rfl⟩ : syracuseStep 1073249 = 804937) B804937
theorem B1073267 : Blo 714321 1073267 := bstep (se 1 (by rfl) ⟨804950, by rfl⟩ : syracuseStep 1073267 = 1609901) B1609901
theorem B1073297 : Blo 714321 1073297 := bstep (se 2 (by rfl) ⟨402486, by rfl⟩ : syracuseStep 1073297 = 804973) B804973
theorem B1073315 : Blo 714321 1073315 := bstep (se 1 (by rfl) ⟨804986, by rfl⟩ : syracuseStep 1073315 = 1609973) B1609973
theorem B1073345 : Blo 714321 1073345 := bstep (se 2 (by rfl) ⟨402504, by rfl⟩ : syracuseStep 1073345 = 805009) B805009
theorem B1073363 : Blo 714321 1073363 := bstep (se 1 (by rfl) ⟨805022, by rfl⟩ : syracuseStep 1073363 = 1610045) B1610045
theorem B2515181 : Blo 714321 2515181 := bstep (se 3 (by rfl) ⟨471596, by rfl⟩ : syracuseStep 2515181 = 943193) B943193
theorem B2416877 : Blo 714321 2416877 := bstep (se 3 (by rfl) ⟨453164, by rfl⟩ : syracuseStep 2416877 = 906329) B906329
theorem B1073393 : Blo 714321 1073393 := bstep (se 2 (by rfl) ⟨402522, by rfl⟩ : syracuseStep 1073393 = 805045) B805045
theorem B1073411 : Blo 714321 1073411 := bstep (se 1 (by rfl) ⟨805058, by rfl⟩ : syracuseStep 1073411 = 1610117) B1610117
theorem B1073441 : Blo 714321 1073441 := bstep (se 2 (by rfl) ⟨402540, by rfl⟩ : syracuseStep 1073441 = 805081) B805081
theorem B2416931 : Blo 714321 2416931 := bstep (se 1 (by rfl) ⟨1812698, by rfl⟩ : syracuseStep 2416931 = 3625397) B3625397
theorem B1073459 : Blo 714321 1073459 := bstep (se 1 (by rfl) ⟨805094, by rfl⟩ : syracuseStep 1073459 = 1610189) B1610189
theorem B4251973 : Blo 714321 4251973 := bstep (se 4 (by rfl) ⟨398622, by rfl⟩ : syracuseStep 4251973 = 797245) B797245
theorem B4088141 : Blo 714321 4088141 := bstep (se 3 (by rfl) ⟨766526, by rfl⟩ : syracuseStep 4088141 = 1533053) B1533053
theorem B1073489 : Blo 714321 1073489 := bstep (se 2 (by rfl) ⟨402558, by rfl⟩ : syracuseStep 1073489 = 805117) B805117
theorem B1073507 : Blo 714321 1073507 := bstep (se 1 (by rfl) ⟨805130, by rfl⟩ : syracuseStep 1073507 = 1610261) B1610261
theorem B1073537 : Blo 714321 1073537 := bstep (se 2 (by rfl) ⟨402576, by rfl⟩ : syracuseStep 1073537 = 805153) B805153
theorem B1073555 : Blo 714321 1073555 := bstep (se 1 (by rfl) ⟨805166, by rfl⟩ : syracuseStep 1073555 = 1610333) B1610333
theorem B1073585 : Blo 714321 1073585 := bstep (se 2 (by rfl) ⟨402594, by rfl⟩ : syracuseStep 1073585 = 805189) B805189
theorem B1073603 : Blo 714321 1073603 := bstep (se 1 (by rfl) ⟨805202, by rfl⟩ : syracuseStep 1073603 = 1610405) B1610405
theorem B1073633 : Blo 714321 1073633 := bstep (se 2 (by rfl) ⟨402612, by rfl⟩ : syracuseStep 1073633 = 805225) B805225
theorem B1073651 : Blo 714321 1073651 := bstep (se 1 (by rfl) ⟨805238, by rfl⟩ : syracuseStep 1073651 = 1610477) B1610477
theorem B1073681 : Blo 714321 1073681 := bstep (se 2 (by rfl) ⟨402630, by rfl⟩ : syracuseStep 1073681 = 805261) B805261
theorem B1073699 : Blo 714321 1073699 := bstep (se 1 (by rfl) ⟨805274, by rfl⟩ : syracuseStep 1073699 = 1610549) B1610549
theorem B2417201 : Blo 714321 2417201 := bstep (se 2 (by rfl) ⟨906450, by rfl⟩ : syracuseStep 2417201 = 1812901) B1812901
theorem B1073729 : Blo 714321 1073729 := bstep (se 2 (by rfl) ⟨402648, by rfl⟩ : syracuseStep 1073729 = 805297) B805297
theorem B1073747 : Blo 714321 1073747 := bstep (se 1 (by rfl) ⟨805310, by rfl⟩ : syracuseStep 1073747 = 1610621) B1610621
theorem B1073777 : Blo 714321 1073777 := bstep (se 2 (by rfl) ⟨402666, by rfl⟩ : syracuseStep 1073777 = 805333) B805333
theorem B1073795 : Blo 714321 1073795 := bstep (se 1 (by rfl) ⟨805346, by rfl⟩ : syracuseStep 1073795 = 1610693) B1610693
theorem B1073825 : Blo 714321 1073825 := bstep (se 2 (by rfl) ⟨402684, by rfl⟩ : syracuseStep 1073825 = 805369) B805369
theorem B1073843 : Blo 714321 1073843 := bstep (se 1 (by rfl) ⟨805382, by rfl⟩ : syracuseStep 1073843 = 1610765) B1610765
theorem B1073873 : Blo 714321 1073873 := bstep (se 2 (by rfl) ⟨402702, by rfl⟩ : syracuseStep 1073873 = 805405) B805405
theorem B1073891 : Blo 714321 1073891 := bstep (se 1 (by rfl) ⟨805418, by rfl⟩ : syracuseStep 1073891 = 1610837) B1610837
theorem B2712305 : Blo 714321 2712305 := bstep (se 2 (by rfl) ⟨1017114, by rfl⟩ : syracuseStep 2712305 = 2034229) B2034229
theorem B1073921 : Blo 714321 1073921 := bstep (se 2 (by rfl) ⟨402720, by rfl⟩ : syracuseStep 1073921 = 805441) B805441
theorem B1106689 : Blo 714321 1106689 := bstep (se 2 (by rfl) ⟨415008, by rfl⟩ : syracuseStep 1106689 = 830017) B830017
theorem B1073939 : Blo 714321 1073939 := bstep (se 1 (by rfl) ⟨805454, by rfl⟩ : syracuseStep 1073939 = 1610909) B1610909
theorem B1073969 : Blo 714321 1073969 := bstep (se 2 (by rfl) ⟨402738, by rfl⟩ : syracuseStep 1073969 = 805477) B805477
theorem B1073987 : Blo 714321 1073987 := bstep (se 1 (by rfl) ⟨805490, by rfl⟩ : syracuseStep 1073987 = 1610981) B1610981
theorem B1074017 : Blo 714321 1074017 := bstep (se 2 (by rfl) ⟨402756, by rfl⟩ : syracuseStep 1074017 = 805513) B805513
theorem B1631075 : Blo 714321 1631075 := bstep (se 1 (by rfl) ⟨1223306, by rfl⟩ : syracuseStep 1631075 = 2446613) B2446613
theorem B1074035 : Blo 714321 1074035 := bstep (se 1 (by rfl) ⟨805526, by rfl⟩ : syracuseStep 1074035 = 1611053) B1611053
theorem B1074065 : Blo 714321 1074065 := bstep (se 2 (by rfl) ⟨402774, by rfl⟩ : syracuseStep 1074065 = 805549) B805549
theorem B1074083 : Blo 714321 1074083 := bstep (se 1 (by rfl) ⟨805562, by rfl⟩ : syracuseStep 1074083 = 1611125) B1611125
theorem B1074113 : Blo 714321 1074113 := bstep (se 2 (by rfl) ⟨402792, by rfl⟩ : syracuseStep 1074113 = 805585) B805585
theorem B1074131 : Blo 714321 1074131 := bstep (se 1 (by rfl) ⟨805598, by rfl⟩ : syracuseStep 1074131 = 1611197) B1611197
theorem B1074161 : Blo 714321 1074161 := bstep (se 2 (by rfl) ⟨402810, by rfl⟩ : syracuseStep 1074161 = 805621) B805621
theorem B1074179 : Blo 714321 1074179 := bstep (se 1 (by rfl) ⟨805634, by rfl⟩ : syracuseStep 1074179 = 1611269) B1611269
theorem B1074209 : Blo 714321 1074209 := bstep (se 2 (by rfl) ⟨402828, by rfl⟩ : syracuseStep 1074209 = 805657) B805657
theorem B1074227 : Blo 714321 1074227 := bstep (se 1 (by rfl) ⟨805670, by rfl⟩ : syracuseStep 1074227 = 1611341) B1611341
theorem B2417741 : Blo 714321 2417741 := bstep (se 3 (by rfl) ⟨453326, by rfl⟩ : syracuseStep 2417741 = 906653) B906653
theorem B1074257 : Blo 714321 1074257 := bstep (se 2 (by rfl) ⟨402846, by rfl⟩ : syracuseStep 1074257 = 805693) B805693
theorem B1074275 : Blo 714321 1074275 := bstep (se 1 (by rfl) ⟨805706, by rfl⟩ : syracuseStep 1074275 = 1611413) B1611413
theorem B1074305 : Blo 714321 1074305 := bstep (se 2 (by rfl) ⟨402864, by rfl⟩ : syracuseStep 1074305 = 805729) B805729
theorem B2417795 : Blo 714321 2417795 := bstep (se 1 (by rfl) ⟨1813346, by rfl⟩ : syracuseStep 2417795 = 3626693) B3626693
theorem B1074323 : Blo 714321 1074323 := bstep (se 1 (by rfl) ⟨805742, by rfl⟩ : syracuseStep 1074323 = 1611485) B1611485
theorem B1074353 : Blo 714321 1074353 := bstep (se 2 (by rfl) ⟨402882, by rfl⟩ : syracuseStep 1074353 = 805765) B805765
theorem B3630257 : Blo 714321 3630257 := bstep (se 2 (by rfl) ⟨1361346, by rfl⟩ : syracuseStep 3630257 = 2722693) B2722693
theorem B1074371 : Blo 714321 1074371 := bstep (se 1 (by rfl) ⟨805778, by rfl⟩ : syracuseStep 1074371 = 1611557) B1611557
theorem B1074401 : Blo 714321 1074401 := bstep (se 2 (by rfl) ⟨402900, by rfl⟩ : syracuseStep 1074401 = 805801) B805801
theorem B1205489 : Blo 714321 1205489 := bstep (se 2 (by rfl) ⟨452058, by rfl⟩ : syracuseStep 1205489 = 904117) B904117
theorem B1074419 : Blo 714321 1074419 := bstep (se 1 (by rfl) ⟨805814, by rfl⟩ : syracuseStep 1074419 = 1611629) B1611629
theorem B1074449 : Blo 714321 1074449 := bstep (se 2 (by rfl) ⟨402918, by rfl⟩ : syracuseStep 1074449 = 805837) B805837
theorem B1074467 : Blo 714321 1074467 := bstep (se 1 (by rfl) ⟨805850, by rfl⟩ : syracuseStep 1074467 = 1611701) B1611701
theorem B4580657 : Blo 714321 4580657 := bstep (se 2 (by rfl) ⟨1717746, by rfl⟩ : syracuseStep 4580657 = 3435493) B3435493
theorem B1074497 : Blo 714321 1074497 := bstep (se 2 (by rfl) ⟨402936, by rfl⟩ : syracuseStep 1074497 = 805873) B805873
theorem B1074515 : Blo 714321 1074515 := bstep (se 1 (by rfl) ⟨805886, by rfl⟩ : syracuseStep 1074515 = 1611773) B1611773
theorem B1205617 : Blo 714321 1205617 := bstep (se 2 (by rfl) ⟨452106, by rfl⟩ : syracuseStep 1205617 = 904213) B904213
theorem B1074545 : Blo 714321 1074545 := bstep (se 2 (by rfl) ⟨402954, by rfl⟩ : syracuseStep 1074545 = 805909) B805909
theorem B1074563 : Blo 714321 1074563 := bstep (se 1 (by rfl) ⟨805922, by rfl⟩ : syracuseStep 1074563 = 1611845) B1611845
theorem B2712973 : Blo 714321 2712973 := bstep (se 3 (by rfl) ⟨508682, by rfl⟩ : syracuseStep 2712973 = 1017365) B1017365
theorem B2418065 : Blo 714321 2418065 := bstep (se 2 (by rfl) ⟨906774, by rfl⟩ : syracuseStep 2418065 = 1813549) B1813549
theorem B1205651 : Blo 714321 1205651 := bstep (se 1 (by rfl) ⟨904238, by rfl⟩ : syracuseStep 1205651 = 1808477) B1808477
theorem B1074593 : Blo 714321 1074593 := bstep (se 2 (by rfl) ⟨402972, by rfl⟩ : syracuseStep 1074593 = 805945) B805945
theorem B1074611 : Blo 714321 1074611 := bstep (se 1 (by rfl) ⟨805958, by rfl⟩ : syracuseStep 1074611 = 1611917) B1611917
theorem B1074641 : Blo 714321 1074641 := bstep (se 2 (by rfl) ⟨402990, by rfl⟩ : syracuseStep 1074641 = 805981) B805981
theorem B1074659 : Blo 714321 1074659 := bstep (se 1 (by rfl) ⟨805994, by rfl⟩ : syracuseStep 1074659 = 1611989) B1611989
theorem B1074689 : Blo 714321 1074689 := bstep (se 2 (by rfl) ⟨403008, by rfl⟩ : syracuseStep 1074689 = 806017) B806017
theorem B1205779 : Blo 714321 1205779 := bstep (se 1 (by rfl) ⟨904334, by rfl⟩ : syracuseStep 1205779 = 1808669) B1808669
theorem B1074707 : Blo 714321 1074707 := bstep (se 1 (by rfl) ⟨806030, by rfl⟩ : syracuseStep 1074707 = 1612061) B1612061
theorem B1074737 : Blo 714321 1074737 := bstep (se 2 (by rfl) ⟨403026, by rfl⟩ : syracuseStep 1074737 = 806053) B806053
theorem B1074755 : Blo 714321 1074755 := bstep (se 1 (by rfl) ⟨806066, by rfl⟩ : syracuseStep 1074755 = 1612133) B1612133
theorem B714323 : Blo 714321 714323 := bstep (se 1 (by rfl) ⟨535742, by rfl⟩ : syracuseStep 714323 = 1071485) B1071485
theorem B1074785 : Blo 714321 1074785 := bstep (se 2 (by rfl) ⟨403044, by rfl⟩ : syracuseStep 1074785 = 806089) B806089
theorem B714339 : Blo 714321 714339 := bstep (se 1 (by rfl) ⟨535754, by rfl⟩ : syracuseStep 714339 = 1071509) B1071509
theorem B714355 : Blo 714321 714355 := bstep (se 1 (by rfl) ⟨535766, by rfl⟩ : syracuseStep 714355 = 1071533) B1071533
theorem B1074803 : Blo 714321 1074803 := bstep (se 1 (by rfl) ⟨806102, by rfl⟩ : syracuseStep 1074803 = 1612205) B1612205
theorem B714371 : Blo 714321 714371 := bstep (se 1 (by rfl) ⟨535778, by rfl⟩ : syracuseStep 714371 = 1071557) B1071557
theorem B1074833 : Blo 714321 1074833 := bstep (se 2 (by rfl) ⟨403062, by rfl⟩ : syracuseStep 1074833 = 806125) B806125
theorem B714387 : Blo 714321 714387 := bstep (se 1 (by rfl) ⟨535790, by rfl⟩ : syracuseStep 714387 = 1071581) B1071581
theorem B1205921 : Blo 714321 1205921 := bstep (se 2 (by rfl) ⟨452220, by rfl⟩ : syracuseStep 1205921 = 904441) B904441
theorem B714403 : Blo 714321 714403 := bstep (se 1 (by rfl) ⟨535802, by rfl⟩ : syracuseStep 714403 = 1071605) B1071605
theorem B1074851 : Blo 714321 1074851 := bstep (se 1 (by rfl) ⟨806138, by rfl⟩ : syracuseStep 1074851 = 1612277) B1612277
theorem B714419 : Blo 714321 714419 := bstep (se 1 (by rfl) ⟨535814, by rfl⟩ : syracuseStep 714419 = 1071629) B1071629
theorem B1074881 : Blo 714321 1074881 := bstep (se 2 (by rfl) ⟨403080, by rfl⟩ : syracuseStep 1074881 = 806161) B806161
theorem B714435 : Blo 714321 714435 := bstep (se 1 (by rfl) ⟨535826, by rfl⟩ : syracuseStep 714435 = 1071653) B1071653
theorem B714451 : Blo 714321 714451 := bstep (se 1 (by rfl) ⟨535838, by rfl⟩ : syracuseStep 714451 = 1071677) B1071677
theorem B1074899 : Blo 714321 1074899 := bstep (se 1 (by rfl) ⟨806174, by rfl⟩ : syracuseStep 1074899 = 1612349) B1612349
theorem B714467 : Blo 714321 714467 := bstep (se 1 (by rfl) ⟨535850, by rfl⟩ : syracuseStep 714467 = 1071701) B1071701
theorem B1074929 : Blo 714321 1074929 := bstep (se 2 (by rfl) ⟨403098, by rfl⟩ : syracuseStep 1074929 = 806197) B806197
theorem B714483 : Blo 714321 714483 := bstep (se 1 (by rfl) ⟨535862, by rfl⟩ : syracuseStep 714483 = 1071725) B1071725
theorem B714499 : Blo 714321 714499 := bstep (se 1 (by rfl) ⟨535874, by rfl⟩ : syracuseStep 714499 = 1071749) B1071749
theorem B1074947 : Blo 714321 1074947 := bstep (se 1 (by rfl) ⟨806210, by rfl⟩ : syracuseStep 1074947 = 1612421) B1612421
theorem B714515 : Blo 714321 714515 := bstep (se 1 (by rfl) ⟨535886, by rfl⟩ : syracuseStep 714515 = 1071773) B1071773
theorem B1206049 : Blo 714321 1206049 := bstep (se 2 (by rfl) ⟨452268, by rfl⟩ : syracuseStep 1206049 = 904537) B904537
theorem B714531 : Blo 714321 714531 := bstep (se 1 (by rfl) ⟨535898, by rfl⟩ : syracuseStep 714531 = 1071797) B1071797
theorem B1074977 : Blo 714321 1074977 := bstep (se 2 (by rfl) ⟨403116, by rfl⟩ : syracuseStep 1074977 = 806233) B806233
theorem B714547 : Blo 714321 714547 := bstep (se 1 (by rfl) ⟨535910, by rfl⟩ : syracuseStep 714547 = 1071821) B1071821
theorem B1074995 : Blo 714321 1074995 := bstep (se 1 (by rfl) ⟨806246, by rfl⟩ : syracuseStep 1074995 = 1612493) B1612493
theorem B714563 : Blo 714321 714563 := bstep (se 1 (by rfl) ⟨535922, by rfl⟩ : syracuseStep 714563 = 1071845) B1071845
theorem B1206083 : Blo 714321 1206083 := bstep (se 1 (by rfl) ⟨904562, by rfl⟩ : syracuseStep 1206083 = 1809125) B1809125
theorem B4581197 : Blo 714321 4581197 := bstep (se 3 (by rfl) ⟨858974, by rfl⟩ : syracuseStep 4581197 = 1717949) B1717949
theorem B1075025 : Blo 714321 1075025 := bstep (se 2 (by rfl) ⟨403134, by rfl⟩ : syracuseStep 1075025 = 806269) B806269
theorem B714579 : Blo 714321 714579 := bstep (se 1 (by rfl) ⟨535934, by rfl⟩ : syracuseStep 714579 = 1071869) B1071869
theorem B714595 : Blo 714321 714595 := bstep (se 1 (by rfl) ⟨535946, by rfl⟩ : syracuseStep 714595 = 1071893) B1071893
theorem B1075043 : Blo 714321 1075043 := bstep (se 1 (by rfl) ⟨806282, by rfl⟩ : syracuseStep 1075043 = 1612565) B1612565
theorem B714611 : Blo 714321 714611 := bstep (se 1 (by rfl) ⟨535958, by rfl⟩ : syracuseStep 714611 = 1071917) B1071917
theorem B1075073 : Blo 714321 1075073 := bstep (se 2 (by rfl) ⟨403152, by rfl⟩ : syracuseStep 1075073 = 806305) B806305
theorem B714627 : Blo 714321 714627 := bstep (se 1 (by rfl) ⟨535970, by rfl⟩ : syracuseStep 714627 = 1071941) B1071941
theorem B714643 : Blo 714321 714643 := bstep (se 1 (by rfl) ⟨535982, by rfl⟩ : syracuseStep 714643 = 1071965) B1071965
theorem B1075091 : Blo 714321 1075091 := bstep (se 1 (by rfl) ⟨806318, by rfl⟩ : syracuseStep 1075091 = 1612637) B1612637
theorem B714659 : Blo 714321 714659 := bstep (se 1 (by rfl) ⟨535994, by rfl⟩ : syracuseStep 714659 = 1071989) B1071989
theorem B2418605 : Blo 714321 2418605 := bstep (se 3 (by rfl) ⟨453488, by rfl⟩ : syracuseStep 2418605 = 906977) B906977
theorem B1075121 : Blo 714321 1075121 := bstep (se 2 (by rfl) ⟨403170, by rfl⟩ : syracuseStep 1075121 = 806341) B806341
theorem B714675 : Blo 714321 714675 := bstep (se 1 (by rfl) ⟨536006, by rfl⟩ : syracuseStep 714675 = 1072013) B1072013
theorem B714691 : Blo 714321 714691 := bstep (se 1 (by rfl) ⟨536018, by rfl⟩ : syracuseStep 714691 = 1072037) B1072037
theorem B1206211 : Blo 714321 1206211 := bstep (se 1 (by rfl) ⟨904658, by rfl⟩ : syracuseStep 1206211 = 1809317) B1809317
theorem B1075139 : Blo 714321 1075139 := bstep (se 1 (by rfl) ⟨806354, by rfl⟩ : syracuseStep 1075139 = 1612709) B1612709
theorem B714707 : Blo 714321 714707 := bstep (se 1 (by rfl) ⟨536030, by rfl⟩ : syracuseStep 714707 = 1072061) B1072061
theorem B1075169 : Blo 714321 1075169 := bstep (se 2 (by rfl) ⟨403188, by rfl⟩ : syracuseStep 1075169 = 806377) B806377
theorem B714723 : Blo 714321 714723 := bstep (se 1 (by rfl) ⟨536042, by rfl⟩ : syracuseStep 714723 = 1072085) B1072085
theorem B2418659 : Blo 714321 2418659 := bstep (se 1 (by rfl) ⟨1813994, by rfl⟩ : syracuseStep 2418659 = 3627989) B3627989
theorem B714739 : Blo 714321 714739 := bstep (se 1 (by rfl) ⟨536054, by rfl⟩ : syracuseStep 714739 = 1072109) B1072109
theorem B1075187 : Blo 714321 1075187 := bstep (se 1 (by rfl) ⟨806390, by rfl⟩ : syracuseStep 1075187 = 1612781) B1612781
theorem B714755 : Blo 714321 714755 := bstep (se 1 (by rfl) ⟨536066, by rfl⟩ : syracuseStep 714755 = 1072133) B1072133
theorem B1009667 : Blo 714321 1009667 := bstep (se 1 (by rfl) ⟨757250, by rfl⟩ : syracuseStep 1009667 = 1514501) B1514501
theorem B1075217 : Blo 714321 1075217 := bstep (se 2 (by rfl) ⟨403206, by rfl⟩ : syracuseStep 1075217 = 806413) B806413
theorem B714771 : Blo 714321 714771 := bstep (se 1 (by rfl) ⟨536078, by rfl⟩ : syracuseStep 714771 = 1072157) B1072157
theorem B714787 : Blo 714321 714787 := bstep (se 1 (by rfl) ⟨536090, by rfl⟩ : syracuseStep 714787 = 1072181) B1072181
theorem B1075235 : Blo 714321 1075235 := bstep (se 1 (by rfl) ⟨806426, by rfl⟩ : syracuseStep 1075235 = 1612853) B1612853
theorem B714803 : Blo 714321 714803 := bstep (se 1 (by rfl) ⟨536102, by rfl⟩ : syracuseStep 714803 = 1072205) B1072205
theorem B1075265 : Blo 714321 1075265 := bstep (se 2 (by rfl) ⟨403224, by rfl⟩ : syracuseStep 1075265 = 806449) B806449
theorem B714819 : Blo 714321 714819 := bstep (se 1 (by rfl) ⟨536114, by rfl⟩ : syracuseStep 714819 = 1072229) B1072229
theorem B1206353 : Blo 714321 1206353 := bstep (se 2 (by rfl) ⟨452382, by rfl⟩ : syracuseStep 1206353 = 904765) B904765
theorem B714835 : Blo 714321 714835 := bstep (se 1 (by rfl) ⟨536126, by rfl⟩ : syracuseStep 714835 = 1072253) B1072253
theorem B1075283 : Blo 714321 1075283 := bstep (se 1 (by rfl) ⟨806462, by rfl⟩ : syracuseStep 1075283 = 1612925) B1612925
theorem B714851 : Blo 714321 714851 := bstep (se 1 (by rfl) ⟨536138, by rfl⟩ : syracuseStep 714851 = 1072277) B1072277
theorem B1075313 : Blo 714321 1075313 := bstep (se 2 (by rfl) ⟨403242, by rfl⟩ : syracuseStep 1075313 = 806485) B806485
theorem B714867 : Blo 714321 714867 := bstep (se 1 (by rfl) ⟨536150, by rfl⟩ : syracuseStep 714867 = 1072301) B1072301
theorem B714883 : Blo 714321 714883 := bstep (se 1 (by rfl) ⟨536162, by rfl⟩ : syracuseStep 714883 = 1072325) B1072325
theorem B1075331 : Blo 714321 1075331 := bstep (se 1 (by rfl) ⟨806498, by rfl⟩ : syracuseStep 1075331 = 1612997) B1612997
theorem B714899 : Blo 714321 714899 := bstep (se 1 (by rfl) ⟨536174, by rfl⟩ : syracuseStep 714899 = 1072349) B1072349
theorem B1075361 : Blo 714321 1075361 := bstep (se 2 (by rfl) ⟨403260, by rfl⟩ : syracuseStep 1075361 = 806521) B806521
theorem B2713763 : Blo 714321 2713763 := bstep (se 1 (by rfl) ⟨2035322, by rfl⟩ : syracuseStep 2713763 = 4070645) B4070645
theorem B714915 : Blo 714321 714915 := bstep (se 1 (by rfl) ⟨536186, by rfl⟩ : syracuseStep 714915 = 1072373) B1072373
theorem B714931 : Blo 714321 714931 := bstep (se 1 (by rfl) ⟨536198, by rfl⟩ : syracuseStep 714931 = 1072397) B1072397
theorem B1075379 : Blo 714321 1075379 := bstep (se 1 (by rfl) ⟨806534, by rfl⟩ : syracuseStep 1075379 = 1613069) B1613069
theorem B714947 : Blo 714321 714947 := bstep (se 1 (by rfl) ⟨536210, by rfl⟩ : syracuseStep 714947 = 1072421) B1072421
theorem B6187205 : Blo 714321 6187205 := bstep (se 4 (by rfl) ⟨580050, by rfl⟩ : syracuseStep 6187205 = 1160101) B1160101
theorem B1206481 : Blo 714321 1206481 := bstep (se 2 (by rfl) ⟨452430, by rfl⟩ : syracuseStep 1206481 = 904861) B904861
theorem B1075409 : Blo 714321 1075409 := bstep (se 2 (by rfl) ⟨403278, by rfl⟩ : syracuseStep 1075409 = 806557) B806557
theorem B714963 : Blo 714321 714963 := bstep (se 1 (by rfl) ⟨536222, by rfl⟩ : syracuseStep 714963 = 1072445) B1072445
theorem B714979 : Blo 714321 714979 := bstep (se 1 (by rfl) ⟨536234, by rfl⟩ : syracuseStep 714979 = 1072469) B1072469
theorem B1861859 : Blo 714321 1861859 := bstep (se 1 (by rfl) ⟨1396394, by rfl⟩ : syracuseStep 1861859 = 2792789) B2792789
theorem B1075427 : Blo 714321 1075427 := bstep (se 1 (by rfl) ⟨806570, by rfl⟩ : syracuseStep 1075427 = 1613141) B1613141
theorem B2418929 : Blo 714321 2418929 := bstep (se 2 (by rfl) ⟨907098, by rfl⟩ : syracuseStep 2418929 = 1814197) B1814197
theorem B1206515 : Blo 714321 1206515 := bstep (se 1 (by rfl) ⟨904886, by rfl⟩ : syracuseStep 1206515 = 1809773) B1809773
theorem B714995 : Blo 714321 714995 := bstep (se 1 (by rfl) ⟨536246, by rfl⟩ : syracuseStep 714995 = 1072493) B1072493
theorem B1075457 : Blo 714321 1075457 := bstep (se 2 (by rfl) ⟨403296, by rfl⟩ : syracuseStep 1075457 = 806593) B806593
theorem B715011 : Blo 714321 715011 := bstep (se 1 (by rfl) ⟨536258, by rfl⟩ : syracuseStep 715011 = 1072517) B1072517
theorem B715027 : Blo 714321 715027 := bstep (se 1 (by rfl) ⟨536270, by rfl⟩ : syracuseStep 715027 = 1072541) B1072541
theorem B1075475 : Blo 714321 1075475 := bstep (se 1 (by rfl) ⟨806606, by rfl⟩ : syracuseStep 1075475 = 1613213) B1613213
theorem B715043 : Blo 714321 715043 := bstep (se 1 (by rfl) ⟨536282, by rfl⟩ : syracuseStep 715043 = 1072565) B1072565
theorem B1075505 : Blo 714321 1075505 := bstep (se 2 (by rfl) ⟨403314, by rfl⟩ : syracuseStep 1075505 = 806629) B806629
theorem B715059 : Blo 714321 715059 := bstep (se 1 (by rfl) ⟨536294, by rfl⟩ : syracuseStep 715059 = 1072589) B1072589
theorem B715075 : Blo 714321 715075 := bstep (se 1 (by rfl) ⟨536306, by rfl⟩ : syracuseStep 715075 = 1072613) B1072613
theorem B1075523 : Blo 714321 1075523 := bstep (se 1 (by rfl) ⟨806642, by rfl⟩ : syracuseStep 1075523 = 1613285) B1613285
theorem B715091 : Blo 714321 715091 := bstep (se 1 (by rfl) ⟨536318, by rfl⟩ : syracuseStep 715091 = 1072637) B1072637
theorem B1075553 : Blo 714321 1075553 := bstep (se 2 (by rfl) ⟨403332, by rfl⟩ : syracuseStep 1075553 = 806665) B806665
theorem B715107 : Blo 714321 715107 := bstep (se 1 (by rfl) ⟨536330, by rfl⟩ : syracuseStep 715107 = 1072661) B1072661
theorem B1206643 : Blo 714321 1206643 := bstep (se 1 (by rfl) ⟨904982, by rfl⟩ : syracuseStep 1206643 = 1809965) B1809965
theorem B715123 : Blo 714321 715123 := bstep (se 1 (by rfl) ⟨536342, by rfl⟩ : syracuseStep 715123 = 1072685) B1072685
theorem B1075571 : Blo 714321 1075571 := bstep (se 1 (by rfl) ⟨806678, by rfl⟩ : syracuseStep 1075571 = 1613357) B1613357
theorem B715139 : Blo 714321 715139 := bstep (se 1 (by rfl) ⟨536354, by rfl⟩ : syracuseStep 715139 = 1072709) B1072709
theorem B1075601 : Blo 714321 1075601 := bstep (se 2 (by rfl) ⟨403350, by rfl⟩ : syracuseStep 1075601 = 806701) B806701
theorem B715155 : Blo 714321 715155 := bstep (se 1 (by rfl) ⟨536366, by rfl⟩ : syracuseStep 715155 = 1072733) B1072733
theorem B715171 : Blo 714321 715171 := bstep (se 1 (by rfl) ⟨536378, by rfl⟩ : syracuseStep 715171 = 1072757) B1072757
theorem B1075619 : Blo 714321 1075619 := bstep (se 1 (by rfl) ⟨806714, by rfl⟩ : syracuseStep 1075619 = 1613429) B1613429
theorem B715187 : Blo 714321 715187 := bstep (se 1 (by rfl) ⟨536390, by rfl⟩ : syracuseStep 715187 = 1072781) B1072781
theorem B1075649 : Blo 714321 1075649 := bstep (se 2 (by rfl) ⟨403368, by rfl⟩ : syracuseStep 1075649 = 806737) B806737
theorem B715203 : Blo 714321 715203 := bstep (se 1 (by rfl) ⟨536402, by rfl⟩ : syracuseStep 715203 = 1072805) B1072805
theorem B715219 : Blo 714321 715219 := bstep (se 1 (by rfl) ⟨536414, by rfl⟩ : syracuseStep 715219 = 1072829) B1072829
theorem B1075667 : Blo 714321 1075667 := bstep (se 1 (by rfl) ⟨806750, by rfl⟩ : syracuseStep 1075667 = 1613501) B1613501
theorem B715235 : Blo 714321 715235 := bstep (se 1 (by rfl) ⟨536426, by rfl⟩ : syracuseStep 715235 = 1072853) B1072853
theorem B3434993 : Blo 714321 3434993 := bstep (se 2 (by rfl) ⟨1288122, by rfl⟩ : syracuseStep 3434993 = 2576245) B2576245
theorem B1075697 : Blo 714321 1075697 := bstep (se 2 (by rfl) ⟨403386, by rfl⟩ : syracuseStep 1075697 = 806773) B806773
theorem B715251 : Blo 714321 715251 := bstep (se 1 (by rfl) ⟨536438, by rfl⟩ : syracuseStep 715251 = 1072877) B1072877
theorem B1206785 : Blo 714321 1206785 := bstep (se 2 (by rfl) ⟨452544, by rfl⟩ : syracuseStep 1206785 = 905089) B905089
theorem B715267 : Blo 714321 715267 := bstep (se 1 (by rfl) ⟨536450, by rfl⟩ : syracuseStep 715267 = 1072901) B1072901
theorem B1075715 : Blo 714321 1075715 := bstep (se 1 (by rfl) ⟨806786, by rfl⟩ : syracuseStep 1075715 = 1613573) B1613573
theorem B715283 : Blo 714321 715283 := bstep (se 1 (by rfl) ⟨536462, by rfl⟩ : syracuseStep 715283 = 1072925) B1072925
theorem B1075745 : Blo 714321 1075745 := bstep (se 2 (by rfl) ⟨403404, by rfl⟩ : syracuseStep 1075745 = 806809) B806809
theorem B715299 : Blo 714321 715299 := bstep (se 1 (by rfl) ⟨536474, by rfl⟩ : syracuseStep 715299 = 1072949) B1072949
theorem B715315 : Blo 714321 715315 := bstep (se 1 (by rfl) ⟨536486, by rfl⟩ : syracuseStep 715315 = 1072973) B1072973
theorem B1075763 : Blo 714321 1075763 := bstep (se 1 (by rfl) ⟨806822, by rfl⟩ : syracuseStep 1075763 = 1613645) B1613645
theorem B715331 : Blo 714321 715331 := bstep (se 1 (by rfl) ⟨536498, by rfl⟩ : syracuseStep 715331 = 1072997) B1072997
theorem B1075793 : Blo 714321 1075793 := bstep (se 2 (by rfl) ⟨403422, by rfl⟩ : syracuseStep 1075793 = 806845) B806845
theorem B715347 : Blo 714321 715347 := bstep (se 1 (by rfl) ⟨536510, by rfl⟩ : syracuseStep 715347 = 1073021) B1073021
theorem B715363 : Blo 714321 715363 := bstep (se 1 (by rfl) ⟨536522, by rfl⟩ : syracuseStep 715363 = 1073045) B1073045
theorem B1075811 : Blo 714321 1075811 := bstep (se 1 (by rfl) ⟨806858, by rfl⟩ : syracuseStep 1075811 = 1613717) B1613717
theorem B3631715 : Blo 714321 3631715 := bstep (se 1 (by rfl) ⟨2723786, by rfl⟩ : syracuseStep 3631715 = 5447573) B5447573
theorem B4909667 : Blo 714321 4909667 := bstep (se 1 (by rfl) ⟨3682250, by rfl⟩ : syracuseStep 4909667 = 7364501) B7364501
theorem B715379 : Blo 714321 715379 := bstep (se 1 (by rfl) ⟨536534, by rfl⟩ : syracuseStep 715379 = 1073069) B1073069
theorem B1206913 : Blo 714321 1206913 := bstep (se 2 (by rfl) ⟨452592, by rfl⟩ : syracuseStep 1206913 = 905185) B905185
theorem B1075841 : Blo 714321 1075841 := bstep (se 2 (by rfl) ⟨403440, by rfl⟩ : syracuseStep 1075841 = 806881) B806881
theorem B715395 : Blo 714321 715395 := bstep (se 1 (by rfl) ⟨536546, by rfl⟩ : syracuseStep 715395 = 1073093) B1073093
theorem B715411 : Blo 714321 715411 := bstep (se 1 (by rfl) ⟨536558, by rfl⟩ : syracuseStep 715411 = 1073117) B1073117
theorem B1075859 : Blo 714321 1075859 := bstep (se 1 (by rfl) ⟨806894, by rfl⟩ : syracuseStep 1075859 = 1613789) B1613789
theorem B1206947 : Blo 714321 1206947 := bstep (se 1 (by rfl) ⟨905210, by rfl⟩ : syracuseStep 1206947 = 1810421) B1810421
theorem B715427 : Blo 714321 715427 := bstep (se 1 (by rfl) ⟨536570, by rfl⟩ : syracuseStep 715427 = 1073141) B1073141
theorem B3435185 : Blo 714321 3435185 := bstep (se 2 (by rfl) ⟨1288194, by rfl⟩ : syracuseStep 3435185 = 2576389) B2576389
theorem B1075889 : Blo 714321 1075889 := bstep (se 2 (by rfl) ⟨403458, by rfl⟩ : syracuseStep 1075889 = 806917) B806917
theorem B715443 : Blo 714321 715443 := bstep (se 1 (by rfl) ⟨536582, by rfl⟩ : syracuseStep 715443 = 1073165) B1073165
theorem B715459 : Blo 714321 715459 := bstep (se 1 (by rfl) ⟨536594, by rfl⟩ : syracuseStep 715459 = 1073189) B1073189
theorem B1075907 : Blo 714321 1075907 := bstep (se 1 (by rfl) ⟨806930, by rfl⟩ : syracuseStep 1075907 = 1613861) B1613861
theorem B715475 : Blo 714321 715475 := bstep (se 1 (by rfl) ⟨536606, by rfl⟩ : syracuseStep 715475 = 1073213) B1073213
theorem B1075937 : Blo 714321 1075937 := bstep (se 2 (by rfl) ⟨403476, by rfl⟩ : syracuseStep 1075937 = 806953) B806953
theorem B715491 : Blo 714321 715491 := bstep (se 1 (by rfl) ⟨536618, by rfl⟩ : syracuseStep 715491 = 1073237) B1073237
theorem B715507 : Blo 714321 715507 := bstep (se 1 (by rfl) ⟨536630, by rfl⟩ : syracuseStep 715507 = 1073261) B1073261
theorem B1075955 : Blo 714321 1075955 := bstep (se 1 (by rfl) ⟨806966, by rfl⟩ : syracuseStep 1075955 = 1613933) B1613933
theorem B715523 : Blo 714321 715523 := bstep (se 1 (by rfl) ⟨536642, by rfl⟩ : syracuseStep 715523 = 1073285) B1073285
theorem B2419469 : Blo 714321 2419469 := bstep (se 3 (by rfl) ⟨453650, by rfl⟩ : syracuseStep 2419469 = 907301) B907301
theorem B1075985 : Blo 714321 1075985 := bstep (se 2 (by rfl) ⟨403494, by rfl⟩ : syracuseStep 1075985 = 806989) B806989
theorem B715539 : Blo 714321 715539 := bstep (se 1 (by rfl) ⟨536654, by rfl⟩ : syracuseStep 715539 = 1073309) B1073309
theorem B3435299 : Blo 714321 3435299 := bstep (se 1 (by rfl) ⟨2576474, by rfl⟩ : syracuseStep 3435299 = 5152949) B5152949
theorem B1207075 : Blo 714321 1207075 := bstep (se 1 (by rfl) ⟨905306, by rfl⟩ : syracuseStep 1207075 = 1810613) B1810613
theorem B715555 : Blo 714321 715555 := bstep (se 1 (by rfl) ⟨536666, by rfl⟩ : syracuseStep 715555 = 1073333) B1073333
theorem B1076003 : Blo 714321 1076003 := bstep (se 1 (by rfl) ⟨807002, by rfl⟩ : syracuseStep 1076003 = 1614005) B1614005
theorem B2714417 : Blo 714321 2714417 := bstep (se 2 (by rfl) ⟨1017906, by rfl⟩ : syracuseStep 2714417 = 2035813) B2035813
theorem B715571 : Blo 714321 715571 := bstep (se 1 (by rfl) ⟨536678, by rfl⟩ : syracuseStep 715571 = 1073357) B1073357
theorem B1076033 : Blo 714321 1076033 := bstep (se 2 (by rfl) ⟨403512, by rfl⟩ : syracuseStep 1076033 = 807025) B807025
theorem B715587 : Blo 714321 715587 := bstep (se 1 (by rfl) ⟨536690, by rfl⟩ : syracuseStep 715587 = 1073381) B1073381
theorem B2419523 : Blo 714321 2419523 := bstep (se 1 (by rfl) ⟨1814642, by rfl⟩ : syracuseStep 2419523 = 3629285) B3629285
theorem B715603 : Blo 714321 715603 := bstep (se 1 (by rfl) ⟨536702, by rfl⟩ : syracuseStep 715603 = 1073405) B1073405
theorem B1076051 : Blo 714321 1076051 := bstep (se 1 (by rfl) ⟨807038, by rfl⟩ : syracuseStep 1076051 = 1614077) B1614077
theorem B2288483 : Blo 714321 2288483 := bstep (se 1 (by rfl) ⟨1716362, by rfl⟩ : syracuseStep 2288483 = 3432725) B3432725
theorem B715619 : Blo 714321 715619 := bstep (se 1 (by rfl) ⟨536714, by rfl⟩ : syracuseStep 715619 = 1073429) B1073429
theorem B1076081 : Blo 714321 1076081 := bstep (se 2 (by rfl) ⟨403530, by rfl⟩ : syracuseStep 1076081 = 807061) B807061
theorem B715635 : Blo 714321 715635 := bstep (se 1 (by rfl) ⟨536726, by rfl⟩ : syracuseStep 715635 = 1073453) B1073453
theorem B715651 : Blo 714321 715651 := bstep (se 1 (by rfl) ⟨536738, by rfl⟩ : syracuseStep 715651 = 1073477) B1073477
theorem B1076099 : Blo 714321 1076099 := bstep (se 1 (by rfl) ⟨807074, by rfl⟩ : syracuseStep 1076099 = 1614149) B1614149
theorem B715667 : Blo 714321 715667 := bstep (se 1 (by rfl) ⟨536750, by rfl⟩ : syracuseStep 715667 = 1073501) B1073501
theorem B1076129 : Blo 714321 1076129 := bstep (se 2 (by rfl) ⟨403548, by rfl⟩ : syracuseStep 1076129 = 807097) B807097
theorem B715683 : Blo 714321 715683 := bstep (se 1 (by rfl) ⟨536762, by rfl⟩ : syracuseStep 715683 = 1073525) B1073525
theorem B1207217 : Blo 714321 1207217 := bstep (se 2 (by rfl) ⟨452706, by rfl⟩ : syracuseStep 1207217 = 905413) B905413
theorem B715699 : Blo 714321 715699 := bstep (se 1 (by rfl) ⟨536774, by rfl⟩ : syracuseStep 715699 = 1073549) B1073549
theorem B1076147 : Blo 714321 1076147 := bstep (se 1 (by rfl) ⟨807110, by rfl⟩ : syracuseStep 1076147 = 1614221) B1614221
theorem B715715 : Blo 714321 715715 := bstep (se 1 (by rfl) ⟨536786, by rfl⟩ : syracuseStep 715715 = 1073573) B1073573
theorem B1076177 : Blo 714321 1076177 := bstep (se 2 (by rfl) ⟨403566, by rfl⟩ : syracuseStep 1076177 = 807133) B807133
theorem B715731 : Blo 714321 715731 := bstep (se 1 (by rfl) ⟨536798, by rfl⟩ : syracuseStep 715731 = 1073597) B1073597
theorem B715747 : Blo 714321 715747 := bstep (se 1 (by rfl) ⟨536810, by rfl⟩ : syracuseStep 715747 = 1073621) B1073621
theorem B1076195 : Blo 714321 1076195 := bstep (se 1 (by rfl) ⟨807146, by rfl⟩ : syracuseStep 1076195 = 1614293) B1614293
theorem B715763 : Blo 714321 715763 := bstep (se 1 (by rfl) ⟨536822, by rfl⟩ : syracuseStep 715763 = 1073645) B1073645
theorem B1076225 : Blo 714321 1076225 := bstep (se 2 (by rfl) ⟨403584, by rfl⟩ : syracuseStep 1076225 = 807169) B807169
theorem B715779 : Blo 714321 715779 := bstep (se 1 (by rfl) ⟨536834, by rfl⟩ : syracuseStep 715779 = 1073669) B1073669
theorem B715795 : Blo 714321 715795 := bstep (se 1 (by rfl) ⟨536846, by rfl⟩ : syracuseStep 715795 = 1073693) B1073693
theorem B1076243 : Blo 714321 1076243 := bstep (se 1 (by rfl) ⟨807182, by rfl⟩ : syracuseStep 1076243 = 1614365) B1614365
theorem B715811 : Blo 714321 715811 := bstep (se 1 (by rfl) ⟨536858, by rfl⟩ : syracuseStep 715811 = 1073717) B1073717
theorem B1207345 : Blo 714321 1207345 := bstep (se 2 (by rfl) ⟨452754, by rfl⟩ : syracuseStep 1207345 = 905509) B905509
theorem B1076273 : Blo 714321 1076273 := bstep (se 2 (by rfl) ⟨403602, by rfl⟩ : syracuseStep 1076273 = 807205) B807205
theorem B715827 : Blo 714321 715827 := bstep (se 1 (by rfl) ⟨536870, by rfl⟩ : syracuseStep 715827 = 1073741) B1073741
theorem B715843 : Blo 714321 715843 := bstep (se 1 (by rfl) ⟨536882, by rfl⟩ : syracuseStep 715843 = 1073765) B1073765
theorem B1076291 : Blo 714321 1076291 := bstep (se 1 (by rfl) ⟨807218, by rfl⟩ : syracuseStep 1076291 = 1614437) B1614437
theorem B2419793 : Blo 714321 2419793 := bstep (se 2 (by rfl) ⟨907422, by rfl⟩ : syracuseStep 2419793 = 1814845) B1814845
theorem B1207379 : Blo 714321 1207379 := bstep (se 1 (by rfl) ⟨905534, by rfl⟩ : syracuseStep 1207379 = 1811069) B1811069
theorem B715859 : Blo 714321 715859 := bstep (se 1 (by rfl) ⟨536894, by rfl⟩ : syracuseStep 715859 = 1073789) B1073789
theorem B1076321 : Blo 714321 1076321 := bstep (se 2 (by rfl) ⟨403620, by rfl⟩ : syracuseStep 1076321 = 807241) B807241
theorem B715875 : Blo 714321 715875 := bstep (se 1 (by rfl) ⟨536906, by rfl⟩ : syracuseStep 715875 = 1073813) B1073813
theorem B715891 : Blo 714321 715891 := bstep (se 1 (by rfl) ⟨536918, by rfl⟩ : syracuseStep 715891 = 1073837) B1073837
theorem B1076339 : Blo 714321 1076339 := bstep (se 1 (by rfl) ⟨807254, by rfl⟩ : syracuseStep 1076339 = 1614509) B1614509
theorem B715907 : Blo 714321 715907 := bstep (se 1 (by rfl) ⟨536930, by rfl⟩ : syracuseStep 715907 = 1073861) B1073861
theorem B1076369 : Blo 714321 1076369 := bstep (se 2 (by rfl) ⟨403638, by rfl⟩ : syracuseStep 1076369 = 807277) B807277
theorem B715923 : Blo 714321 715923 := bstep (se 1 (by rfl) ⟨536942, by rfl⟩ : syracuseStep 715923 = 1073885) B1073885
theorem B715939 : Blo 714321 715939 := bstep (se 1 (by rfl) ⟨536954, by rfl⟩ : syracuseStep 715939 = 1073909) B1073909
theorem B1076387 : Blo 714321 1076387 := bstep (se 1 (by rfl) ⟨807290, by rfl⟩ : syracuseStep 1076387 = 1614581) B1614581
theorem B4091057 : Blo 714321 4091057 := bstep (se 2 (by rfl) ⟨1534146, by rfl⟩ : syracuseStep 4091057 = 3068293) B3068293
theorem B715955 : Blo 714321 715955 := bstep (se 1 (by rfl) ⟨536966, by rfl⟩ : syracuseStep 715955 = 1073933) B1073933
theorem B1076417 : Blo 714321 1076417 := bstep (se 2 (by rfl) ⟨403656, by rfl⟩ : syracuseStep 1076417 = 807313) B807313
theorem B715971 : Blo 714321 715971 := bstep (se 1 (by rfl) ⟨536978, by rfl⟩ : syracuseStep 715971 = 1073957) B1073957
theorem B1207507 : Blo 714321 1207507 := bstep (se 1 (by rfl) ⟨905630, by rfl⟩ : syracuseStep 1207507 = 1811261) B1811261
theorem B715987 : Blo 714321 715987 := bstep (se 1 (by rfl) ⟨536990, by rfl⟩ : syracuseStep 715987 = 1073981) B1073981
theorem B1076435 : Blo 714321 1076435 := bstep (se 1 (by rfl) ⟨807326, by rfl⟩ : syracuseStep 1076435 = 1614653) B1614653
theorem B716003 : Blo 714321 716003 := bstep (se 1 (by rfl) ⟨537002, by rfl⟩ : syracuseStep 716003 = 1074005) B1074005
theorem B13102307 : Blo 714321 13102307 := bstep (se 1 (by rfl) ⟨9826730, by rfl⟩ : syracuseStep 13102307 = 19653461) B19653461
theorem B1076465 : Blo 714321 1076465 := bstep (se 2 (by rfl) ⟨403674, by rfl⟩ : syracuseStep 1076465 = 807349) B807349
theorem B716019 : Blo 714321 716019 := bstep (se 1 (by rfl) ⟨537014, by rfl⟩ : syracuseStep 716019 = 1074029) B1074029
theorem B716035 : Blo 714321 716035 := bstep (se 1 (by rfl) ⟨537026, by rfl⟩ : syracuseStep 716035 = 1074053) B1074053
theorem B1076483 : Blo 714321 1076483 := bstep (se 1 (by rfl) ⟨807362, by rfl⟩ : syracuseStep 1076483 = 1614725) B1614725
theorem B716051 : Blo 714321 716051 := bstep (se 1 (by rfl) ⟨537038, by rfl⟩ : syracuseStep 716051 = 1074077) B1074077
theorem B1076513 : Blo 714321 1076513 := bstep (se 2 (by rfl) ⟨403692, by rfl⟩ : syracuseStep 1076513 = 807385) B807385
theorem B716067 : Blo 714321 716067 := bstep (se 1 (by rfl) ⟨537050, by rfl⟩ : syracuseStep 716067 = 1074101) B1074101
theorem B716083 : Blo 714321 716083 := bstep (se 1 (by rfl) ⟨537062, by rfl⟩ : syracuseStep 716083 = 1074125) B1074125
theorem B1076531 : Blo 714321 1076531 := bstep (se 1 (by rfl) ⟨807398, by rfl⟩ : syracuseStep 1076531 = 1614797) B1614797
theorem B716099 : Blo 714321 716099 := bstep (se 1 (by rfl) ⟨537074, by rfl⟩ : syracuseStep 716099 = 1074149) B1074149
theorem B1076561 : Blo 714321 1076561 := bstep (se 2 (by rfl) ⟨403710, by rfl⟩ : syracuseStep 1076561 = 807421) B807421
theorem B716115 : Blo 714321 716115 := bstep (se 1 (by rfl) ⟨537086, by rfl⟩ : syracuseStep 716115 = 1074173) B1074173
theorem B1207649 : Blo 714321 1207649 := bstep (se 2 (by rfl) ⟨452868, by rfl⟩ : syracuseStep 1207649 = 905737) B905737
theorem B716131 : Blo 714321 716131 := bstep (se 1 (by rfl) ⟨537098, by rfl⟩ : syracuseStep 716131 = 1074197) B1074197
theorem B1076579 : Blo 714321 1076579 := bstep (se 1 (by rfl) ⟨807434, by rfl⟩ : syracuseStep 1076579 = 1614869) B1614869
theorem B13036913 : Blo 714321 13036913 := bstep (se 2 (by rfl) ⟨4888842, by rfl⟩ : syracuseStep 13036913 = 9777685) B9777685
theorem B716147 : Blo 714321 716147 := bstep (se 1 (by rfl) ⟨537110, by rfl⟩ : syracuseStep 716147 = 1074221) B1074221
theorem B1076609 : Blo 714321 1076609 := bstep (se 2 (by rfl) ⟨403728, by rfl⟩ : syracuseStep 1076609 = 807457) B807457
theorem B716163 : Blo 714321 716163 := bstep (se 1 (by rfl) ⟨537122, by rfl⟩ : syracuseStep 716163 = 1074245) B1074245
theorem B3632525 : Blo 714321 3632525 := bstep (se 3 (by rfl) ⟨681098, by rfl⟩ : syracuseStep 3632525 = 1362197) B1362197
theorem B716179 : Blo 714321 716179 := bstep (se 1 (by rfl) ⟨537134, by rfl⟩ : syracuseStep 716179 = 1074269) B1074269
theorem B1076627 : Blo 714321 1076627 := bstep (se 1 (by rfl) ⟨807470, by rfl⟩ : syracuseStep 1076627 = 1614941) B1614941
theorem B716195 : Blo 714321 716195 := bstep (se 1 (by rfl) ⟨537146, by rfl⟩ : syracuseStep 716195 = 1074293) B1074293
theorem B1076657 : Blo 714321 1076657 := bstep (se 2 (by rfl) ⟨403746, by rfl⟩ : syracuseStep 1076657 = 807493) B807493
theorem B716211 : Blo 714321 716211 := bstep (se 1 (by rfl) ⟨537158, by rfl⟩ : syracuseStep 716211 = 1074317) B1074317
theorem B716227 : Blo 714321 716227 := bstep (se 1 (by rfl) ⟨537170, by rfl⟩ : syracuseStep 716227 = 1074341) B1074341
theorem B1076675 : Blo 714321 1076675 := bstep (se 1 (by rfl) ⟨807506, by rfl⟩ : syracuseStep 1076675 = 1615013) B1615013
theorem B716243 : Blo 714321 716243 := bstep (se 1 (by rfl) ⟨537182, by rfl⟩ : syracuseStep 716243 = 1074365) B1074365
theorem B1207777 : Blo 714321 1207777 := bstep (se 2 (by rfl) ⟨452916, by rfl⟩ : syracuseStep 1207777 = 905833) B905833
theorem B716259 : Blo 714321 716259 := bstep (se 1 (by rfl) ⟨537194, by rfl⟩ : syracuseStep 716259 = 1074389) B1074389
theorem B1076705 : Blo 714321 1076705 := bstep (se 2 (by rfl) ⟨403764, by rfl⟩ : syracuseStep 1076705 = 807529) B807529
theorem B716275 : Blo 714321 716275 := bstep (se 1 (by rfl) ⟨537206, by rfl⟩ : syracuseStep 716275 = 1074413) B1074413
theorem B1076723 : Blo 714321 1076723 := bstep (se 1 (by rfl) ⟨807542, by rfl⟩ : syracuseStep 1076723 = 1615085) B1615085
theorem B1207811 : Blo 714321 1207811 := bstep (se 1 (by rfl) ⟨905858, by rfl⟩ : syracuseStep 1207811 = 1811717) B1811717
theorem B716291 : Blo 714321 716291 := bstep (se 1 (by rfl) ⟨537218, by rfl⟩ : syracuseStep 716291 = 1074437) B1074437
theorem B1076753 : Blo 714321 1076753 := bstep (se 2 (by rfl) ⟨403782, by rfl⟩ : syracuseStep 1076753 = 807565) B807565
theorem B716307 : Blo 714321 716307 := bstep (se 1 (by rfl) ⟨537230, by rfl⟩ : syracuseStep 716307 = 1074461) B1074461
theorem B716323 : Blo 714321 716323 := bstep (se 1 (by rfl) ⟨537242, by rfl⟩ : syracuseStep 716323 = 1074485) B1074485
theorem B1076771 : Blo 714321 1076771 := bstep (se 1 (by rfl) ⟨807578, by rfl⟩ : syracuseStep 1076771 = 1615157) B1615157
theorem B716339 : Blo 714321 716339 := bstep (se 1 (by rfl) ⟨537254, by rfl⟩ : syracuseStep 716339 = 1074509) B1074509
theorem B1076801 : Blo 714321 1076801 := bstep (se 2 (by rfl) ⟨403800, by rfl⟩ : syracuseStep 1076801 = 807601) B807601
theorem B716355 : Blo 714321 716355 := bstep (se 1 (by rfl) ⟨537266, by rfl⟩ : syracuseStep 716355 = 1074533) B1074533
theorem B716371 : Blo 714321 716371 := bstep (se 1 (by rfl) ⟨537278, by rfl⟩ : syracuseStep 716371 = 1074557) B1074557
theorem B1076819 : Blo 714321 1076819 := bstep (se 1 (by rfl) ⟨807614, by rfl⟩ : syracuseStep 1076819 = 1615229) B1615229
theorem B716387 : Blo 714321 716387 := bstep (se 1 (by rfl) ⟨537290, by rfl⟩ : syracuseStep 716387 = 1074581) B1074581
theorem B2420333 : Blo 714321 2420333 := bstep (se 3 (by rfl) ⟨453812, by rfl⟩ : syracuseStep 2420333 = 907625) B907625
theorem B1076849 : Blo 714321 1076849 := bstep (se 2 (by rfl) ⟨403818, by rfl⟩ : syracuseStep 1076849 = 807637) B807637
theorem B716403 : Blo 714321 716403 := bstep (se 1 (by rfl) ⟨537302, by rfl⟩ : syracuseStep 716403 = 1074605) B1074605
theorem B1207939 : Blo 714321 1207939 := bstep (se 1 (by rfl) ⟨905954, by rfl⟩ : syracuseStep 1207939 = 1811909) B1811909
theorem B716419 : Blo 714321 716419 := bstep (se 1 (by rfl) ⟨537314, by rfl⟩ : syracuseStep 716419 = 1074629) B1074629
theorem B1076867 : Blo 714321 1076867 := bstep (se 1 (by rfl) ⟨807650, by rfl⟩ : syracuseStep 1076867 = 1615301) B1615301
theorem B716435 : Blo 714321 716435 := bstep (se 1 (by rfl) ⟨537326, by rfl⟩ : syracuseStep 716435 = 1074653) B1074653
theorem B1076897 : Blo 714321 1076897 := bstep (se 2 (by rfl) ⟨403836, by rfl⟩ : syracuseStep 1076897 = 807673) B807673
theorem B716451 : Blo 714321 716451 := bstep (se 1 (by rfl) ⟨537338, by rfl⟩ : syracuseStep 716451 = 1074677) B1074677
theorem B2420387 : Blo 714321 2420387 := bstep (se 1 (by rfl) ⟨1815290, by rfl⟩ : syracuseStep 2420387 = 3630581) B3630581
theorem B2289329 : Blo 714321 2289329 := bstep (se 2 (by rfl) ⟨858498, by rfl⟩ : syracuseStep 2289329 = 1716997) B1716997
theorem B978611 : Blo 714321 978611 := bstep (se 1 (by rfl) ⟨733958, by rfl⟩ : syracuseStep 978611 = 1467917) B1467917
theorem B716467 : Blo 714321 716467 := bstep (se 1 (by rfl) ⟨537350, by rfl⟩ : syracuseStep 716467 = 1074701) B1074701
theorem B1076915 : Blo 714321 1076915 := bstep (se 1 (by rfl) ⟨807686, by rfl⟩ : syracuseStep 1076915 = 1615373) B1615373
theorem B716483 : Blo 714321 716483 := bstep (se 1 (by rfl) ⟨537362, by rfl⟩ : syracuseStep 716483 = 1074725) B1074725
theorem B1076945 : Blo 714321 1076945 := bstep (se 2 (by rfl) ⟨403854, by rfl⟩ : syracuseStep 1076945 = 807709) B807709
theorem B716499 : Blo 714321 716499 := bstep (se 1 (by rfl) ⟨537374, by rfl⟩ : syracuseStep 716499 = 1074749) B1074749
theorem B2289379 : Blo 714321 2289379 := bstep (se 1 (by rfl) ⟨1717034, by rfl⟩ : syracuseStep 2289379 = 3434069) B3434069
theorem B716515 : Blo 714321 716515 := bstep (se 1 (by rfl) ⟨537386, by rfl⟩ : syracuseStep 716515 = 1074773) B1074773
theorem B1076963 : Blo 714321 1076963 := bstep (se 1 (by rfl) ⟨807722, by rfl⟩ : syracuseStep 1076963 = 1615445) B1615445
theorem B716531 : Blo 714321 716531 := bstep (se 1 (by rfl) ⟨537398, by rfl⟩ : syracuseStep 716531 = 1074797) B1074797
theorem B1076993 : Blo 714321 1076993 := bstep (se 2 (by rfl) ⟨403872, by rfl⟩ : syracuseStep 1076993 = 807745) B807745
theorem B716547 : Blo 714321 716547 := bstep (se 1 (by rfl) ⟨537410, by rfl⟩ : syracuseStep 716547 = 1074821) B1074821
theorem B1208081 : Blo 714321 1208081 := bstep (se 2 (by rfl) ⟨453030, by rfl⟩ : syracuseStep 1208081 = 906061) B906061
theorem B716563 : Blo 714321 716563 := bstep (se 1 (by rfl) ⟨537422, by rfl⟩ : syracuseStep 716563 = 1074845) B1074845
theorem B1077011 : Blo 714321 1077011 := bstep (se 1 (by rfl) ⟨807758, by rfl⟩ : syracuseStep 1077011 = 1615517) B1615517
theorem B716579 : Blo 714321 716579 := bstep (se 1 (by rfl) ⟨537434, by rfl⟩ : syracuseStep 716579 = 1074869) B1074869
theorem B1077041 : Blo 714321 1077041 := bstep (se 2 (by rfl) ⟨403890, by rfl⟩ : syracuseStep 1077041 = 807781) B807781
theorem B716595 : Blo 714321 716595 := bstep (se 1 (by rfl) ⟨537446, by rfl⟩ : syracuseStep 716595 = 1074893) B1074893
theorem B716611 : Blo 714321 716611 := bstep (se 1 (by rfl) ⟨537458, by rfl⟩ : syracuseStep 716611 = 1074917) B1074917
theorem B1077059 : Blo 714321 1077059 := bstep (se 1 (by rfl) ⟨807794, by rfl⟩ : syracuseStep 1077059 = 1615589) B1615589
theorem B716627 : Blo 714321 716627 := bstep (se 1 (by rfl) ⟨537470, by rfl⟩ : syracuseStep 716627 = 1074941) B1074941
theorem B1077089 : Blo 714321 1077089 := bstep (se 2 (by rfl) ⟨403908, by rfl⟩ : syracuseStep 1077089 = 807817) B807817
theorem B716643 : Blo 714321 716643 := bstep (se 1 (by rfl) ⟨537482, by rfl⟩ : syracuseStep 716643 = 1074965) B1074965
theorem B716659 : Blo 714321 716659 := bstep (se 1 (by rfl) ⟨537494, by rfl⟩ : syracuseStep 716659 = 1074989) B1074989
theorem B1077107 : Blo 714321 1077107 := bstep (se 1 (by rfl) ⟨807830, by rfl⟩ : syracuseStep 1077107 = 1615661) B1615661
theorem B716675 : Blo 714321 716675 := bstep (se 1 (by rfl) ⟨537506, by rfl⟩ : syracuseStep 716675 = 1075013) B1075013
theorem B1208209 : Blo 714321 1208209 := bstep (se 2 (by rfl) ⟨453078, by rfl⟩ : syracuseStep 1208209 = 906157) B906157
theorem B1077137 : Blo 714321 1077137 := bstep (se 2 (by rfl) ⟨403926, by rfl⟩ : syracuseStep 1077137 = 807853) B807853
theorem B716691 : Blo 714321 716691 := bstep (se 1 (by rfl) ⟨537518, by rfl⟩ : syracuseStep 716691 = 1075037) B1075037
theorem B716707 : Blo 714321 716707 := bstep (se 1 (by rfl) ⟨537530, by rfl⟩ : syracuseStep 716707 = 1075061) B1075061
theorem B1077155 : Blo 714321 1077155 := bstep (se 1 (by rfl) ⟨807866, by rfl⟩ : syracuseStep 1077155 = 1615733) B1615733
theorem B2420657 : Blo 714321 2420657 := bstep (se 2 (by rfl) ⟨907746, by rfl⟩ : syracuseStep 2420657 = 1815493) B1815493
theorem B1208243 : Blo 714321 1208243 := bstep (se 1 (by rfl) ⟨906182, by rfl⟩ : syracuseStep 1208243 = 1812365) B1812365
theorem B716723 : Blo 714321 716723 := bstep (se 1 (by rfl) ⟨537542, by rfl⟩ : syracuseStep 716723 = 1075085) B1075085
theorem B1077185 : Blo 714321 1077185 := bstep (se 2 (by rfl) ⟨403944, by rfl⟩ : syracuseStep 1077185 = 807889) B807889
theorem B716739 : Blo 714321 716739 := bstep (se 1 (by rfl) ⟨537554, by rfl⟩ : syracuseStep 716739 = 1075109) B1075109
theorem B716755 : Blo 714321 716755 := bstep (se 1 (by rfl) ⟨537566, by rfl⟩ : syracuseStep 716755 = 1075133) B1075133
theorem B1077203 : Blo 714321 1077203 := bstep (se 1 (by rfl) ⟨807902, by rfl⟩ : syracuseStep 1077203 = 1615805) B1615805
theorem B1241057 : Blo 714321 1241057 := bstep (se 2 (by rfl) ⟨465396, by rfl⟩ : syracuseStep 1241057 = 930793) B930793
theorem B716771 : Blo 714321 716771 := bstep (se 1 (by rfl) ⟨537578, by rfl⟩ : syracuseStep 716771 = 1075157) B1075157
theorem B1077233 : Blo 714321 1077233 := bstep (se 2 (by rfl) ⟨403962, by rfl⟩ : syracuseStep 1077233 = 807925) B807925
theorem B716787 : Blo 714321 716787 := bstep (se 1 (by rfl) ⟨537590, by rfl⟩ : syracuseStep 716787 = 1075181) B1075181
theorem B716803 : Blo 714321 716803 := bstep (se 1 (by rfl) ⟨537602, by rfl⟩ : syracuseStep 716803 = 1075205) B1075205
theorem B1077251 : Blo 714321 1077251 := bstep (se 1 (by rfl) ⟨807938, by rfl⟩ : syracuseStep 1077251 = 1615877) B1615877
theorem B716819 : Blo 714321 716819 := bstep (se 1 (by rfl) ⟨537614, by rfl⟩ : syracuseStep 716819 = 1075229) B1075229
theorem B1077281 : Blo 714321 1077281 := bstep (se 2 (by rfl) ⟨403980, by rfl⟩ : syracuseStep 1077281 = 807961) B807961
theorem B716835 : Blo 714321 716835 := bstep (se 1 (by rfl) ⟨537626, by rfl⟩ : syracuseStep 716835 = 1075253) B1075253
theorem B1208371 : Blo 714321 1208371 := bstep (se 1 (by rfl) ⟨906278, by rfl⟩ : syracuseStep 1208371 = 1812557) B1812557
theorem B716851 : Blo 714321 716851 := bstep (se 1 (by rfl) ⟨537638, by rfl⟩ : syracuseStep 716851 = 1075277) B1075277
theorem B1077299 : Blo 714321 1077299 := bstep (se 1 (by rfl) ⟨807974, by rfl⟩ : syracuseStep 1077299 = 1615949) B1615949
theorem B716867 : Blo 714321 716867 := bstep (se 1 (by rfl) ⟨537650, by rfl⟩ : syracuseStep 716867 = 1075301) B1075301
theorem B1077329 : Blo 714321 1077329 := bstep (se 2 (by rfl) ⟨403998, by rfl⟩ : syracuseStep 1077329 = 807997) B807997
theorem B716883 : Blo 714321 716883 := bstep (se 1 (by rfl) ⟨537662, by rfl⟩ : syracuseStep 716883 = 1075325) B1075325
theorem B716899 : Blo 714321 716899 := bstep (se 1 (by rfl) ⟨537674, by rfl⟩ : syracuseStep 716899 = 1075349) B1075349
theorem B1077347 : Blo 714321 1077347 := bstep (se 1 (by rfl) ⟨808010, by rfl⟩ : syracuseStep 1077347 = 1616021) B1616021
theorem B716915 : Blo 714321 716915 := bstep (se 1 (by rfl) ⟨537686, by rfl⟩ : syracuseStep 716915 = 1075373) B1075373
theorem B1077377 : Blo 714321 1077377 := bstep (se 2 (by rfl) ⟨404016, by rfl⟩ : syracuseStep 1077377 = 808033) B808033
theorem B716931 : Blo 714321 716931 := bstep (se 1 (by rfl) ⟨537698, by rfl⟩ : syracuseStep 716931 = 1075397) B1075397
theorem B716947 : Blo 714321 716947 := bstep (se 1 (by rfl) ⟨537710, by rfl⟩ : syracuseStep 716947 = 1075421) B1075421
theorem B1077395 : Blo 714321 1077395 := bstep (se 1 (by rfl) ⟨808046, by rfl⟩ : syracuseStep 1077395 = 1616093) B1616093
theorem B716963 : Blo 714321 716963 := bstep (se 1 (by rfl) ⟨537722, by rfl⟩ : syracuseStep 716963 = 1075445) B1075445
theorem B1077425 : Blo 714321 1077425 := bstep (se 2 (by rfl) ⟨404034, by rfl⟩ : syracuseStep 1077425 = 808069) B808069
theorem B716979 : Blo 714321 716979 := bstep (se 1 (by rfl) ⟨537734, by rfl⟩ : syracuseStep 716979 = 1075469) B1075469
theorem B1208513 : Blo 714321 1208513 := bstep (se 2 (by rfl) ⟨453192, by rfl⟩ : syracuseStep 1208513 = 906385) B906385
theorem B716995 : Blo 714321 716995 := bstep (se 1 (by rfl) ⟨537746, by rfl⟩ : syracuseStep 716995 = 1075493) B1075493
theorem B1077443 : Blo 714321 1077443 := bstep (se 1 (by rfl) ⟨808082, by rfl⟩ : syracuseStep 1077443 = 1616165) B1616165
theorem B717011 : Blo 714321 717011 := bstep (se 1 (by rfl) ⟨537758, by rfl⟩ : syracuseStep 717011 = 1075517) B1075517
theorem B1077473 : Blo 714321 1077473 := bstep (se 2 (by rfl) ⟨404052, by rfl⟩ : syracuseStep 1077473 = 808105) B808105
theorem B2715875 : Blo 714321 2715875 := bstep (se 1 (by rfl) ⟨2036906, by rfl⟩ : syracuseStep 2715875 = 4073813) B4073813
theorem B717027 : Blo 714321 717027 := bstep (se 1 (by rfl) ⟨537770, by rfl⟩ : syracuseStep 717027 = 1075541) B1075541
theorem B2355437 : Blo 714321 2355437 := bstep (se 3 (by rfl) ⟨441644, by rfl⟩ : syracuseStep 2355437 = 883289) B883289
theorem B2715889 : Blo 714321 2715889 := bstep (se 2 (by rfl) ⟨1018458, by rfl⟩ : syracuseStep 2715889 = 2036917) B2036917
theorem B717043 : Blo 714321 717043 := bstep (se 1 (by rfl) ⟨537782, by rfl⟩ : syracuseStep 717043 = 1075565) B1075565
theorem B717059 : Blo 714321 717059 := bstep (se 1 (by rfl) ⟨537794, by rfl⟩ : syracuseStep 717059 = 1075589) B1075589
theorem B717075 : Blo 714321 717075 := bstep (se 1 (by rfl) ⟨537806, by rfl⟩ : syracuseStep 717075 = 1075613) B1075613
theorem B717091 : Blo 714321 717091 := bstep (se 1 (by rfl) ⟨537818, by rfl⟩ : syracuseStep 717091 = 1075637) B1075637
theorem B717107 : Blo 714321 717107 := bstep (se 1 (by rfl) ⟨537830, by rfl⟩ : syracuseStep 717107 = 1075661) B1075661
theorem B1208641 : Blo 714321 1208641 := bstep (se 2 (by rfl) ⟨453240, by rfl⟩ : syracuseStep 1208641 = 906481) B906481
theorem B717123 : Blo 714321 717123 := bstep (se 1 (by rfl) ⟨537842, by rfl⟩ : syracuseStep 717123 = 1075685) B1075685
theorem B717139 : Blo 714321 717139 := bstep (se 1 (by rfl) ⟨537854, by rfl⟩ : syracuseStep 717139 = 1075709) B1075709
theorem B1208675 : Blo 714321 1208675 := bstep (se 1 (by rfl) ⟨906506, by rfl⟩ : syracuseStep 1208675 = 1813013) B1813013
theorem B717155 : Blo 714321 717155 := bstep (se 1 (by rfl) ⟨537866, by rfl⟩ : syracuseStep 717155 = 1075733) B1075733
theorem B2355569 : Blo 714321 2355569 := bstep (se 2 (by rfl) ⟨883338, by rfl⟩ : syracuseStep 2355569 = 1766677) B1766677
theorem B717171 : Blo 714321 717171 := bstep (se 1 (by rfl) ⟨537878, by rfl⟩ : syracuseStep 717171 = 1075757) B1075757
theorem B717187 : Blo 714321 717187 := bstep (se 1 (by rfl) ⟨537890, by rfl⟩ : syracuseStep 717187 = 1075781) B1075781
theorem B717203 : Blo 714321 717203 := bstep (se 1 (by rfl) ⟨537902, by rfl⟩ : syracuseStep 717203 = 1075805) B1075805
theorem B717219 : Blo 714321 717219 := bstep (se 1 (by rfl) ⟨537914, by rfl⟩ : syracuseStep 717219 = 1075829) B1075829
theorem B2585009 : Blo 714321 2585009 := bstep (se 2 (by rfl) ⟨969378, by rfl⟩ : syracuseStep 2585009 = 1938757) B1938757
theorem B717235 : Blo 714321 717235 := bstep (se 1 (by rfl) ⟨537926, by rfl⟩ : syracuseStep 717235 = 1075853) B1075853
theorem B717251 : Blo 714321 717251 := bstep (se 1 (by rfl) ⟨537938, by rfl⟩ : syracuseStep 717251 = 1075877) B1075877
theorem B2421197 : Blo 714321 2421197 := bstep (se 3 (by rfl) ⟨453974, by rfl⟩ : syracuseStep 2421197 = 907949) B907949
theorem B717267 : Blo 714321 717267 := bstep (se 1 (by rfl) ⟨537950, by rfl⟩ : syracuseStep 717267 = 1075901) B1075901
theorem B1208803 : Blo 714321 1208803 := bstep (se 1 (by rfl) ⟨906602, by rfl⟩ : syracuseStep 1208803 = 1813205) B1813205
theorem B717283 : Blo 714321 717283 := bstep (se 1 (by rfl) ⟨537962, by rfl⟩ : syracuseStep 717283 = 1075925) B1075925
theorem B717299 : Blo 714321 717299 := bstep (se 1 (by rfl) ⟨537974, by rfl⟩ : syracuseStep 717299 = 1075949) B1075949
theorem B717315 : Blo 714321 717315 := bstep (se 1 (by rfl) ⟨537986, by rfl⟩ : syracuseStep 717315 = 1075973) B1075973
theorem B2421251 : Blo 714321 2421251 := bstep (se 1 (by rfl) ⟨1815938, by rfl⟩ : syracuseStep 2421251 = 3631877) B3631877
theorem B717331 : Blo 714321 717331 := bstep (se 1 (by rfl) ⟨537998, by rfl⟩ : syracuseStep 717331 = 1075997) B1075997
theorem B717347 : Blo 714321 717347 := bstep (se 1 (by rfl) ⟨538010, by rfl⟩ : syracuseStep 717347 = 1076021) B1076021
theorem B717363 : Blo 714321 717363 := bstep (se 1 (by rfl) ⟨538022, by rfl⟩ : syracuseStep 717363 = 1076045) B1076045
theorem B717379 : Blo 714321 717379 := bstep (se 1 (by rfl) ⟨538034, by rfl⟩ : syracuseStep 717379 = 1076069) B1076069
theorem B717395 : Blo 714321 717395 := bstep (se 1 (by rfl) ⟨538046, by rfl⟩ : syracuseStep 717395 = 1076093) B1076093
theorem B717411 : Blo 714321 717411 := bstep (se 1 (by rfl) ⟨538058, by rfl⟩ : syracuseStep 717411 = 1076117) B1076117
theorem B1208945 : Blo 714321 1208945 := bstep (se 2 (by rfl) ⟨453354, by rfl⟩ : syracuseStep 1208945 = 906709) B906709
theorem B11629169 : Blo 714321 11629169 := bstep (se 2 (by rfl) ⟨4360938, by rfl⟩ : syracuseStep 11629169 = 8721877) B8721877
theorem B717427 : Blo 714321 717427 := bstep (se 1 (by rfl) ⟨538070, by rfl⟩ : syracuseStep 717427 = 1076141) B1076141
theorem B717443 : Blo 714321 717443 := bstep (se 1 (by rfl) ⟨538082, by rfl⟩ : syracuseStep 717443 = 1076165) B1076165
theorem B717459 : Blo 714321 717459 := bstep (se 1 (by rfl) ⟨538094, by rfl⟩ : syracuseStep 717459 = 1076189) B1076189
theorem B717475 : Blo 714321 717475 := bstep (se 1 (by rfl) ⟨538106, by rfl⟩ : syracuseStep 717475 = 1076213) B1076213
theorem B717491 : Blo 714321 717491 := bstep (se 1 (by rfl) ⟨538118, by rfl⟩ : syracuseStep 717491 = 1076237) B1076237
theorem B717507 : Blo 714321 717507 := bstep (se 1 (by rfl) ⟨538130, by rfl⟩ : syracuseStep 717507 = 1076261) B1076261
theorem B717523 : Blo 714321 717523 := bstep (se 1 (by rfl) ⟨538142, by rfl⟩ : syracuseStep 717523 = 1076285) B1076285
theorem B717539 : Blo 714321 717539 := bstep (se 1 (by rfl) ⟨538154, by rfl⟩ : syracuseStep 717539 = 1076309) B1076309
theorem B1209073 : Blo 714321 1209073 := bstep (se 2 (by rfl) ⟨453402, by rfl⟩ : syracuseStep 1209073 = 906805) B906805
theorem B717555 : Blo 714321 717555 := bstep (se 1 (by rfl) ⟨538166, by rfl⟩ : syracuseStep 717555 = 1076333) B1076333
theorem B717571 : Blo 714321 717571 := bstep (se 1 (by rfl) ⟨538178, by rfl⟩ : syracuseStep 717571 = 1076357) B1076357
theorem B2585357 : Blo 714321 2585357 := bstep (se 3 (by rfl) ⟨484754, by rfl⟩ : syracuseStep 2585357 = 969509) B969509
theorem B2421521 : Blo 714321 2421521 := bstep (se 2 (by rfl) ⟨908070, by rfl⟩ : syracuseStep 2421521 = 1816141) B1816141
theorem B1209107 : Blo 714321 1209107 := bstep (se 1 (by rfl) ⟨906830, by rfl⟩ : syracuseStep 1209107 = 1813661) B1813661
theorem B717587 : Blo 714321 717587 := bstep (se 1 (by rfl) ⟨538190, by rfl⟩ : syracuseStep 717587 = 1076381) B1076381
theorem B717603 : Blo 714321 717603 := bstep (se 1 (by rfl) ⟨538202, by rfl⟩ : syracuseStep 717603 = 1076405) B1076405
theorem B717619 : Blo 714321 717619 := bstep (se 1 (by rfl) ⟨538214, by rfl⟩ : syracuseStep 717619 = 1076429) B1076429
theorem B717635 : Blo 714321 717635 := bstep (se 1 (by rfl) ⟨538226, by rfl⟩ : syracuseStep 717635 = 1076453) B1076453
theorem B717651 : Blo 714321 717651 := bstep (se 1 (by rfl) ⟨538238, by rfl⟩ : syracuseStep 717651 = 1076477) B1076477
theorem B717667 : Blo 714321 717667 := bstep (se 1 (by rfl) ⟨538250, by rfl⟩ : syracuseStep 717667 = 1076501) B1076501
theorem B717683 : Blo 714321 717683 := bstep (se 1 (by rfl) ⟨538262, by rfl⟩ : syracuseStep 717683 = 1076525) B1076525
theorem B717699 : Blo 714321 717699 := bstep (se 1 (by rfl) ⟨538274, by rfl⟩ : syracuseStep 717699 = 1076549) B1076549
theorem B1209235 : Blo 714321 1209235 := bstep (se 1 (by rfl) ⟨906926, by rfl⟩ : syracuseStep 1209235 = 1813853) B1813853
theorem B717715 : Blo 714321 717715 := bstep (se 1 (by rfl) ⟨538286, by rfl⟩ : syracuseStep 717715 = 1076573) B1076573
theorem B717731 : Blo 714321 717731 := bstep (se 1 (by rfl) ⟨538298, by rfl⟩ : syracuseStep 717731 = 1076597) B1076597
theorem B2290609 : Blo 714321 2290609 := bstep (se 2 (by rfl) ⟨858978, by rfl⟩ : syracuseStep 2290609 = 1717957) B1717957
theorem B717747 : Blo 714321 717747 := bstep (se 1 (by rfl) ⟨538310, by rfl⟩ : syracuseStep 717747 = 1076621) B1076621
theorem B717763 : Blo 714321 717763 := bstep (se 1 (by rfl) ⟨538322, by rfl⟩ : syracuseStep 717763 = 1076645) B1076645
theorem B4584397 : Blo 714321 4584397 := bstep (se 3 (by rfl) ⟨859574, by rfl⟩ : syracuseStep 4584397 = 1719149) B1719149
theorem B717779 : Blo 714321 717779 := bstep (se 1 (by rfl) ⟨538334, by rfl⟩ : syracuseStep 717779 = 1076669) B1076669
theorem B717795 : Blo 714321 717795 := bstep (se 1 (by rfl) ⟨538346, by rfl⟩ : syracuseStep 717795 = 1076693) B1076693
theorem B717811 : Blo 714321 717811 := bstep (se 1 (by rfl) ⟨538358, by rfl⟩ : syracuseStep 717811 = 1076717) B1076717
theorem B717827 : Blo 714321 717827 := bstep (se 1 (by rfl) ⟨538370, by rfl⟩ : syracuseStep 717827 = 1076741) B1076741
theorem B717843 : Blo 714321 717843 := bstep (se 1 (by rfl) ⟨538382, by rfl⟩ : syracuseStep 717843 = 1076765) B1076765
theorem B1209377 : Blo 714321 1209377 := bstep (se 2 (by rfl) ⟨453516, by rfl⟩ : syracuseStep 1209377 = 907033) B907033
theorem B717859 : Blo 714321 717859 := bstep (se 1 (by rfl) ⟨538394, by rfl⟩ : syracuseStep 717859 = 1076789) B1076789
theorem B717875 : Blo 714321 717875 := bstep (se 1 (by rfl) ⟨538406, by rfl⟩ : syracuseStep 717875 = 1076813) B1076813
theorem B717891 : Blo 714321 717891 := bstep (se 1 (by rfl) ⟨538418, by rfl⟩ : syracuseStep 717891 = 1076837) B1076837
theorem B3667021 : Blo 714321 3667021 := bstep (se 3 (by rfl) ⟨687566, by rfl⟩ : syracuseStep 3667021 = 1375133) B1375133
theorem B717907 : Blo 714321 717907 := bstep (se 1 (by rfl) ⟨538430, by rfl⟩ : syracuseStep 717907 = 1076861) B1076861
theorem B717923 : Blo 714321 717923 := bstep (se 1 (by rfl) ⟨538442, by rfl⟩ : syracuseStep 717923 = 1076885) B1076885
theorem B717939 : Blo 714321 717939 := bstep (se 1 (by rfl) ⟨538454, by rfl⟩ : syracuseStep 717939 = 1076909) B1076909
theorem B717955 : Blo 714321 717955 := bstep (se 1 (by rfl) ⟨538466, by rfl⟩ : syracuseStep 717955 = 1076933) B1076933
theorem B717971 : Blo 714321 717971 := bstep (se 1 (by rfl) ⟨538478, by rfl⟩ : syracuseStep 717971 = 1076957) B1076957
theorem B1209505 : Blo 714321 1209505 := bstep (se 2 (by rfl) ⟨453564, by rfl⟩ : syracuseStep 1209505 = 907129) B907129
theorem B717987 : Blo 714321 717987 := bstep (se 1 (by rfl) ⟨538490, by rfl⟩ : syracuseStep 717987 = 1076981) B1076981
theorem B718003 : Blo 714321 718003 := bstep (se 1 (by rfl) ⟨538502, by rfl⟩ : syracuseStep 718003 = 1077005) B1077005
theorem B1209539 : Blo 714321 1209539 := bstep (se 1 (by rfl) ⟨907154, by rfl⟩ : syracuseStep 1209539 = 1814309) B1814309
theorem B718019 : Blo 714321 718019 := bstep (se 1 (by rfl) ⟨538514, by rfl⟩ : syracuseStep 718019 = 1077029) B1077029
theorem B718035 : Blo 714321 718035 := bstep (se 1 (by rfl) ⟨538526, by rfl⟩ : syracuseStep 718035 = 1077053) B1077053
theorem B718051 : Blo 714321 718051 := bstep (se 1 (by rfl) ⟨538538, by rfl⟩ : syracuseStep 718051 = 1077077) B1077077
theorem B718067 : Blo 714321 718067 := bstep (se 1 (by rfl) ⟨538550, by rfl⟩ : syracuseStep 718067 = 1077101) B1077101
theorem B718083 : Blo 714321 718083 := bstep (se 1 (by rfl) ⟨538562, by rfl⟩ : syracuseStep 718083 = 1077125) B1077125
theorem B718099 : Blo 714321 718099 := bstep (se 1 (by rfl) ⟨538574, by rfl⟩ : syracuseStep 718099 = 1077149) B1077149
theorem B718115 : Blo 714321 718115 := bstep (se 1 (by rfl) ⟨538586, by rfl⟩ : syracuseStep 718115 = 1077173) B1077173
theorem B2422061 : Blo 714321 2422061 := bstep (se 3 (by rfl) ⟨454136, by rfl⟩ : syracuseStep 2422061 = 908273) B908273
theorem B1045811 : Blo 714321 1045811 := bstep (se 1 (by rfl) ⟨784358, by rfl⟩ : syracuseStep 1045811 = 1568717) B1568717
theorem B718131 : Blo 714321 718131 := bstep (se 1 (by rfl) ⟨538598, by rfl⟩ : syracuseStep 718131 = 1077197) B1077197
theorem B1209667 : Blo 714321 1209667 := bstep (se 1 (by rfl) ⟨907250, by rfl⟩ : syracuseStep 1209667 = 1814501) B1814501
theorem B718147 : Blo 714321 718147 := bstep (se 1 (by rfl) ⟨538610, by rfl⟩ : syracuseStep 718147 = 1077221) B1077221
theorem B718163 : Blo 714321 718163 := bstep (se 1 (by rfl) ⟨538622, by rfl⟩ : syracuseStep 718163 = 1077245) B1077245
theorem B2422115 : Blo 714321 2422115 := bstep (se 1 (by rfl) ⟨1816586, by rfl⟩ : syracuseStep 2422115 = 3633173) B3633173
theorem B718179 : Blo 714321 718179 := bstep (se 1 (by rfl) ⟨538634, by rfl⟩ : syracuseStep 718179 = 1077269) B1077269
theorem B718195 : Blo 714321 718195 := bstep (se 1 (by rfl) ⟨538646, by rfl⟩ : syracuseStep 718195 = 1077293) B1077293
theorem B718211 : Blo 714321 718211 := bstep (se 1 (by rfl) ⟨538658, by rfl⟩ : syracuseStep 718211 = 1077317) B1077317
theorem B718227 : Blo 714321 718227 := bstep (se 1 (by rfl) ⟨538670, by rfl⟩ : syracuseStep 718227 = 1077341) B1077341
theorem B718243 : Blo 714321 718243 := bstep (se 1 (by rfl) ⟨538682, by rfl⟩ : syracuseStep 718243 = 1077365) B1077365
theorem B718259 : Blo 714321 718259 := bstep (se 1 (by rfl) ⟨538694, by rfl⟩ : syracuseStep 718259 = 1077389) B1077389
theorem B718275 : Blo 714321 718275 := bstep (se 1 (by rfl) ⟨538706, by rfl⟩ : syracuseStep 718275 = 1077413) B1077413
theorem B1209809 : Blo 714321 1209809 := bstep (se 2 (by rfl) ⟨453678, by rfl⟩ : syracuseStep 1209809 = 907357) B907357
theorem B718291 : Blo 714321 718291 := bstep (se 1 (by rfl) ⟨538718, by rfl⟩ : syracuseStep 718291 = 1077437) B1077437
theorem B718307 : Blo 714321 718307 := bstep (se 1 (by rfl) ⟨538730, by rfl⟩ : syracuseStep 718307 = 1077461) B1077461
theorem B1963565 : Blo 714321 1963565 := bstep (se 3 (by rfl) ⟨368168, by rfl⟩ : syracuseStep 1963565 = 736337) B736337
theorem B1209937 : Blo 714321 1209937 := bstep (se 2 (by rfl) ⟨453726, by rfl⟩ : syracuseStep 1209937 = 907453) B907453
theorem B2422385 : Blo 714321 2422385 := bstep (se 2 (by rfl) ⟨908394, by rfl⟩ : syracuseStep 2422385 = 1816789) B1816789
theorem B1209971 : Blo 714321 1209971 := bstep (se 1 (by rfl) ⟨907478, by rfl⟩ : syracuseStep 1209971 = 1814957) B1814957
theorem B2717347 : Blo 714321 2717347 := bstep (se 1 (by rfl) ⟨2038010, by rfl⟩ : syracuseStep 2717347 = 4076021) B4076021
theorem B1210099 : Blo 714321 1210099 := bstep (se 1 (by rfl) ⟨907574, by rfl⟩ : syracuseStep 1210099 = 1815149) B1815149
theorem B2324305 : Blo 714321 2324305 := bstep (se 2 (by rfl) ⟨871614, by rfl⟩ : syracuseStep 2324305 = 1743229) B1743229
theorem B1210241 : Blo 714321 1210241 := bstep (se 2 (by rfl) ⟨453840, by rfl⟩ : syracuseStep 1210241 = 907681) B907681
theorem B1308593 : Blo 714321 1308593 := bstep (se 2 (by rfl) ⟨490722, by rfl⟩ : syracuseStep 1308593 = 981445) B981445
theorem B1210369 : Blo 714321 1210369 := bstep (se 2 (by rfl) ⟨453888, by rfl⟩ : syracuseStep 1210369 = 907777) B907777
theorem B1210403 : Blo 714321 1210403 := bstep (se 1 (by rfl) ⟨907802, by rfl⟩ : syracuseStep 1210403 = 1815605) B1815605
theorem B2291789 : Blo 714321 2291789 := bstep (se 3 (by rfl) ⟨429710, by rfl⟩ : syracuseStep 2291789 = 859421) B859421
theorem B2422925 : Blo 714321 2422925 := bstep (se 3 (by rfl) ⟨454298, by rfl⟩ : syracuseStep 2422925 = 908597) B908597
theorem B1210531 : Blo 714321 1210531 := bstep (se 1 (by rfl) ⟨907898, by rfl⟩ : syracuseStep 1210531 = 1815797) B1815797
theorem B1145011 : Blo 714321 1145011 := bstep (se 1 (by rfl) ⟨858758, by rfl⟩ : syracuseStep 1145011 = 1717517) B1717517
theorem B9828533 : Blo 714321 9828533 := bstep (se 5 (by rfl) ⟨460712, by rfl⟩ : syracuseStep 9828533 = 921425) B921425
theorem B2422979 : Blo 714321 2422979 := bstep (se 1 (by rfl) ⟨1817234, by rfl⟩ : syracuseStep 2422979 = 3634469) B3634469
theorem B3635441 : Blo 714321 3635441 := bstep (se 2 (by rfl) ⟨1363290, by rfl⟩ : syracuseStep 3635441 = 2726581) B2726581
theorem B1210673 : Blo 714321 1210673 := bstep (se 2 (by rfl) ⟨454002, by rfl⟩ : syracuseStep 1210673 = 908005) B908005
theorem B8157509 : Blo 714321 8157509 := bstep (se 4 (by rfl) ⟨764766, by rfl⟩ : syracuseStep 8157509 = 1529533) B1529533
theorem B2619811 : Blo 714321 2619811 := bstep (se 1 (by rfl) ⟨1964858, by rfl⟩ : syracuseStep 2619811 = 3929717) B3929717
theorem B1210801 : Blo 714321 1210801 := bstep (se 2 (by rfl) ⟨454050, by rfl⟩ : syracuseStep 1210801 = 908101) B908101
theorem B1145267 : Blo 714321 1145267 := bstep (se 1 (by rfl) ⟨858950, by rfl⟩ : syracuseStep 1145267 = 1717901) B1717901
theorem B2423249 : Blo 714321 2423249 := bstep (se 2 (by rfl) ⟨908718, by rfl⟩ : syracuseStep 2423249 = 1817437) B1817437
theorem B1210835 : Blo 714321 1210835 := bstep (se 1 (by rfl) ⟨908126, by rfl⟩ : syracuseStep 1210835 = 1816253) B1816253
theorem B1210963 : Blo 714321 1210963 := bstep (se 1 (by rfl) ⟨908222, by rfl⟩ : syracuseStep 1210963 = 1816445) B1816445
theorem B1964675 : Blo 714321 1964675 := bstep (se 1 (by rfl) ⟨1473506, by rfl⟩ : syracuseStep 1964675 = 2947013) B2947013
theorem B1211105 : Blo 714321 1211105 := bstep (se 2 (by rfl) ⟨454164, by rfl⟩ : syracuseStep 1211105 = 908329) B908329
theorem B5798627 : Blo 714321 5798627 := bstep (se 1 (by rfl) ⟨4348970, by rfl⟩ : syracuseStep 5798627 = 8697941) B8697941
theorem B1047377 : Blo 714321 1047377 := bstep (se 2 (by rfl) ⟨392766, by rfl⟩ : syracuseStep 1047377 = 785533) B785533
theorem B1211233 : Blo 714321 1211233 := bstep (se 2 (by rfl) ⟨454212, by rfl⟩ : syracuseStep 1211233 = 908425) B908425
theorem B1211267 : Blo 714321 1211267 := bstep (se 1 (by rfl) ⟨908450, by rfl⟩ : syracuseStep 1211267 = 1816901) B1816901
theorem B4914053 : Blo 714321 4914053 := bstep (se 4 (by rfl) ⟨460692, by rfl⟩ : syracuseStep 4914053 = 921385) B921385
theorem B2423789 : Blo 714321 2423789 := bstep (se 3 (by rfl) ⟨454460, by rfl⟩ : syracuseStep 2423789 = 908921) B908921
theorem B1211395 : Blo 714321 1211395 := bstep (se 1 (by rfl) ⟨908546, by rfl⟩ : syracuseStep 1211395 = 1817093) B1817093
theorem B2423843 : Blo 714321 2423843 := bstep (se 1 (by rfl) ⟨1817882, by rfl⟩ : syracuseStep 2423843 = 3635765) B3635765
theorem B1145971 : Blo 714321 1145971 := bstep (se 1 (by rfl) ⟨859478, by rfl⟩ : syracuseStep 1145971 = 1718957) B1718957
theorem B1211537 : Blo 714321 1211537 := bstep (se 2 (by rfl) ⟨454326, by rfl⟩ : syracuseStep 1211537 = 908653) B908653
theorem B982211 : Blo 714321 982211 := bstep (se 1 (by rfl) ⟨736658, by rfl⟩ : syracuseStep 982211 = 1473317) B1473317
theorem B1211665 : Blo 714321 1211665 := bstep (se 2 (by rfl) ⟨454374, by rfl⟩ : syracuseStep 1211665 = 908749) B908749
theorem B2424113 : Blo 714321 2424113 := bstep (se 2 (by rfl) ⟨909042, by rfl⟩ : syracuseStep 2424113 = 1818085) B1818085
theorem B1211699 : Blo 714321 1211699 := bstep (se 1 (by rfl) ⟨908774, by rfl⟩ : syracuseStep 1211699 = 1817549) B1817549
theorem B1146241 : Blo 714321 1146241 := bstep (se 2 (by rfl) ⟨429840, by rfl⟩ : syracuseStep 1146241 = 859681) B859681
theorem B1211827 : Blo 714321 1211827 := bstep (se 1 (by rfl) ⟨908870, by rfl⟩ : syracuseStep 1211827 = 1817741) B1817741
theorem B1146305 : Blo 714321 1146305 := bstep (se 2 (by rfl) ⟨429864, by rfl⟩ : syracuseStep 1146305 = 859729) B859729
theorem B1637891 : Blo 714321 1637891 := bstep (se 1 (by rfl) ⟨1228418, by rfl⟩ : syracuseStep 1637891 = 2456837) B2456837
theorem B982561 : Blo 714321 982561 := bstep (se 2 (by rfl) ⟨368460, by rfl⟩ : syracuseStep 982561 = 736921) B736921
theorem B3276323 : Blo 714321 3276323 := bstep (se 1 (by rfl) ⟨2457242, by rfl⟩ : syracuseStep 3276323 = 4914485) B4914485
theorem B1211969 : Blo 714321 1211969 := bstep (se 2 (by rfl) ⟨454488, by rfl⟩ : syracuseStep 1211969 = 908977) B908977
theorem B1212097 : Blo 714321 1212097 := bstep (se 2 (by rfl) ⟨454536, by rfl⟩ : syracuseStep 1212097 = 909073) B909073
theorem B1212131 : Blo 714321 1212131 := bstep (se 1 (by rfl) ⟨909098, by rfl⟩ : syracuseStep 1212131 = 1818197) B1818197
theorem B2293571 : Blo 714321 2293571 := bstep (se 1 (by rfl) ⟨1720178, by rfl⟩ : syracuseStep 2293571 = 3440357) B3440357
theorem B2719565 : Blo 714321 2719565 := bstep (se 3 (by rfl) ⟨509918, by rfl⟩ : syracuseStep 2719565 = 1019837) B1019837
theorem B2752643 : Blo 714321 2752643 := bstep (se 1 (by rfl) ⟨2064482, by rfl⟩ : syracuseStep 2752643 = 4128965) B4128965
theorem B3440819 : Blo 714321 3440819 := bstep (se 1 (by rfl) ⟨2580614, by rfl⟩ : syracuseStep 3440819 = 5161229) B5161229
theorem B2720051 : Blo 714321 2720051 := bstep (se 1 (by rfl) ⟨2040038, by rfl⟩ : syracuseStep 2720051 = 4080077) B4080077
theorem B2326849 : Blo 714321 2326849 := bstep (se 2 (by rfl) ⟨872568, by rfl⟩ : syracuseStep 2326849 = 1745137) B1745137
theorem B3440971 : Blo 714321 3440971 := bstep (se 1 (by rfl) ⟨2580728, by rfl⟩ : syracuseStep 3440971 = 5161457) B5161457
theorem B10322275 : Blo 714321 10322275 := bstep (se 1 (by rfl) ⟨7741706, by rfl⟩ : syracuseStep 10322275 = 15483413) B15483413
theorem B5669297 : Blo 714321 5669297 := bstep (se 2 (by rfl) ⟨2125986, by rfl⟩ : syracuseStep 5669297 = 4251973) B4251973
theorem B1933913 : Blo 714321 1933913 := bstep (se 2 (by rfl) ⟨725217, by rfl⟩ : syracuseStep 1933913 = 1450435) B1450435
theorem B1311383 : Blo 714321 1311383 := bstep (se 1 (by rfl) ⟨983537, by rfl⟩ : syracuseStep 1311383 = 1967075) B1967075
theorem B1475585 : Blo 714321 1475585 := bstep (se 2 (by rfl) ⟨553344, by rfl⟩ : syracuseStep 1475585 = 1106689) B1106689
theorem B46368227 : Blo 714321 46368227 := bstep (se 1 (by rfl) ⟨34776170, by rfl⟩ : syracuseStep 46368227 = 69552341) B69552341
theorem B1607255 : Blo 714321 1607255 := bstep (se 1 (by rfl) ⟨1205441, by rfl⟩ : syracuseStep 1607255 = 2410883) B2410883
theorem B919127 : Blo 714321 919127 := bstep (se 1 (by rfl) ⟨689345, by rfl⟩ : syracuseStep 919127 = 1378691) B1378691
theorem B1377985 : Blo 714321 1377985 := bstep (se 2 (by rfl) ⟨516744, by rfl⟩ : syracuseStep 1377985 = 1033489) B1033489
theorem B1017559 : Blo 714321 1017559 := bstep (se 1 (by rfl) ⟨763169, by rfl⟩ : syracuseStep 1017559 = 1526339) B1526339
theorem B2721539 : Blo 714321 2721539 := bstep (se 1 (by rfl) ⟨2041154, by rfl⟩ : syracuseStep 2721539 = 4082309) B4082309
theorem B1607435 : Blo 714321 1607435 := bstep (se 1 (by rfl) ⟨1205576, by rfl⟩ : syracuseStep 1607435 = 2411153) B2411153
theorem B1607489 : Blo 714321 1607489 := bstep (se 2 (by rfl) ⟨602808, by rfl⟩ : syracuseStep 1607489 = 1205617) B1205617
theorem B1607705 : Blo 714321 1607705 := bstep (se 2 (by rfl) ⟨602889, by rfl⟩ : syracuseStep 1607705 = 1205779) B1205779
theorem B1607795 : Blo 714321 1607795 := bstep (se 1 (by rfl) ⟨1205846, by rfl⟩ : syracuseStep 1607795 = 2411693) B2411693
theorem B1607831 : Blo 714321 1607831 := bstep (se 1 (by rfl) ⟨1205873, by rfl⟩ : syracuseStep 1607831 = 2411747) B2411747
theorem B2721995 : Blo 714321 2721995 := bstep (se 1 (by rfl) ⟨2041496, by rfl⟩ : syracuseStep 2721995 = 4082993) B4082993
theorem B5441741 : Blo 714321 5441741 := bstep (se 3 (by rfl) ⟨1020326, by rfl⟩ : syracuseStep 5441741 = 2040653) B2040653
theorem B1608011 : Blo 714321 1608011 := bstep (se 1 (by rfl) ⟨1206008, by rfl⟩ : syracuseStep 1608011 = 2412017) B2412017
theorem B8259941 : Blo 714321 8259941 := bstep (se 4 (by rfl) ⟨774369, by rfl⟩ : syracuseStep 8259941 = 1548739) B1548739
theorem B88279409 : Blo 714321 88279409 := bstep (se 2 (by rfl) ⟨33104778, by rfl⟩ : syracuseStep 88279409 = 66209557) B66209557
theorem B1608065 : Blo 714321 1608065 := bstep (se 2 (by rfl) ⟨603024, by rfl⟩ : syracuseStep 1608065 = 1206049) B1206049
theorem B2722193 : Blo 714321 2722193 := bstep (se 2 (by rfl) ⟨1020822, by rfl⟩ : syracuseStep 2722193 = 2041645) B2041645
theorem B1018379 : Blo 714321 1018379 := bstep (se 1 (by rfl) ⟨763784, by rfl⟩ : syracuseStep 1018379 = 1527569) B1527569
theorem B1608281 : Blo 714321 1608281 := bstep (se 2 (by rfl) ⟨603105, by rfl⟩ : syracuseStep 1608281 = 1206211) B1206211
theorem B2034355 : Blo 714321 2034355 := bstep (se 1 (by rfl) ⟨1525766, by rfl⟩ : syracuseStep 2034355 = 3051533) B3051533
theorem B1608371 : Blo 714321 1608371 := bstep (se 1 (by rfl) ⟨1206278, by rfl⟩ : syracuseStep 1608371 = 2412557) B2412557
theorem B5442227 : Blo 714321 5442227 := bstep (se 1 (by rfl) ⟨4081670, by rfl⟩ : syracuseStep 5442227 = 8163341) B8163341
theorem B1608407 : Blo 714321 1608407 := bstep (se 1 (by rfl) ⟨1206305, by rfl⟩ : syracuseStep 1608407 = 2412611) B2412611
theorem B1608587 : Blo 714321 1608587 := bstep (se 1 (by rfl) ⟨1206440, by rfl⟩ : syracuseStep 1608587 = 2412881) B2412881
theorem B1608641 : Blo 714321 1608641 := bstep (se 2 (by rfl) ⟨603240, by rfl⟩ : syracuseStep 1608641 = 1206481) B1206481
theorem B2722967 : Blo 714321 2722967 := bstep (se 1 (by rfl) ⟨2042225, by rfl⟩ : syracuseStep 2722967 = 4084451) B4084451
theorem B1608857 : Blo 714321 1608857 := bstep (se 2 (by rfl) ⟨603321, by rfl⟩ : syracuseStep 1608857 = 1206643) B1206643
theorem B1608947 : Blo 714321 1608947 := bstep (se 1 (by rfl) ⟨1206710, by rfl⟩ : syracuseStep 1608947 = 2413421) B2413421
theorem B1608983 : Blo 714321 1608983 := bstep (se 1 (by rfl) ⟨1206737, by rfl⟩ : syracuseStep 1608983 = 2413475) B2413475
theorem B2723165 : Blo 714321 2723165 := bstep (se 3 (by rfl) ⟨510593, by rfl⟩ : syracuseStep 2723165 = 1021187) B1021187
theorem B1609163 : Blo 714321 1609163 := bstep (se 1 (by rfl) ⟨1206872, by rfl⟩ : syracuseStep 1609163 = 2413745) B2413745
theorem B2788829 : Blo 714321 2788829 := bstep (se 3 (by rfl) ⟨522905, by rfl⟩ : syracuseStep 2788829 = 1045811) B1045811
theorem B1609217 : Blo 714321 1609217 := bstep (se 2 (by rfl) ⟨603456, by rfl⟩ : syracuseStep 1609217 = 1206913) B1206913
theorem B6524621 : Blo 714321 6524621 := bstep (se 3 (by rfl) ⟨1223366, by rfl⟩ : syracuseStep 6524621 = 2446733) B2446733
theorem B1609433 : Blo 714321 1609433 := bstep (se 2 (by rfl) ⟨603537, by rfl⟩ : syracuseStep 1609433 = 1207075) B1207075
theorem B1609523 : Blo 714321 1609523 := bstep (se 1 (by rfl) ⟨1207142, by rfl⟩ : syracuseStep 1609523 = 2414285) B2414285
theorem B1609559 : Blo 714321 1609559 := bstep (se 1 (by rfl) ⟨1207169, by rfl⟩ : syracuseStep 1609559 = 2414339) B2414339
theorem B1609739 : Blo 714321 1609739 := bstep (se 1 (by rfl) ⟨1207304, by rfl⟩ : syracuseStep 1609739 = 2414609) B2414609
theorem B1609793 : Blo 714321 1609793 := bstep (se 2 (by rfl) ⟨603672, by rfl⟩ : syracuseStep 1609793 = 1207345) B1207345
theorem B5443685 : Blo 714321 5443685 := bstep (se 4 (by rfl) ⟨510345, by rfl⟩ : syracuseStep 5443685 = 1020691) B1020691
theorem B1610009 : Blo 714321 1610009 := bstep (se 2 (by rfl) ⟨603753, by rfl⟩ : syracuseStep 1610009 = 1207507) B1207507
theorem B1610099 : Blo 714321 1610099 := bstep (se 1 (by rfl) ⟨1207574, by rfl⟩ : syracuseStep 1610099 = 2415149) B2415149
theorem B13767029 : Blo 714321 13767029 := bstep (se 5 (by rfl) ⟨645329, by rfl⟩ : syracuseStep 13767029 = 1290659) B1290659
theorem B1610135 : Blo 714321 1610135 := bstep (se 1 (by rfl) ⟨1207601, by rfl⟩ : syracuseStep 1610135 = 2415203) B2415203
theorem B1610315 : Blo 714321 1610315 := bstep (se 1 (by rfl) ⟨1207736, by rfl⟩ : syracuseStep 1610315 = 2415473) B2415473
theorem B5444171 : Blo 714321 5444171 := bstep (se 1 (by rfl) ⟨4083128, by rfl⟩ : syracuseStep 5444171 = 8166257) B8166257
theorem B1610369 : Blo 714321 1610369 := bstep (se 2 (by rfl) ⟨603888, by rfl⟩ : syracuseStep 1610369 = 1207777) B1207777
theorem B1610585 : Blo 714321 1610585 := bstep (se 2 (by rfl) ⟨603969, by rfl⟩ : syracuseStep 1610585 = 1207939) B1207939
theorem B1610675 : Blo 714321 1610675 := bstep (se 1 (by rfl) ⟨1208006, by rfl⟩ : syracuseStep 1610675 = 2416013) B2416013
theorem B1610711 : Blo 714321 1610711 := bstep (se 1 (by rfl) ⟨1208033, by rfl⟩ : syracuseStep 1610711 = 2416067) B2416067
theorem B3052505 : Blo 714321 3052505 := bstep (se 2 (by rfl) ⟨1144689, by rfl⟩ : syracuseStep 3052505 = 2289379) B2289379
theorem B1610891 : Blo 714321 1610891 := bstep (se 1 (by rfl) ⟨1208168, by rfl⟩ : syracuseStep 1610891 = 2416337) B2416337
theorem B1610945 : Blo 714321 1610945 := bstep (se 2 (by rfl) ⟨604104, by rfl⟩ : syracuseStep 1610945 = 1208209) B1208209
theorem B2725123 : Blo 714321 2725123 := bstep (se 1 (by rfl) ⟨2043842, by rfl⟩ : syracuseStep 2725123 = 4087685) B4087685
theorem B2692445 : Blo 714321 2692445 := bstep (se 3 (by rfl) ⟨504833, by rfl⟩ : syracuseStep 2692445 = 1009667) B1009667
theorem B1611161 : Blo 714321 1611161 := bstep (se 2 (by rfl) ⟨604185, by rfl⟩ : syracuseStep 1611161 = 1208371) B1208371
theorem B1611251 : Blo 714321 1611251 := bstep (se 1 (by rfl) ⟨1208438, by rfl⟩ : syracuseStep 1611251 = 2416877) B2416877
theorem B2037271 : Blo 714321 2037271 := bstep (se 1 (by rfl) ⟨1527953, by rfl⟩ : syracuseStep 2037271 = 3055907) B3055907
theorem B1611287 : Blo 714321 1611287 := bstep (se 1 (by rfl) ⟨1208465, by rfl⟩ : syracuseStep 1611287 = 2416931) B2416931
theorem B2725427 : Blo 714321 2725427 := bstep (se 1 (by rfl) ⟨2044070, by rfl⟩ : syracuseStep 2725427 = 4088141) B4088141
theorem B5969483 : Blo 714321 5969483 := bstep (se 1 (by rfl) ⟨4477112, by rfl⟩ : syracuseStep 5969483 = 8954225) B8954225
theorem B1611467 : Blo 714321 1611467 := bstep (se 1 (by rfl) ⟨1208600, by rfl⟩ : syracuseStep 1611467 = 2417201) B2417201
theorem B1611521 : Blo 714321 1611521 := bstep (se 2 (by rfl) ⟨604320, by rfl⟩ : syracuseStep 1611521 = 1208641) B1208641
theorem B1808203 : Blo 714321 1808203 := bstep (se 1 (by rfl) ⟨1356152, by rfl⟩ : syracuseStep 1808203 = 2712305) B2712305
theorem B1808345 : Blo 714321 1808345 := bstep (se 2 (by rfl) ⟨678129, by rfl⟩ : syracuseStep 1808345 = 1356259) B1356259
theorem B1611737 : Blo 714321 1611737 := bstep (se 2 (by rfl) ⟨604401, by rfl⟩ : syracuseStep 1611737 = 1208803) B1208803
theorem B2299927 : Blo 714321 2299927 := bstep (se 1 (by rfl) ⟨1724945, by rfl⟩ : syracuseStep 2299927 = 3449891) B3449891
theorem B1611827 : Blo 714321 1611827 := bstep (se 1 (by rfl) ⟨1208870, by rfl⟩ : syracuseStep 1611827 = 2417741) B2417741
theorem B1611863 : Blo 714321 1611863 := bstep (se 1 (by rfl) ⟨1208897, by rfl⟩ : syracuseStep 1611863 = 2417795) B2417795
theorem B2726081 : Blo 714321 2726081 := bstep (se 2 (by rfl) ⟨1022280, by rfl⟩ : syracuseStep 2726081 = 2044561) B2044561
theorem B3053771 : Blo 714321 3053771 := bstep (se 1 (by rfl) ⟨2290328, by rfl⟩ : syracuseStep 3053771 = 4580657) B4580657
theorem B13211909 : Blo 714321 13211909 := bstep (se 4 (by rfl) ⟨1238616, by rfl⟩ : syracuseStep 13211909 = 2477233) B2477233
theorem B1612043 : Blo 714321 1612043 := bstep (se 1 (by rfl) ⟨1209032, by rfl⟩ : syracuseStep 1612043 = 2418065) B2418065
theorem B1612097 : Blo 714321 1612097 := bstep (se 2 (by rfl) ⟨604536, by rfl⟩ : syracuseStep 1612097 = 1209073) B1209073
theorem B1612313 : Blo 714321 1612313 := bstep (se 2 (by rfl) ⟨604617, by rfl⟩ : syracuseStep 1612313 = 1209235) B1209235
theorem B3054131 : Blo 714321 3054131 := bstep (se 1 (by rfl) ⟨2290598, by rfl⟩ : syracuseStep 3054131 = 4581197) B4581197
theorem B1612403 : Blo 714321 1612403 := bstep (se 1 (by rfl) ⟨1209302, by rfl⟩ : syracuseStep 1612403 = 2418605) B2418605
theorem B1612439 : Blo 714321 1612439 := bstep (se 1 (by rfl) ⟨1209329, by rfl⟩ : syracuseStep 1612439 = 2418659) B2418659
theorem B1809175 : Blo 714321 1809175 := bstep (se 1 (by rfl) ⟨1356881, by rfl⟩ : syracuseStep 1809175 = 2713763) B2713763
theorem B4070189 : Blo 714321 4070189 := bstep (se 3 (by rfl) ⟨763160, by rfl⟩ : syracuseStep 4070189 = 1526321) B1526321
theorem B3873581 : Blo 714321 3873581 := bstep (se 3 (by rfl) ⟨726296, by rfl⟩ : syracuseStep 3873581 = 1452593) B1452593
theorem B2038603 : Blo 714321 2038603 := bstep (se 1 (by rfl) ⟨1528952, by rfl⟩ : syracuseStep 2038603 = 3057905) B3057905
theorem B1612619 : Blo 714321 1612619 := bstep (se 1 (by rfl) ⟨1209464, by rfl⟩ : syracuseStep 1612619 = 2418929) B2418929
theorem B1612673 : Blo 714321 1612673 := bstep (se 2 (by rfl) ⟨604752, by rfl⟩ : syracuseStep 1612673 = 1209505) B1209505
theorem B1612889 : Blo 714321 1612889 := bstep (se 2 (by rfl) ⟨604833, by rfl⟩ : syracuseStep 1612889 = 1209667) B1209667
theorem B2038877 : Blo 714321 2038877 := bstep (se 3 (by rfl) ⟨382289, by rfl⟩ : syracuseStep 2038877 = 764579) B764579
theorem B1612979 : Blo 714321 1612979 := bstep (se 1 (by rfl) ⟨1209734, by rfl⟩ : syracuseStep 1612979 = 2419469) B2419469
theorem B1809611 : Blo 714321 1809611 := bstep (se 1 (by rfl) ⟨1357208, by rfl⟩ : syracuseStep 1809611 = 2714417) B2714417
theorem B1613015 : Blo 714321 1613015 := bstep (se 1 (by rfl) ⟨1209761, by rfl⟩ : syracuseStep 1613015 = 2419523) B2419523
theorem B1613195 : Blo 714321 1613195 := bstep (se 1 (by rfl) ⟨1209896, by rfl⟩ : syracuseStep 1613195 = 2419793) B2419793
theorem B2727341 : Blo 714321 2727341 := bstep (se 3 (by rfl) ⟨511376, by rfl⟩ : syracuseStep 2727341 = 1022753) B1022753
theorem B2039219 : Blo 714321 2039219 := bstep (se 1 (by rfl) ⟨1529414, by rfl⟩ : syracuseStep 2039219 = 3058829) B3058829
theorem B1613249 : Blo 714321 1613249 := bstep (se 2 (by rfl) ⟨604968, by rfl⟩ : syracuseStep 1613249 = 1209937) B1209937
theorem B2727371 : Blo 714321 2727371 := bstep (se 1 (by rfl) ⟨2045528, by rfl⟩ : syracuseStep 2727371 = 4091057) B4091057
theorem B1449431 : Blo 714321 1449431 := bstep (se 1 (by rfl) ⟨1087073, by rfl⟩ : syracuseStep 1449431 = 2174147) B2174147
theorem B2793005 : Blo 714321 2793005 := bstep (se 3 (by rfl) ⟨523688, by rfl⟩ : syracuseStep 2793005 = 1047377) B1047377
theorem B1809985 : Blo 714321 1809985 := bstep (se 2 (by rfl) ⟨678744, by rfl⟩ : syracuseStep 1809985 = 1357489) B1357489
theorem B8691275 : Blo 714321 8691275 := bstep (se 1 (by rfl) ⟨6518456, by rfl⟩ : syracuseStep 8691275 = 13036913) B13036913
theorem B1613465 : Blo 714321 1613465 := bstep (se 2 (by rfl) ⟨605049, by rfl⟩ : syracuseStep 1613465 = 1210099) B1210099
theorem B1613555 : Blo 714321 1613555 := bstep (se 1 (by rfl) ⟨1210166, by rfl⟩ : syracuseStep 1613555 = 2420333) B2420333
theorem B1613591 : Blo 714321 1613591 := bstep (se 1 (by rfl) ⟨1210193, by rfl⟩ : syracuseStep 1613591 = 2420387) B2420387
theorem B47652785 : Blo 714321 47652785 := bstep (se 2 (by rfl) ⟨17869794, by rfl⟩ : syracuseStep 47652785 = 35739589) B35739589
theorem B1613771 : Blo 714321 1613771 := bstep (se 1 (by rfl) ⟨1210328, by rfl⟩ : syracuseStep 1613771 = 2420657) B2420657
theorem B827371 : Blo 714321 827371 := bstep (se 1 (by rfl) ⟨620528, by rfl⟩ : syracuseStep 827371 = 1241057) B1241057
theorem B1613825 : Blo 714321 1613825 := bstep (se 2 (by rfl) ⟨605184, by rfl⟩ : syracuseStep 1613825 = 1210369) B1210369
theorem B4595777 : Blo 714321 4595777 := bstep (se 2 (by rfl) ⟨1723416, by rfl⟩ : syracuseStep 4595777 = 3446833) B3446833
theorem B4464715 : Blo 714321 4464715 := bstep (se 1 (by rfl) ⟨3348536, by rfl⟩ : syracuseStep 4464715 = 6697073) B6697073
theorem B1810583 : Blo 714321 1810583 := bstep (se 1 (by rfl) ⟨1357937, by rfl⟩ : syracuseStep 1810583 = 2715875) B2715875
theorem B1417409 : Blo 714321 1417409 := bstep (se 2 (by rfl) ⟨531528, by rfl⟩ : syracuseStep 1417409 = 1063057) B1063057
theorem B1614041 : Blo 714321 1614041 := bstep (se 2 (by rfl) ⟨605265, by rfl⟩ : syracuseStep 1614041 = 1210531) B1210531
theorem B1614131 : Blo 714321 1614131 := bstep (se 1 (by rfl) ⟨1210598, by rfl⟩ : syracuseStep 1614131 = 2421197) B2421197
theorem B1614167 : Blo 714321 1614167 := bstep (se 1 (by rfl) ⟨1210625, by rfl⟩ : syracuseStep 1614167 = 2421251) B2421251
theorem B5808485 : Blo 714321 5808485 := bstep (se 4 (by rfl) ⟨544545, by rfl⟩ : syracuseStep 5808485 = 1089091) B1089091
theorem B860555 : Blo 714321 860555 := bstep (se 1 (by rfl) ⟨645416, by rfl⟩ : syracuseStep 860555 = 1290833) B1290833
theorem B1614347 : Blo 714321 1614347 := bstep (se 1 (by rfl) ⟨1210760, by rfl⟩ : syracuseStep 1614347 = 2421521) B2421521
theorem B1614401 : Blo 714321 1614401 := bstep (se 2 (by rfl) ⟨605400, by rfl⟩ : syracuseStep 1614401 = 1210801) B1210801
theorem B860747 : Blo 714321 860747 := bstep (se 1 (by rfl) ⟨645560, by rfl⟩ : syracuseStep 860747 = 1291121) B1291121
theorem B1614617 : Blo 714321 1614617 := bstep (se 2 (by rfl) ⟨605481, by rfl⟩ : syracuseStep 1614617 = 1210963) B1210963
theorem B1614707 : Blo 714321 1614707 := bstep (se 1 (by rfl) ⟨1211030, by rfl⟩ : syracuseStep 1614707 = 2422061) B2422061
theorem B1614743 : Blo 714321 1614743 := bstep (se 1 (by rfl) ⟨1211057, by rfl⟩ : syracuseStep 1614743 = 2422115) B2422115
theorem B1811393 : Blo 714321 1811393 := bstep (se 2 (by rfl) ⟨679272, by rfl⟩ : syracuseStep 1811393 = 1358545) B1358545
theorem B1614923 : Blo 714321 1614923 := bstep (se 1 (by rfl) ⟨1211192, by rfl⟩ : syracuseStep 1614923 = 2422385) B2422385
theorem B1614977 : Blo 714321 1614977 := bstep (se 2 (by rfl) ⟨605616, by rfl⟩ : syracuseStep 1614977 = 1211233) B1211233
theorem B7349399 : Blo 714321 7349399 := bstep (se 1 (by rfl) ⟨5512049, by rfl⟩ : syracuseStep 7349399 = 11024099) B11024099
theorem B1615193 : Blo 714321 1615193 := bstep (se 2 (by rfl) ⟨605697, by rfl⟩ : syracuseStep 1615193 = 1211395) B1211395
theorem B1615283 : Blo 714321 1615283 := bstep (se 1 (by rfl) ⟨1211462, by rfl⟩ : syracuseStep 1615283 = 2422925) B2422925
theorem B2041291 : Blo 714321 2041291 := bstep (se 1 (by rfl) ⟨1530968, by rfl⟩ : syracuseStep 2041291 = 3061937) B3061937
theorem B1615319 : Blo 714321 1615319 := bstep (se 1 (by rfl) ⟨1211489, by rfl⟩ : syracuseStep 1615319 = 2422979) B2422979
theorem B1811929 : Blo 714321 1811929 := bstep (se 2 (by rfl) ⟨679473, by rfl⟩ : syracuseStep 1811929 = 1358947) B1358947
theorem B13608461 : Blo 714321 13608461 := bstep (se 3 (by rfl) ⟨2551586, by rfl⟩ : syracuseStep 13608461 = 5103173) B5103173
theorem B763511 : Blo 714321 763511 := bstep (se 1 (by rfl) ⟨572633, by rfl⟩ : syracuseStep 763511 = 1145267) B1145267
theorem B1615499 : Blo 714321 1615499 := bstep (se 1 (by rfl) ⟨1211624, by rfl⟩ : syracuseStep 1615499 = 2423249) B2423249
theorem B1615553 : Blo 714321 1615553 := bstep (se 2 (by rfl) ⟨605832, by rfl⟩ : syracuseStep 1615553 = 1211665) B1211665
theorem B12396293 : Blo 714321 12396293 := bstep (se 4 (by rfl) ⟨1162152, by rfl⟩ : syracuseStep 12396293 = 2324305) B2324305
theorem B5449517 : Blo 714321 5449517 := bstep (se 3 (by rfl) ⟨1021784, by rfl⟩ : syracuseStep 5449517 = 2043569) B2043569
theorem B1288001 : Blo 714321 1288001 := bstep (se 2 (by rfl) ⟨483000, by rfl⟩ : syracuseStep 1288001 = 966001) B966001
theorem B1615769 : Blo 714321 1615769 := bstep (se 2 (by rfl) ⟨605913, by rfl⟩ : syracuseStep 1615769 = 1211827) B1211827
theorem B2041793 : Blo 714321 2041793 := bstep (se 2 (by rfl) ⟨765672, by rfl⟩ : syracuseStep 2041793 = 1531345) B1531345
theorem B1615859 : Blo 714321 1615859 := bstep (se 1 (by rfl) ⟨1211894, by rfl⟩ : syracuseStep 1615859 = 2423789) B2423789
theorem B1615895 : Blo 714321 1615895 := bstep (se 1 (by rfl) ⟨1211921, by rfl⟩ : syracuseStep 1615895 = 2423843) B2423843
theorem B1616075 : Blo 714321 1616075 := bstep (se 1 (by rfl) ⟨1212056, by rfl⟩ : syracuseStep 1616075 = 2424113) B2424113
theorem B1616129 : Blo 714321 1616129 := bstep (se 2 (by rfl) ⟨606048, by rfl⟩ : syracuseStep 1616129 = 1212097) B1212097
theorem B2042135 : Blo 714321 2042135 := bstep (se 1 (by rfl) ⟨1531601, by rfl⟩ : syracuseStep 2042135 = 3063203) B3063203
theorem B764203 : Blo 714321 764203 := bstep (se 1 (by rfl) ⟨573152, by rfl⟩ : syracuseStep 764203 = 1146305) B1146305
theorem B1091927 : Blo 714321 1091927 := bstep (se 1 (by rfl) ⟨818945, by rfl⟩ : syracuseStep 1091927 = 1637891) B1637891
theorem B1452439 : Blo 714321 1452439 := bstep (se 1 (by rfl) ⟨1089329, by rfl⟩ : syracuseStep 1452439 = 2178659) B2178659
theorem B1681817 : Blo 714321 1681817 := bstep (se 2 (by rfl) ⟨630681, by rfl⟩ : syracuseStep 1681817 = 1261363) B1261363
theorem B1550785 : Blo 714321 1550785 := bstep (se 2 (by rfl) ⟨581544, by rfl⟩ : syracuseStep 1550785 = 1163089) B1163089
theorem B1813043 : Blo 714321 1813043 := bstep (se 1 (by rfl) ⟨1359782, by rfl⟩ : syracuseStep 1813043 = 2719565) B2719565
theorem B2763571 : Blo 714321 2763571 := bstep (se 1 (by rfl) ⟨2072678, by rfl⟩ : syracuseStep 2763571 = 4145357) B4145357
theorem B1813337 : Blo 714321 1813337 := bstep (se 2 (by rfl) ⟨680001, by rfl⟩ : syracuseStep 1813337 = 1360003) B1360003
theorem B3877733 : Blo 714321 3877733 := bstep (se 4 (by rfl) ⟨363537, by rfl⟩ : syracuseStep 3877733 = 727075) B727075
theorem B1289305 : Blo 714321 1289305 := bstep (se 2 (by rfl) ⟨483489, by rfl⟩ : syracuseStep 1289305 = 966979) B966979
theorem B1453387 : Blo 714321 1453387 := bstep (se 1 (by rfl) ⟨1090040, by rfl⟩ : syracuseStep 1453387 = 2180081) B2180081
theorem B3059203 : Blo 714321 3059203 := bstep (se 1 (by rfl) ⟨2294402, by rfl⟩ : syracuseStep 3059203 = 4588805) B4588805
theorem B3878551 : Blo 714321 3878551 := bstep (se 1 (by rfl) ⟨2908913, by rfl⟩ : syracuseStep 3878551 = 5817827) B5817827
theorem B1224407 : Blo 714321 1224407 := bstep (se 1 (by rfl) ⟨918305, by rfl⟩ : syracuseStep 1224407 = 1836611) B1836611
theorem B765655 : Blo 714321 765655 := bstep (se 1 (by rfl) ⟨574241, by rfl⟩ : syracuseStep 765655 = 1148483) B1148483
theorem B3059545 : Blo 714321 3059545 := bstep (se 2 (by rfl) ⟨1147329, by rfl⟩ : syracuseStep 3059545 = 2294659) B2294659
theorem B1552343 : Blo 714321 1552343 := bstep (se 1 (by rfl) ⟨1164257, by rfl⟩ : syracuseStep 1552343 = 2328515) B2328515
theorem B766027 : Blo 714321 766027 := bstep (se 1 (by rfl) ⟨574520, by rfl⟩ : syracuseStep 766027 = 1149041) B1149041
theorem B1224791 : Blo 714321 1224791 := bstep (se 1 (by rfl) ⟨918593, by rfl⟩ : syracuseStep 1224791 = 1837187) B1837187
theorem B4600081 : Blo 714321 4600081 := bstep (se 2 (by rfl) ⟨1725030, by rfl⟩ : syracuseStep 4600081 = 3450061) B3450061
theorem B2044253 : Blo 714321 2044253 := bstep (se 3 (by rfl) ⟨383297, by rfl⟩ : syracuseStep 2044253 = 766595) B766595
theorem B7352677 : Blo 714321 7352677 := bstep (se 4 (by rfl) ⟨689313, by rfl⟩ : syracuseStep 7352677 = 1378627) B1378627
theorem B1814987 : Blo 714321 1814987 := bstep (se 1 (by rfl) ⟨1361240, by rfl⟩ : syracuseStep 1814987 = 2722481) B2722481
theorem B3617297 : Blo 714321 3617297 := bstep (se 2 (by rfl) ⟨1356486, by rfl⟩ : syracuseStep 3617297 = 2712973) B2712973
theorem B3617459 : Blo 714321 3617459 := bstep (se 1 (by rfl) ⟨2713094, by rfl⟩ : syracuseStep 3617459 = 5426189) B5426189
theorem B2044595 : Blo 714321 2044595 := bstep (se 1 (by rfl) ⟨1533446, by rfl⟩ : syracuseStep 2044595 = 3066893) B3066893
theorem B3060503 : Blo 714321 3060503 := bstep (se 1 (by rfl) ⟨2295377, by rfl⟩ : syracuseStep 3060503 = 4590755) B4590755
theorem B2175947 : Blo 714321 2175947 := bstep (se 1 (by rfl) ⟨1631960, by rfl⟩ : syracuseStep 2175947 = 3263921) B3263921
theorem B1356851 : Blo 714321 1356851 := bstep (se 1 (by rfl) ⟨1017638, by rfl⟩ : syracuseStep 1356851 = 2035277) B2035277
theorem B1291403 : Blo 714321 1291403 := bstep (se 1 (by rfl) ⟨968552, by rfl⟩ : syracuseStep 1291403 = 1937105) B1937105
theorem B1357003 : Blo 714321 1357003 := bstep (se 1 (by rfl) ⟨1017752, by rfl⟩ : syracuseStep 1357003 = 2035505) B2035505
theorem B1815959 : Blo 714321 1815959 := bstep (se 1 (by rfl) ⟨1361969, by rfl⟩ : syracuseStep 1815959 = 2723939) B2723939
theorem B12269069 : Blo 714321 12269069 := bstep (se 3 (by rfl) ⟨2300450, by rfl⟩ : syracuseStep 12269069 = 4600901) B4600901
theorem B1357337 : Blo 714321 1357337 := bstep (se 2 (by rfl) ⟨509001, by rfl⟩ : syracuseStep 1357337 = 1018003) B1018003
theorem B5453405 : Blo 714321 5453405 := bstep (se 3 (by rfl) ⟨1022513, by rfl⟩ : syracuseStep 5453405 = 2045027) B2045027
theorem B3192721 : Blo 714321 3192721 := bstep (se 2 (by rfl) ⟨1197270, by rfl⟩ : syracuseStep 3192721 = 2394541) B2394541
theorem B1816627 : Blo 714321 1816627 := bstep (se 1 (by rfl) ⟨1362470, by rfl⟩ : syracuseStep 1816627 = 2724941) B2724941
theorem B4077661 : Blo 714321 4077661 := bstep (se 3 (by rfl) ⟨764561, by rfl⟩ : syracuseStep 4077661 = 1529123) B1529123
theorem B1357975 : Blo 714321 1357975 := bstep (se 1 (by rfl) ⟨1018481, by rfl⟩ : syracuseStep 1357975 = 2036963) B2036963
theorem B39172247 : Blo 714321 39172247 := bstep (se 1 (by rfl) ⟨29379185, by rfl⟩ : syracuseStep 39172247 = 58758371) B58758371
theorem B1816769 : Blo 714321 1816769 := bstep (se 2 (by rfl) ⟨681288, by rfl⟩ : syracuseStep 1816769 = 1362577) B1362577
theorem B3062195 : Blo 714321 3062195 := bstep (se 1 (by rfl) ⟨2296646, by rfl⟩ : syracuseStep 3062195 = 4593293) B4593293
theorem B3258883 : Blo 714321 3258883 := bstep (se 1 (by rfl) ⟨2444162, by rfl⟩ : syracuseStep 3258883 = 4888325) B4888325
theorem B3619403 : Blo 714321 3619403 := bstep (se 1 (by rfl) ⟨2714552, by rfl⟩ : syracuseStep 3619403 = 5429105) B5429105
theorem B6896279 : Blo 714321 6896279 := bstep (se 1 (by rfl) ⟨5172209, by rfl⟩ : syracuseStep 6896279 = 10344419) B10344419
theorem B1718977 : Blo 714321 1718977 := bstep (se 2 (by rfl) ⟨644616, by rfl⟩ : syracuseStep 1718977 = 1289233) B1289233
theorem B1489817 : Blo 714321 1489817 := bstep (se 2 (by rfl) ⟨558681, by rfl⟩ : syracuseStep 1489817 = 1117363) B1117363
theorem B1358795 : Blo 714321 1358795 := bstep (se 1 (by rfl) ⟨1019096, by rfl⟩ : syracuseStep 1358795 = 2038193) B2038193
theorem B1358849 : Blo 714321 1358849 := bstep (se 2 (by rfl) ⟨509568, by rfl⟩ : syracuseStep 1358849 = 1019137) B1019137
theorem B1293427 : Blo 714321 1293427 := bstep (se 1 (by rfl) ⟨970070, by rfl⟩ : syracuseStep 1293427 = 1940141) B1940141
theorem B965785 : Blo 714321 965785 := bstep (se 2 (by rfl) ⟨362169, by rfl⟩ : syracuseStep 965785 = 724339) B724339
theorem B1818035 : Blo 714321 1818035 := bstep (se 1 (by rfl) ⟨1363526, by rfl⟩ : syracuseStep 1818035 = 2727053) B2727053
theorem B1293889 : Blo 714321 1293889 := bstep (se 2 (by rfl) ⟨485208, by rfl⟩ : syracuseStep 1293889 = 970417) B970417
theorem B5226059 : Blo 714321 5226059 := bstep (se 1 (by rfl) ⟨3919544, by rfl⟩ : syracuseStep 5226059 = 7839089) B7839089
theorem B1720025 : Blo 714321 1720025 := bstep (se 2 (by rfl) ⟨645009, by rfl⟩ : syracuseStep 1720025 = 1290019) B1290019
theorem B3489581 : Blo 714321 3489581 := bstep (se 3 (by rfl) ⟨654296, by rfl⟩ : syracuseStep 3489581 = 1308593) B1308593
theorem B1359767 : Blo 714321 1359767 := bstep (se 1 (by rfl) ⟨1019825, by rfl⟩ : syracuseStep 1359767 = 2039651) B2039651
theorem B1032089 : Blo 714321 1032089 := bstep (se 2 (by rfl) ⟨387033, by rfl⟩ : syracuseStep 1032089 = 774067) B774067
theorem B3621185 : Blo 714321 3621185 := bstep (se 2 (by rfl) ⟨1357944, by rfl⟩ : syracuseStep 3621185 = 2715889) B2715889
theorem B1360307 : Blo 714321 1360307 := bstep (se 1 (by rfl) ⟨1020230, by rfl⟩ : syracuseStep 1360307 = 2040461) B2040461
theorem B6111845 : Blo 714321 6111845 := bstep (se 4 (by rfl) ⟨572985, by rfl⟩ : syracuseStep 6111845 = 1145971) B1145971
theorem B803659 : Blo 714321 803659 := bstep (se 1 (by rfl) ⟨602744, by rfl⟩ : syracuseStep 803659 = 1205489) B1205489
theorem B1360793 : Blo 714321 1360793 := bstep (se 2 (by rfl) ⟨510297, by rfl⟩ : syracuseStep 1360793 = 1020595) B1020595
theorem B803767 : Blo 714321 803767 := bstep (se 1 (by rfl) ⟨602825, by rfl⟩ : syracuseStep 803767 = 1205651) B1205651
theorem B3064877 : Blo 714321 3064877 := bstep (se 3 (by rfl) ⟨574664, by rfl⟩ : syracuseStep 3064877 = 1149329) B1149329
theorem B803947 : Blo 714321 803947 := bstep (se 1 (by rfl) ⟨602960, by rfl⟩ : syracuseStep 803947 = 1205921) B1205921
theorem B804055 : Blo 714321 804055 := bstep (se 1 (by rfl) ⟨603041, by rfl⟩ : syracuseStep 804055 = 1206083) B1206083
theorem B6112529 : Blo 714321 6112529 := bstep (se 2 (by rfl) ⟨2292198, by rfl⟩ : syracuseStep 6112529 = 4584397) B4584397
theorem B804235 : Blo 714321 804235 := bstep (se 1 (by rfl) ⟨603176, by rfl⟩ : syracuseStep 804235 = 1206353) B1206353
theorem B804343 : Blo 714321 804343 := bstep (se 1 (by rfl) ⟨603257, by rfl⟩ : syracuseStep 804343 = 1206515) B1206515
theorem B13092445 : Blo 714321 13092445 := bstep (se 3 (by rfl) ⟨2454833, by rfl⟩ : syracuseStep 13092445 = 4909667) B4909667
theorem B1492619 : Blo 714321 1492619 := bstep (se 1 (by rfl) ⟨1119464, by rfl⟩ : syracuseStep 1492619 = 2238929) B2238929
theorem B804523 : Blo 714321 804523 := bstep (se 1 (by rfl) ⟨603392, by rfl⟩ : syracuseStep 804523 = 1206785) B1206785
theorem B804631 : Blo 714321 804631 := bstep (se 1 (by rfl) ⟨603473, by rfl⟩ : syracuseStep 804631 = 1206947) B1206947
theorem B10438517 : Blo 714321 10438517 := bstep (se 5 (by rfl) ⟨489305, by rfl⟩ : syracuseStep 10438517 = 978611) B978611
theorem B1525655 : Blo 714321 1525655 := bstep (se 1 (by rfl) ⟨1144241, by rfl⟩ : syracuseStep 1525655 = 2288483) B2288483
theorem B804811 : Blo 714321 804811 := bstep (se 1 (by rfl) ⟨603608, by rfl⟩ : syracuseStep 804811 = 1207217) B1207217
theorem B804919 : Blo 714321 804919 := bstep (se 1 (by rfl) ⟨603689, by rfl⟩ : syracuseStep 804919 = 1207379) B1207379
theorem B5425217 : Blo 714321 5425217 := bstep (se 2 (by rfl) ⟨2034456, by rfl⟩ : syracuseStep 5425217 = 4068913) B4068913
theorem B8734871 : Blo 714321 8734871 := bstep (se 1 (by rfl) ⟨6551153, by rfl⟩ : syracuseStep 8734871 = 13102307) B13102307
theorem B3623129 : Blo 714321 3623129 := bstep (se 2 (by rfl) ⟨1358673, by rfl⟩ : syracuseStep 3623129 = 2717347) B2717347
theorem B805099 : Blo 714321 805099 := bstep (se 1 (by rfl) ⟨603824, by rfl⟩ : syracuseStep 805099 = 1207649) B1207649
theorem B1362251 : Blo 714321 1362251 := bstep (se 1 (by rfl) ⟨1021688, by rfl⟩ : syracuseStep 1362251 = 2043377) B2043377
theorem B805207 : Blo 714321 805207 := bstep (se 1 (by rfl) ⟨603905, by rfl⟩ : syracuseStep 805207 = 1207811) B1207811
theorem B1526219 : Blo 714321 1526219 := bstep (se 1 (by rfl) ⟨1144664, by rfl⟩ : syracuseStep 1526219 = 2289329) B2289329
theorem B1362433 : Blo 714321 1362433 := bstep (se 2 (by rfl) ⟨510912, by rfl⟩ : syracuseStep 1362433 = 1021825) B1021825
theorem B805387 : Blo 714321 805387 := bstep (se 1 (by rfl) ⟨604040, by rfl⟩ : syracuseStep 805387 = 1208081) B1208081
theorem B805495 : Blo 714321 805495 := bstep (se 1 (by rfl) ⟨604121, by rfl⟩ : syracuseStep 805495 = 1208243) B1208243
theorem B805675 : Blo 714321 805675 := bstep (se 1 (by rfl) ⟨604256, by rfl⟩ : syracuseStep 805675 = 1208513) B1208513
theorem B2411315 : Blo 714321 2411315 := bstep (se 1 (by rfl) ⟨1808486, by rfl⟩ : syracuseStep 2411315 = 3616973) B3616973
theorem B805783 : Blo 714321 805783 := bstep (se 1 (by rfl) ⟨604337, by rfl⟩ : syracuseStep 805783 = 1208675) B1208675
theorem B1526681 : Blo 714321 1526681 := bstep (se 2 (by rfl) ⟨572505, by rfl⟩ : syracuseStep 1526681 = 1145011) B1145011
theorem B1362881 : Blo 714321 1362881 := bstep (se 2 (by rfl) ⟨511080, by rfl⟩ : syracuseStep 1362881 = 1022161) B1022161
theorem B1723339 : Blo 714321 1723339 := bstep (se 1 (by rfl) ⟨1292504, by rfl⟩ : syracuseStep 1723339 = 2585009) B2585009
theorem B2411585 : Blo 714321 2411585 := bstep (se 2 (by rfl) ⟨904344, by rfl⟩ : syracuseStep 2411585 = 1808689) B1808689
theorem B805963 : Blo 714321 805963 := bstep (se 1 (by rfl) ⟨604472, by rfl⟩ : syracuseStep 805963 = 1208945) B1208945
theorem B7752779 : Blo 714321 7752779 := bstep (se 1 (by rfl) ⟨5814584, by rfl⟩ : syracuseStep 7752779 = 11629169) B11629169
theorem B904279 : Blo 714321 904279 := bstep (se 1 (by rfl) ⟨678209, by rfl⟩ : syracuseStep 904279 = 1356419) B1356419
theorem B1723571 : Blo 714321 1723571 := bstep (se 1 (by rfl) ⟨1292678, by rfl⟩ : syracuseStep 1723571 = 2585357) B2585357
theorem B806071 : Blo 714321 806071 := bstep (se 1 (by rfl) ⟨604553, by rfl⟩ : syracuseStep 806071 = 1209107) B1209107
theorem B3493081 : Blo 714321 3493081 := bstep (se 2 (by rfl) ⟨1309905, by rfl⟩ : syracuseStep 3493081 = 2619811) B2619811
theorem B1723609 : Blo 714321 1723609 := bstep (se 2 (by rfl) ⟨646353, by rfl⟩ : syracuseStep 1723609 = 1292707) B1292707
theorem B1363223 : Blo 714321 1363223 := bstep (se 1 (by rfl) ⟨1022417, by rfl⟩ : syracuseStep 1363223 = 2044835) B2044835
theorem B806251 : Blo 714321 806251 := bstep (se 1 (by rfl) ⟨604688, by rfl⟩ : syracuseStep 806251 = 1209377) B1209377
theorem B806359 : Blo 714321 806359 := bstep (se 1 (by rfl) ⟨604769, by rfl⟩ : syracuseStep 806359 = 1209539) B1209539
theorem B2412125 : Blo 714321 2412125 := bstep (se 3 (by rfl) ⟨452273, by rfl⟩ : syracuseStep 2412125 = 904547) B904547
theorem B806539 : Blo 714321 806539 := bstep (se 1 (by rfl) ⟨604904, by rfl⟩ : syracuseStep 806539 = 1209809) B1209809
theorem B806647 : Blo 714321 806647 := bstep (se 1 (by rfl) ⟨604985, by rfl⟩ : syracuseStep 806647 = 1209971) B1209971
theorem B3624749 : Blo 714321 3624749 := bstep (se 3 (by rfl) ⟨679640, by rfl⟩ : syracuseStep 3624749 = 1359281) B1359281
theorem B806827 : Blo 714321 806827 := bstep (se 1 (by rfl) ⟨605120, by rfl⟩ : syracuseStep 806827 = 1210241) B1210241
theorem B5427161 : Blo 714321 5427161 := bstep (se 2 (by rfl) ⟨2035185, by rfl⟩ : syracuseStep 5427161 = 4070371) B4070371
theorem B806935 : Blo 714321 806935 := bstep (se 1 (by rfl) ⟨605201, by rfl⟩ : syracuseStep 806935 = 1210403) B1210403
theorem B1527859 : Blo 714321 1527859 := bstep (se 1 (by rfl) ⟨1145894, by rfl⟩ : syracuseStep 1527859 = 2291789) B2291789
theorem B5525597 : Blo 714321 5525597 := bstep (se 3 (by rfl) ⟨1036049, by rfl⟩ : syracuseStep 5525597 = 2072099) B2072099
theorem B807115 : Blo 714321 807115 := bstep (se 1 (by rfl) ⟨605336, by rfl⟩ : syracuseStep 807115 = 1210673) B1210673
theorem B807223 : Blo 714321 807223 := bstep (se 1 (by rfl) ⟨605417, by rfl⟩ : syracuseStep 807223 = 1210835) B1210835
theorem B3068225 : Blo 714321 3068225 := bstep (se 2 (by rfl) ⟨1150584, by rfl⟩ : syracuseStep 3068225 = 2301169) B2301169
theorem B807403 : Blo 714321 807403 := bstep (se 1 (by rfl) ⟨605552, by rfl⟩ : syracuseStep 807403 = 1211105) B1211105
theorem B1528321 : Blo 714321 1528321 := bstep (se 2 (by rfl) ⟨573120, by rfl⟩ : syracuseStep 1528321 = 1146241) B1146241
theorem B12440081 : Blo 714321 12440081 := bstep (se 2 (by rfl) ⟨4665030, by rfl⟩ : syracuseStep 12440081 = 9330061) B9330061
theorem B3265069 : Blo 714321 3265069 := bstep (se 3 (by rfl) ⟨612200, by rfl⟩ : syracuseStep 3265069 = 1224401) B1224401
theorem B1724993 : Blo 714321 1724993 := bstep (se 2 (by rfl) ⟨646872, by rfl⟩ : syracuseStep 1724993 = 1293745) B1293745
theorem B807511 : Blo 714321 807511 := bstep (se 1 (by rfl) ⟨605633, by rfl⟩ : syracuseStep 807511 = 1211267) B1211267
theorem B2413259 : Blo 714321 2413259 := bstep (se 1 (by rfl) ⟨1809944, by rfl⟩ : syracuseStep 2413259 = 3619889) B3619889
theorem B905995 : Blo 714321 905995 := bstep (se 1 (by rfl) ⟨679496, by rfl⟩ : syracuseStep 905995 = 1358993) B1358993
theorem B807691 : Blo 714321 807691 := bstep (se 1 (by rfl) ⟨605768, by rfl⟩ : syracuseStep 807691 = 1211537) B1211537
theorem B2577197 : Blo 714321 2577197 := bstep (se 3 (by rfl) ⟨483224, by rfl⟩ : syracuseStep 2577197 = 966449) B966449
theorem B10343213 : Blo 714321 10343213 := bstep (se 3 (by rfl) ⟨1939352, by rfl⟩ : syracuseStep 10343213 = 3878705) B3878705
theorem B807799 : Blo 714321 807799 := bstep (se 1 (by rfl) ⟨605849, by rfl⟩ : syracuseStep 807799 = 1211699) B1211699
theorem B2413529 : Blo 714321 2413529 := bstep (se 2 (by rfl) ⟨905073, by rfl⟩ : syracuseStep 2413529 = 1810147) B1810147
theorem B2184215 : Blo 714321 2184215 := bstep (se 1 (by rfl) ⟨1638161, by rfl⟩ : syracuseStep 2184215 = 3276323) B3276323
theorem B807979 : Blo 714321 807979 := bstep (se 1 (by rfl) ⟨605984, by rfl⟩ : syracuseStep 807979 = 1211969) B1211969
theorem B808087 : Blo 714321 808087 := bstep (se 1 (by rfl) ⟨606065, by rfl⟩ : syracuseStep 808087 = 1212131) B1212131
theorem B1529047 : Blo 714321 1529047 := bstep (se 1 (by rfl) ⟨1146785, by rfl⟩ : syracuseStep 1529047 = 2293571) B2293571
theorem B7853429 : Blo 714321 7853429 := bstep (se 5 (by rfl) ⟨368129, by rfl⟩ : syracuseStep 7853429 = 736259) B736259
theorem B1660313 : Blo 714321 1660313 := bstep (se 2 (by rfl) ⟨622617, by rfl⟩ : syracuseStep 1660313 = 1245235) B1245235
theorem B2414231 : Blo 714321 2414231 := bstep (se 1 (by rfl) ⟨1810673, by rfl⟩ : syracuseStep 2414231 = 3621347) B3621347
theorem B3102401 : Blo 714321 3102401 := bstep (se 2 (by rfl) ⟨1163400, by rfl⟩ : syracuseStep 3102401 = 2326801) B2326801
theorem B906967 : Blo 714321 906967 := bstep (se 1 (by rfl) ⟨680225, by rfl⟩ : syracuseStep 906967 = 1360451) B1360451
theorem B2578193 : Blo 714321 2578193 := bstep (se 2 (by rfl) ⟨966822, by rfl⟩ : syracuseStep 2578193 = 1933645) B1933645
theorem B2905931 : Blo 714321 2905931 := bstep (se 1 (by rfl) ⟨2179448, by rfl⟩ : syracuseStep 2905931 = 4358897) B4358897
theorem B1529867 : Blo 714321 1529867 := bstep (se 1 (by rfl) ⟨1147400, by rfl⟩ : syracuseStep 1529867 = 2294801) B2294801
theorem B2414771 : Blo 714321 2414771 := bstep (se 1 (by rfl) ⟨1811078, by rfl⟩ : syracuseStep 2414771 = 3622157) B3622157
theorem B5822765 : Blo 714321 5822765 := bstep (se 3 (by rfl) ⟨1091768, by rfl⟩ : syracuseStep 5822765 = 2183537) B2183537
theorem B2578781 : Blo 714321 2578781 := bstep (se 3 (by rfl) ⟨483521, by rfl⟩ : syracuseStep 2578781 = 967043) B967043
theorem B2415041 : Blo 714321 2415041 := bstep (se 2 (by rfl) ⟨905640, by rfl⟩ : syracuseStep 2415041 = 1811281) B1811281
theorem B1071563 : Blo 714321 1071563 := bstep (se 1 (by rfl) ⟨803672, by rfl⟩ : syracuseStep 1071563 = 1607345) B1607345
theorem B2447819 : Blo 714321 2447819 := bstep (se 1 (by rfl) ⟨1835864, by rfl⟩ : syracuseStep 2447819 = 3671729) B3671729
theorem B1071575 : Blo 714321 1071575 := bstep (se 1 (by rfl) ⟨803681, by rfl⟩ : syracuseStep 1071575 = 1607363) B1607363
theorem B907787 : Blo 714321 907787 := bstep (se 1 (by rfl) ⟨680840, by rfl⟩ : syracuseStep 907787 = 1361681) B1361681
theorem B1071641 : Blo 714321 1071641 := bstep (se 2 (by rfl) ⟨401865, by rfl⟩ : syracuseStep 1071641 = 803731) B803731
theorem B1071755 : Blo 714321 1071755 := bstep (se 1 (by rfl) ⟨803816, by rfl⟩ : syracuseStep 1071755 = 1607633) B1607633
theorem B1071767 : Blo 714321 1071767 := bstep (se 1 (by rfl) ⟨803825, by rfl⟩ : syracuseStep 1071767 = 1607651) B1607651
theorem B1071833 : Blo 714321 1071833 := bstep (se 2 (by rfl) ⟨401937, by rfl⟩ : syracuseStep 1071833 = 803875) B803875
theorem B1071947 : Blo 714321 1071947 := bstep (se 1 (by rfl) ⟨803960, by rfl⟩ : syracuseStep 1071947 = 1607921) B1607921
theorem B1071959 : Blo 714321 1071959 := bstep (se 1 (by rfl) ⟨803969, by rfl⟩ : syracuseStep 1071959 = 1607939) B1607939
theorem B1530713 : Blo 714321 1530713 := bstep (se 2 (by rfl) ⟨574017, by rfl⟩ : syracuseStep 1530713 = 1148035) B1148035
theorem B1072025 : Blo 714321 1072025 := bstep (se 2 (by rfl) ⟨402009, by rfl⟩ : syracuseStep 1072025 = 804019) B804019
theorem B7756721 : Blo 714321 7756721 := bstep (se 2 (by rfl) ⟨2908770, by rfl⟩ : syracuseStep 7756721 = 5817541) B5817541
theorem B2415581 : Blo 714321 2415581 := bstep (se 3 (by rfl) ⟨452921, by rfl⟩ : syracuseStep 2415581 = 905843) B905843
theorem B1072139 : Blo 714321 1072139 := bstep (se 1 (by rfl) ⟨804104, by rfl⟩ : syracuseStep 1072139 = 1608209) B1608209
theorem B2579473 : Blo 714321 2579473 := bstep (se 2 (by rfl) ⟨967302, by rfl⟩ : syracuseStep 2579473 = 1934605) B1934605
theorem B1072151 : Blo 714321 1072151 := bstep (se 1 (by rfl) ⟨804113, by rfl⟩ : syracuseStep 1072151 = 1608227) B1608227
theorem B2448407 : Blo 714321 2448407 := bstep (se 1 (by rfl) ⟨1836305, by rfl⟩ : syracuseStep 2448407 = 3672611) B3672611
theorem B1072217 : Blo 714321 1072217 := bstep (se 2 (by rfl) ⟨402081, by rfl⟩ : syracuseStep 1072217 = 804163) B804163
theorem B4086935 : Blo 714321 4086935 := bstep (se 1 (by rfl) ⟨3065201, by rfl⟩ : syracuseStep 4086935 = 6130403) B6130403
theorem B1072331 : Blo 714321 1072331 := bstep (se 1 (by rfl) ⟨804248, by rfl⟩ : syracuseStep 1072331 = 1608497) B1608497
theorem B908491 : Blo 714321 908491 := bstep (se 1 (by rfl) ⟨681368, by rfl⟩ : syracuseStep 908491 = 1362737) B1362737
theorem B1072343 : Blo 714321 1072343 := bstep (se 1 (by rfl) ⟨804257, by rfl⟩ : syracuseStep 1072343 = 1608515) B1608515
theorem B1072409 : Blo 714321 1072409 := bstep (se 2 (by rfl) ⟨402153, by rfl⟩ : syracuseStep 1072409 = 804307) B804307
theorem B5430563 : Blo 714321 5430563 := bstep (se 1 (by rfl) ⟨4072922, by rfl⟩ : syracuseStep 5430563 = 8145845) B8145845
theorem B1072523 : Blo 714321 1072523 := bstep (se 1 (by rfl) ⟨804392, by rfl⟩ : syracuseStep 1072523 = 1608785) B1608785
theorem B1072535 : Blo 714321 1072535 := bstep (se 1 (by rfl) ⟨804401, by rfl⟩ : syracuseStep 1072535 = 1608803) B1608803
theorem B908759 : Blo 714321 908759 := bstep (se 1 (by rfl) ⟨681569, by rfl⟩ : syracuseStep 908759 = 1363139) B1363139
theorem B1072601 : Blo 714321 1072601 := bstep (se 2 (by rfl) ⟨402225, by rfl⟩ : syracuseStep 1072601 = 804451) B804451
theorem B1531379 : Blo 714321 1531379 := bstep (se 1 (by rfl) ⟨1148534, by rfl⟩ : syracuseStep 1531379 = 2297069) B2297069
theorem B1072715 : Blo 714321 1072715 := bstep (se 1 (by rfl) ⟨804536, by rfl⟩ : syracuseStep 1072715 = 1609073) B1609073
theorem B1072727 : Blo 714321 1072727 := bstep (se 1 (by rfl) ⟨804545, by rfl⟩ : syracuseStep 1072727 = 1609091) B1609091
theorem B4349533 : Blo 714321 4349533 := bstep (se 3 (by rfl) ⟨815537, by rfl⟩ : syracuseStep 4349533 = 1631075) B1631075
theorem B3628637 : Blo 714321 3628637 := bstep (se 3 (by rfl) ⟨680369, by rfl⟩ : syracuseStep 3628637 = 1360739) B1360739
theorem B1072793 : Blo 714321 1072793 := bstep (se 2 (by rfl) ⟨402297, by rfl⟩ : syracuseStep 1072793 = 804595) B804595
theorem B1072907 : Blo 714321 1072907 := bstep (se 1 (by rfl) ⟨804680, by rfl⟩ : syracuseStep 1072907 = 1609361) B1609361
theorem B1072919 : Blo 714321 1072919 := bstep (se 1 (by rfl) ⟨804689, by rfl⟩ : syracuseStep 1072919 = 1609379) B1609379
theorem B26828597 : Blo 714321 26828597 := bstep (se 5 (by rfl) ⟨1257590, by rfl⟩ : syracuseStep 26828597 = 2515181) B2515181
theorem B1072985 : Blo 714321 1072985 := bstep (se 2 (by rfl) ⟨402369, by rfl⟩ : syracuseStep 1072985 = 804739) B804739
theorem B1073099 : Blo 714321 1073099 := bstep (se 1 (by rfl) ⟨804824, by rfl⟩ : syracuseStep 1073099 = 1609649) B1609649
theorem B1073111 : Blo 714321 1073111 := bstep (se 1 (by rfl) ⟨804833, by rfl⟩ : syracuseStep 1073111 = 1609667) B1609667
theorem B8708057 : Blo 714321 8708057 := bstep (se 2 (by rfl) ⟨3265521, by rfl⟩ : syracuseStep 8708057 = 6531043) B6531043
theorem B1073177 : Blo 714321 1073177 := bstep (se 2 (by rfl) ⟨402441, by rfl⟩ : syracuseStep 1073177 = 804883) B804883
theorem B2416715 : Blo 714321 2416715 := bstep (se 1 (by rfl) ⟨1812536, by rfl⟩ : syracuseStep 2416715 = 3625073) B3625073
theorem B83845205 : Blo 714321 83845205 := bstep (se 8 (by rfl) ⟨491280, by rfl⟩ : syracuseStep 83845205 = 982561) B982561
theorem B1073291 : Blo 714321 1073291 := bstep (se 1 (by rfl) ⟨804968, by rfl⟩ : syracuseStep 1073291 = 1609937) B1609937
theorem B1073303 : Blo 714321 1073303 := bstep (se 1 (by rfl) ⟨804977, by rfl⟩ : syracuseStep 1073303 = 1609955) B1609955
theorem B1073369 : Blo 714321 1073369 := bstep (se 2 (by rfl) ⟨402513, by rfl⟩ : syracuseStep 1073369 = 805027) B805027
theorem B1073483 : Blo 714321 1073483 := bstep (se 1 (by rfl) ⟨805112, by rfl⟩ : syracuseStep 1073483 = 1610225) B1610225
theorem B1073495 : Blo 714321 1073495 := bstep (se 1 (by rfl) ⟨805121, by rfl⟩ : syracuseStep 1073495 = 1610243) B1610243
theorem B2416985 : Blo 714321 2416985 := bstep (se 2 (by rfl) ⟨906369, by rfl⟩ : syracuseStep 2416985 = 1812739) B1812739
theorem B3268957 : Blo 714321 3268957 := bstep (se 3 (by rfl) ⟨612929, by rfl⟩ : syracuseStep 3268957 = 1225859) B1225859
theorem B1073561 : Blo 714321 1073561 := bstep (se 2 (by rfl) ⟨402585, by rfl⟩ : syracuseStep 1073561 = 805171) B805171
theorem B1532353 : Blo 714321 1532353 := bstep (se 2 (by rfl) ⟨574632, by rfl⟩ : syracuseStep 1532353 = 1149265) B1149265
theorem B1630681 : Blo 714321 1630681 := bstep (se 2 (by rfl) ⟨611505, by rfl⟩ : syracuseStep 1630681 = 1223011) B1223011
theorem B1073675 : Blo 714321 1073675 := bstep (se 1 (by rfl) ⟨805256, by rfl⟩ : syracuseStep 1073675 = 1610513) B1610513
theorem B1073687 : Blo 714321 1073687 := bstep (se 1 (by rfl) ⟨805265, by rfl⟩ : syracuseStep 1073687 = 1610531) B1610531
theorem B1073753 : Blo 714321 1073753 := bstep (se 2 (by rfl) ⟨402657, by rfl⟩ : syracuseStep 1073753 = 805315) B805315
theorem B1532609 : Blo 714321 1532609 := bstep (se 2 (by rfl) ⟨574728, by rfl⟩ : syracuseStep 1532609 = 1149457) B1149457
theorem B1073867 : Blo 714321 1073867 := bstep (se 1 (by rfl) ⟨805400, by rfl⟩ : syracuseStep 1073867 = 1610801) B1610801
theorem B1073879 : Blo 714321 1073879 := bstep (se 1 (by rfl) ⟨805409, by rfl⟩ : syracuseStep 1073879 = 1610819) B1610819
theorem B1532695 : Blo 714321 1532695 := bstep (se 1 (by rfl) ⟨1149521, by rfl⟩ : syracuseStep 1532695 = 2299043) B2299043
theorem B1073945 : Blo 714321 1073945 := bstep (se 2 (by rfl) ⟨402729, by rfl⟩ : syracuseStep 1073945 = 805459) B805459
theorem B4580171 : Blo 714321 4580171 := bstep (se 1 (by rfl) ⟨3435128, by rfl⟩ : syracuseStep 4580171 = 6870257) B6870257
theorem B2581379 : Blo 714321 2581379 := bstep (se 1 (by rfl) ⟨1936034, by rfl⟩ : syracuseStep 2581379 = 3872069) B3872069
theorem B1074059 : Blo 714321 1074059 := bstep (se 1 (by rfl) ⟨805544, by rfl⟩ : syracuseStep 1074059 = 1611089) B1611089
theorem B1074071 : Blo 714321 1074071 := bstep (se 1 (by rfl) ⟨805553, by rfl⟩ : syracuseStep 1074071 = 1611107) B1611107
theorem B1074137 : Blo 714321 1074137 := bstep (se 2 (by rfl) ⟨402801, by rfl⟩ : syracuseStep 1074137 = 805603) B805603
theorem B2417687 : Blo 714321 2417687 := bstep (se 1 (by rfl) ⟨1813265, by rfl⟩ : syracuseStep 2417687 = 3626531) B3626531
theorem B1074251 : Blo 714321 1074251 := bstep (se 1 (by rfl) ⟨805688, by rfl⟩ : syracuseStep 1074251 = 1611377) B1611377
theorem B1074263 : Blo 714321 1074263 := bstep (se 1 (by rfl) ⟨805697, by rfl⟩ : syracuseStep 1074263 = 1611395) B1611395
theorem B1074329 : Blo 714321 1074329 := bstep (se 2 (by rfl) ⟨402873, by rfl⟩ : syracuseStep 1074329 = 805747) B805747
theorem B1074443 : Blo 714321 1074443 := bstep (se 1 (by rfl) ⟨805832, by rfl⟩ : syracuseStep 1074443 = 1611665) B1611665
theorem B1074455 : Blo 714321 1074455 := bstep (se 1 (by rfl) ⟨805841, by rfl⟩ : syracuseStep 1074455 = 1611683) B1611683
theorem B1074521 : Blo 714321 1074521 := bstep (se 2 (by rfl) ⟨402945, by rfl⟩ : syracuseStep 1074521 = 805891) B805891
theorem B1074635 : Blo 714321 1074635 := bstep (se 1 (by rfl) ⟨805976, by rfl⟩ : syracuseStep 1074635 = 1611953) B1611953
theorem B1074647 : Blo 714321 1074647 := bstep (se 1 (by rfl) ⟨805985, by rfl⟩ : syracuseStep 1074647 = 1611971) B1611971
theorem B1074713 : Blo 714321 1074713 := bstep (se 2 (by rfl) ⟨403017, by rfl⟩ : syracuseStep 1074713 = 806035) B806035
theorem B2418227 : Blo 714321 2418227 := bstep (se 1 (by rfl) ⟨1813670, by rfl⟩ : syracuseStep 2418227 = 3627341) B3627341
theorem B714327 : Blo 714321 714327 := bstep (se 1 (by rfl) ⟨535745, by rfl⟩ : syracuseStep 714327 = 1071491) B1071491
theorem B1631831 : Blo 714321 1631831 := bstep (se 1 (by rfl) ⟨1223873, by rfl⟩ : syracuseStep 1631831 = 2447747) B2447747
theorem B714347 : Blo 714321 714347 := bstep (se 1 (by rfl) ⟨535760, by rfl⟩ : syracuseStep 714347 = 1071521) B1071521
theorem B714359 : Blo 714321 714359 := bstep (se 1 (by rfl) ⟨535769, by rfl⟩ : syracuseStep 714359 = 1071539) B1071539
theorem B714379 : Blo 714321 714379 := bstep (se 1 (by rfl) ⟨535784, by rfl⟩ : syracuseStep 714379 = 1071569) B1071569
theorem B1074827 : Blo 714321 1074827 := bstep (se 1 (by rfl) ⟨806120, by rfl⟩ : syracuseStep 1074827 = 1612241) B1612241
theorem B714391 : Blo 714321 714391 := bstep (se 1 (by rfl) ⟨535793, by rfl⟩ : syracuseStep 714391 = 1071587) B1071587
theorem B1074839 : Blo 714321 1074839 := bstep (se 1 (by rfl) ⟨806129, by rfl⟩ : syracuseStep 1074839 = 1612259) B1612259
theorem B3630743 : Blo 714321 3630743 := bstep (se 1 (by rfl) ⟨2723057, by rfl⟩ : syracuseStep 3630743 = 5446115) B5446115
theorem B714411 : Blo 714321 714411 := bstep (se 1 (by rfl) ⟨535808, by rfl⟩ : syracuseStep 714411 = 1071617) B1071617
theorem B714423 : Blo 714321 714423 := bstep (se 1 (by rfl) ⟨535817, by rfl⟩ : syracuseStep 714423 = 1071635) B1071635
theorem B714443 : Blo 714321 714443 := bstep (se 1 (by rfl) ⟨535832, by rfl⟩ : syracuseStep 714443 = 1071665) B1071665
theorem B714455 : Blo 714321 714455 := bstep (se 1 (by rfl) ⟨535841, by rfl⟩ : syracuseStep 714455 = 1071683) B1071683
theorem B1205975 : Blo 714321 1205975 := bstep (se 1 (by rfl) ⟨904481, by rfl⟩ : syracuseStep 1205975 = 1808963) B1808963
theorem B1074905 : Blo 714321 1074905 := bstep (se 2 (by rfl) ⟨403089, by rfl⟩ : syracuseStep 1074905 = 806179) B806179
theorem B714475 : Blo 714321 714475 := bstep (se 1 (by rfl) ⟨535856, by rfl⟩ : syracuseStep 714475 = 1071713) B1071713
theorem B714487 : Blo 714321 714487 := bstep (se 1 (by rfl) ⟨535865, by rfl⟩ : syracuseStep 714487 = 1071731) B1071731
theorem B2942723 : Blo 714321 2942723 := bstep (se 1 (by rfl) ⟨2207042, by rfl⟩ : syracuseStep 2942723 = 4414085) B4414085
theorem B714507 : Blo 714321 714507 := bstep (se 1 (by rfl) ⟨535880, by rfl⟩ : syracuseStep 714507 = 1071761) B1071761
theorem B714519 : Blo 714321 714519 := bstep (se 1 (by rfl) ⟨535889, by rfl⟩ : syracuseStep 714519 = 1071779) B1071779
theorem B714539 : Blo 714321 714539 := bstep (se 1 (by rfl) ⟨535904, by rfl⟩ : syracuseStep 714539 = 1071809) B1071809
theorem B714551 : Blo 714321 714551 := bstep (se 1 (by rfl) ⟨535913, by rfl⟩ : syracuseStep 714551 = 1071827) B1071827
theorem B2418497 : Blo 714321 2418497 := bstep (se 2 (by rfl) ⟨906936, by rfl⟩ : syracuseStep 2418497 = 1813873) B1813873
theorem B714571 : Blo 714321 714571 := bstep (se 1 (by rfl) ⟨535928, by rfl⟩ : syracuseStep 714571 = 1071857) B1071857
theorem B1075019 : Blo 714321 1075019 := bstep (se 1 (by rfl) ⟨806264, by rfl⟩ : syracuseStep 1075019 = 1612529) B1612529
theorem B714583 : Blo 714321 714583 := bstep (se 1 (by rfl) ⟨535937, by rfl⟩ : syracuseStep 714583 = 1071875) B1071875
theorem B1206103 : Blo 714321 1206103 := bstep (se 1 (by rfl) ⟨904577, by rfl⟩ : syracuseStep 1206103 = 1809155) B1809155
theorem B1075031 : Blo 714321 1075031 := bstep (se 1 (by rfl) ⟨806273, by rfl⟩ : syracuseStep 1075031 = 1612547) B1612547
theorem B714603 : Blo 714321 714603 := bstep (se 1 (by rfl) ⟨535952, by rfl⟩ : syracuseStep 714603 = 1071905) B1071905
theorem B714615 : Blo 714321 714615 := bstep (se 1 (by rfl) ⟨535961, by rfl⟩ : syracuseStep 714615 = 1071923) B1071923
theorem B714635 : Blo 714321 714635 := bstep (se 1 (by rfl) ⟨535976, by rfl⟩ : syracuseStep 714635 = 1071953) B1071953
theorem B714647 : Blo 714321 714647 := bstep (se 1 (by rfl) ⟨535985, by rfl⟩ : syracuseStep 714647 = 1071971) B1071971
theorem B1075097 : Blo 714321 1075097 := bstep (se 2 (by rfl) ⟨403161, by rfl⟩ : syracuseStep 1075097 = 806323) B806323
theorem B714667 : Blo 714321 714667 := bstep (se 1 (by rfl) ⟨536000, by rfl⟩ : syracuseStep 714667 = 1072001) B1072001
theorem B714679 : Blo 714321 714679 := bstep (se 1 (by rfl) ⟨536009, by rfl⟩ : syracuseStep 714679 = 1072019) B1072019
theorem B714699 : Blo 714321 714699 := bstep (se 1 (by rfl) ⟨536024, by rfl⟩ : syracuseStep 714699 = 1072049) B1072049
theorem B714711 : Blo 714321 714711 := bstep (se 1 (by rfl) ⟨536033, by rfl⟩ : syracuseStep 714711 = 1072067) B1072067
theorem B714731 : Blo 714321 714731 := bstep (se 1 (by rfl) ⟨536048, by rfl⟩ : syracuseStep 714731 = 1072097) B1072097
theorem B714743 : Blo 714321 714743 := bstep (se 1 (by rfl) ⟨536057, by rfl⟩ : syracuseStep 714743 = 1072115) B1072115
theorem B714763 : Blo 714321 714763 := bstep (se 1 (by rfl) ⟨536072, by rfl⟩ : syracuseStep 714763 = 1072145) B1072145
theorem B1075211 : Blo 714321 1075211 := bstep (se 1 (by rfl) ⟨806408, by rfl⟩ : syracuseStep 1075211 = 1612817) B1612817
theorem B714775 : Blo 714321 714775 := bstep (se 1 (by rfl) ⟨536081, by rfl⟩ : syracuseStep 714775 = 1072163) B1072163
theorem B1075223 : Blo 714321 1075223 := bstep (se 1 (by rfl) ⟨806417, by rfl⟩ : syracuseStep 1075223 = 1612835) B1612835
theorem B714795 : Blo 714321 714795 := bstep (se 1 (by rfl) ⟨536096, by rfl⟩ : syracuseStep 714795 = 1072193) B1072193
theorem B714807 : Blo 714321 714807 := bstep (se 1 (by rfl) ⟨536105, by rfl⟩ : syracuseStep 714807 = 1072211) B1072211
theorem B714827 : Blo 714321 714827 := bstep (se 1 (by rfl) ⟨536120, by rfl⟩ : syracuseStep 714827 = 1072241) B1072241
theorem B714839 : Blo 714321 714839 := bstep (se 1 (by rfl) ⟨536129, by rfl⟩ : syracuseStep 714839 = 1072259) B1072259
theorem B1075289 : Blo 714321 1075289 := bstep (se 2 (by rfl) ⟨403233, by rfl⟩ : syracuseStep 1075289 = 806467) B806467
theorem B714859 : Blo 714321 714859 := bstep (se 1 (by rfl) ⟨536144, by rfl⟩ : syracuseStep 714859 = 1072289) B1072289
theorem B714871 : Blo 714321 714871 := bstep (se 1 (by rfl) ⟨536153, by rfl⟩ : syracuseStep 714871 = 1072307) B1072307
theorem B714891 : Blo 714321 714891 := bstep (se 1 (by rfl) ⟨536168, by rfl⟩ : syracuseStep 714891 = 1072337) B1072337
theorem B714903 : Blo 714321 714903 := bstep (se 1 (by rfl) ⟨536177, by rfl⟩ : syracuseStep 714903 = 1072355) B1072355
theorem B714923 : Blo 714321 714923 := bstep (se 1 (by rfl) ⟨536192, by rfl⟩ : syracuseStep 714923 = 1072385) B1072385
theorem B714935 : Blo 714321 714935 := bstep (se 1 (by rfl) ⟨536201, by rfl⟩ : syracuseStep 714935 = 1072403) B1072403
theorem B714955 : Blo 714321 714955 := bstep (se 1 (by rfl) ⟨536216, by rfl⟩ : syracuseStep 714955 = 1072433) B1072433
theorem B1075403 : Blo 714321 1075403 := bstep (se 1 (by rfl) ⟨806552, by rfl⟩ : syracuseStep 1075403 = 1613105) B1613105
theorem B714967 : Blo 714321 714967 := bstep (se 1 (by rfl) ⟨536225, by rfl⟩ : syracuseStep 714967 = 1072451) B1072451
theorem B1075415 : Blo 714321 1075415 := bstep (se 1 (by rfl) ⟨806561, by rfl⟩ : syracuseStep 1075415 = 1613123) B1613123
theorem B714987 : Blo 714321 714987 := bstep (se 1 (by rfl) ⟨536240, by rfl⟩ : syracuseStep 714987 = 1072481) B1072481
theorem B714999 : Blo 714321 714999 := bstep (se 1 (by rfl) ⟨536249, by rfl⟩ : syracuseStep 714999 = 1072499) B1072499
theorem B12216581 : Blo 714321 12216581 := bstep (se 4 (by rfl) ⟨1145304, by rfl⟩ : syracuseStep 12216581 = 2290609) B2290609
theorem B715019 : Blo 714321 715019 := bstep (se 1 (by rfl) ⟨536264, by rfl⟩ : syracuseStep 715019 = 1072529) B1072529
theorem B715031 : Blo 714321 715031 := bstep (se 1 (by rfl) ⟨536273, by rfl⟩ : syracuseStep 715031 = 1072547) B1072547
theorem B1075481 : Blo 714321 1075481 := bstep (se 2 (by rfl) ⟨403305, by rfl⟩ : syracuseStep 1075481 = 806611) B806611
theorem B715051 : Blo 714321 715051 := bstep (se 1 (by rfl) ⟨536288, by rfl⟩ : syracuseStep 715051 = 1072577) B1072577
theorem B715063 : Blo 714321 715063 := bstep (se 1 (by rfl) ⟨536297, by rfl⟩ : syracuseStep 715063 = 1072595) B1072595
theorem B2713931 : Blo 714321 2713931 := bstep (se 1 (by rfl) ⟨2035448, by rfl⟩ : syracuseStep 2713931 = 4070897) B4070897
theorem B715083 : Blo 714321 715083 := bstep (se 1 (by rfl) ⟨536312, by rfl⟩ : syracuseStep 715083 = 1072625) B1072625
theorem B715095 : Blo 714321 715095 := bstep (se 1 (by rfl) ⟨536321, by rfl⟩ : syracuseStep 715095 = 1072643) B1072643
theorem B2713945 : Blo 714321 2713945 := bstep (se 2 (by rfl) ⟨1017729, by rfl⟩ : syracuseStep 2713945 = 2035459) B2035459
theorem B2419037 : Blo 714321 2419037 := bstep (se 3 (by rfl) ⟨453569, by rfl⟩ : syracuseStep 2419037 = 907139) B907139
theorem B715115 : Blo 714321 715115 := bstep (se 1 (by rfl) ⟨536336, by rfl⟩ : syracuseStep 715115 = 1072673) B1072673
theorem B715127 : Blo 714321 715127 := bstep (se 1 (by rfl) ⟨536345, by rfl⟩ : syracuseStep 715127 = 1072691) B1072691
theorem B715147 : Blo 714321 715147 := bstep (se 1 (by rfl) ⟨536360, by rfl⟩ : syracuseStep 715147 = 1072721) B1072721
theorem B1075595 : Blo 714321 1075595 := bstep (se 1 (by rfl) ⟨806696, by rfl⟩ : syracuseStep 1075595 = 1613393) B1613393
theorem B715159 : Blo 714321 715159 := bstep (se 1 (by rfl) ⟨536369, by rfl⟩ : syracuseStep 715159 = 1072739) B1072739
theorem B1075607 : Blo 714321 1075607 := bstep (se 1 (by rfl) ⟨806705, by rfl⟩ : syracuseStep 1075607 = 1613411) B1613411
theorem B715179 : Blo 714321 715179 := bstep (se 1 (by rfl) ⟨536384, by rfl⟩ : syracuseStep 715179 = 1072769) B1072769
theorem B5171633 : Blo 714321 5171633 := bstep (se 2 (by rfl) ⟨1939362, by rfl⟩ : syracuseStep 5171633 = 3878725) B3878725
theorem B715191 : Blo 714321 715191 := bstep (se 1 (by rfl) ⟨536393, by rfl⟩ : syracuseStep 715191 = 1072787) B1072787
theorem B1206731 : Blo 714321 1206731 := bstep (se 1 (by rfl) ⟨905048, by rfl⟩ : syracuseStep 1206731 = 1810097) B1810097
theorem B715211 : Blo 714321 715211 := bstep (se 1 (by rfl) ⟨536408, by rfl⟩ : syracuseStep 715211 = 1072817) B1072817
theorem B715223 : Blo 714321 715223 := bstep (se 1 (by rfl) ⟨536417, by rfl⟩ : syracuseStep 715223 = 1072835) B1072835
theorem B1075673 : Blo 714321 1075673 := bstep (se 2 (by rfl) ⟨403377, by rfl⟩ : syracuseStep 1075673 = 806755) B806755
theorem B715243 : Blo 714321 715243 := bstep (se 1 (by rfl) ⟨536432, by rfl⟩ : syracuseStep 715243 = 1072865) B1072865
theorem B715255 : Blo 714321 715255 := bstep (se 1 (by rfl) ⟨536441, by rfl⟩ : syracuseStep 715255 = 1072883) B1072883
theorem B715275 : Blo 714321 715275 := bstep (se 1 (by rfl) ⟨536456, by rfl⟩ : syracuseStep 715275 = 1072913) B1072913
theorem B715287 : Blo 714321 715287 := bstep (se 1 (by rfl) ⟨536465, by rfl⟩ : syracuseStep 715287 = 1072931) B1072931
theorem B715307 : Blo 714321 715307 := bstep (se 1 (by rfl) ⟨536480, by rfl⟩ : syracuseStep 715307 = 1072961) B1072961
theorem B715319 : Blo 714321 715319 := bstep (se 1 (by rfl) ⟨536489, by rfl⟩ : syracuseStep 715319 = 1072979) B1072979
theorem B1206859 : Blo 714321 1206859 := bstep (se 1 (by rfl) ⟨905144, by rfl⟩ : syracuseStep 1206859 = 1810289) B1810289
theorem B715339 : Blo 714321 715339 := bstep (se 1 (by rfl) ⟨536504, by rfl⟩ : syracuseStep 715339 = 1073009) B1073009
theorem B1075787 : Blo 714321 1075787 := bstep (se 1 (by rfl) ⟨806840, by rfl⟩ : syracuseStep 1075787 = 1613681) B1613681
theorem B715351 : Blo 714321 715351 := bstep (se 1 (by rfl) ⟨536513, by rfl⟩ : syracuseStep 715351 = 1073027) B1073027
theorem B1075799 : Blo 714321 1075799 := bstep (se 1 (by rfl) ⟨806849, by rfl⟩ : syracuseStep 1075799 = 1613699) B1613699
theorem B715371 : Blo 714321 715371 := bstep (se 1 (by rfl) ⟨536528, by rfl⟩ : syracuseStep 715371 = 1073057) B1073057
theorem B715383 : Blo 714321 715383 := bstep (se 1 (by rfl) ⟨536537, by rfl⟩ : syracuseStep 715383 = 1073075) B1073075
theorem B715403 : Blo 714321 715403 := bstep (se 1 (by rfl) ⟨536552, by rfl⟩ : syracuseStep 715403 = 1073105) B1073105
theorem B715415 : Blo 714321 715415 := bstep (se 1 (by rfl) ⟨536561, by rfl⟩ : syracuseStep 715415 = 1073123) B1073123
theorem B5171863 : Blo 714321 5171863 := bstep (se 1 (by rfl) ⟨3878897, by rfl⟩ : syracuseStep 5171863 = 7757795) B7757795
theorem B1075865 : Blo 714321 1075865 := bstep (se 2 (by rfl) ⟨403449, by rfl⟩ : syracuseStep 1075865 = 806899) B806899
theorem B715435 : Blo 714321 715435 := bstep (se 1 (by rfl) ⟨536576, by rfl⟩ : syracuseStep 715435 = 1073153) B1073153
theorem B715447 : Blo 714321 715447 := bstep (se 1 (by rfl) ⟨536585, by rfl⟩ : syracuseStep 715447 = 1073171) B1073171
theorem B715467 : Blo 714321 715467 := bstep (se 1 (by rfl) ⟨536600, by rfl⟩ : syracuseStep 715467 = 1073201) B1073201
theorem B715479 : Blo 714321 715479 := bstep (se 1 (by rfl) ⟨536609, by rfl⟩ : syracuseStep 715479 = 1073219) B1073219
theorem B1207001 : Blo 714321 1207001 := bstep (se 2 (by rfl) ⟨452625, by rfl⟩ : syracuseStep 1207001 = 905251) B905251
theorem B715499 : Blo 714321 715499 := bstep (se 1 (by rfl) ⟨536624, by rfl⟩ : syracuseStep 715499 = 1073249) B1073249
theorem B715511 : Blo 714321 715511 := bstep (se 1 (by rfl) ⟨536633, by rfl⟩ : syracuseStep 715511 = 1073267) B1073267
theorem B715531 : Blo 714321 715531 := bstep (se 1 (by rfl) ⟨536648, by rfl⟩ : syracuseStep 715531 = 1073297) B1073297
theorem B1075979 : Blo 714321 1075979 := bstep (se 1 (by rfl) ⟨806984, by rfl⟩ : syracuseStep 1075979 = 1613969) B1613969
theorem B715543 : Blo 714321 715543 := bstep (se 1 (by rfl) ⟨536657, by rfl⟩ : syracuseStep 715543 = 1073315) B1073315
theorem B1075991 : Blo 714321 1075991 := bstep (se 1 (by rfl) ⟨806993, by rfl⟩ : syracuseStep 1075991 = 1613987) B1613987
theorem B715563 : Blo 714321 715563 := bstep (se 1 (by rfl) ⟨536672, by rfl⟩ : syracuseStep 715563 = 1073345) B1073345
theorem B715575 : Blo 714321 715575 := bstep (se 1 (by rfl) ⟨536681, by rfl⟩ : syracuseStep 715575 = 1073363) B1073363
theorem B715595 : Blo 714321 715595 := bstep (se 1 (by rfl) ⟨536696, by rfl⟩ : syracuseStep 715595 = 1073393) B1073393
theorem B715607 : Blo 714321 715607 := bstep (se 1 (by rfl) ⟨536705, by rfl⟩ : syracuseStep 715607 = 1073411) B1073411
theorem B1207129 : Blo 714321 1207129 := bstep (se 2 (by rfl) ⟨452673, by rfl⟩ : syracuseStep 1207129 = 905347) B905347
theorem B1076057 : Blo 714321 1076057 := bstep (se 2 (by rfl) ⟨403521, by rfl⟩ : syracuseStep 1076057 = 807043) B807043
theorem B715627 : Blo 714321 715627 := bstep (se 1 (by rfl) ⟨536720, by rfl⟩ : syracuseStep 715627 = 1073441) B1073441
theorem B715639 : Blo 714321 715639 := bstep (se 1 (by rfl) ⟨536729, by rfl⟩ : syracuseStep 715639 = 1073459) B1073459
theorem B715659 : Blo 714321 715659 := bstep (se 1 (by rfl) ⟨536744, by rfl⟩ : syracuseStep 715659 = 1073489) B1073489
theorem B715671 : Blo 714321 715671 := bstep (se 1 (by rfl) ⟨536753, by rfl⟩ : syracuseStep 715671 = 1073507) B1073507
theorem B715691 : Blo 714321 715691 := bstep (se 1 (by rfl) ⟨536768, by rfl⟩ : syracuseStep 715691 = 1073537) B1073537
theorem B715703 : Blo 714321 715703 := bstep (se 1 (by rfl) ⟨536777, by rfl⟩ : syracuseStep 715703 = 1073555) B1073555
theorem B715723 : Blo 714321 715723 := bstep (se 1 (by rfl) ⟨536792, by rfl⟩ : syracuseStep 715723 = 1073585) B1073585
theorem B1076171 : Blo 714321 1076171 := bstep (se 1 (by rfl) ⟨807128, by rfl⟩ : syracuseStep 1076171 = 1614257) B1614257
theorem B715735 : Blo 714321 715735 := bstep (se 1 (by rfl) ⟨536801, by rfl⟩ : syracuseStep 715735 = 1073603) B1073603
theorem B1076183 : Blo 714321 1076183 := bstep (se 1 (by rfl) ⟨807137, by rfl⟩ : syracuseStep 1076183 = 1614275) B1614275
theorem B715755 : Blo 714321 715755 := bstep (se 1 (by rfl) ⟨536816, by rfl⟩ : syracuseStep 715755 = 1073633) B1073633
theorem B715767 : Blo 714321 715767 := bstep (se 1 (by rfl) ⟨536825, by rfl⟩ : syracuseStep 715767 = 1073651) B1073651
theorem B715787 : Blo 714321 715787 := bstep (se 1 (by rfl) ⟨536840, by rfl⟩ : syracuseStep 715787 = 1073681) B1073681
theorem B2583569 : Blo 714321 2583569 := bstep (se 2 (by rfl) ⟨968838, by rfl⟩ : syracuseStep 2583569 = 1937677) B1937677
theorem B715799 : Blo 714321 715799 := bstep (se 1 (by rfl) ⟨536849, by rfl⟩ : syracuseStep 715799 = 1073699) B1073699
theorem B1076249 : Blo 714321 1076249 := bstep (se 2 (by rfl) ⟨403593, by rfl⟩ : syracuseStep 1076249 = 807187) B807187
theorem B715819 : Blo 714321 715819 := bstep (se 1 (by rfl) ⟨536864, by rfl⟩ : syracuseStep 715819 = 1073729) B1073729
theorem B715831 : Blo 714321 715831 := bstep (se 1 (by rfl) ⟨536873, by rfl⟩ : syracuseStep 715831 = 1073747) B1073747
theorem B19557445 : Blo 714321 19557445 := bstep (se 4 (by rfl) ⟨1833510, by rfl⟩ : syracuseStep 19557445 = 3667021) B3667021
theorem B715851 : Blo 714321 715851 := bstep (se 1 (by rfl) ⟨536888, by rfl⟩ : syracuseStep 715851 = 1073777) B1073777
theorem B715863 : Blo 714321 715863 := bstep (se 1 (by rfl) ⟨536897, by rfl⟩ : syracuseStep 715863 = 1073795) B1073795
theorem B715883 : Blo 714321 715883 := bstep (se 1 (by rfl) ⟨536912, by rfl⟩ : syracuseStep 715883 = 1073825) B1073825
theorem B715895 : Blo 714321 715895 := bstep (se 1 (by rfl) ⟨536921, by rfl⟩ : syracuseStep 715895 = 1073843) B1073843
theorem B715915 : Blo 714321 715915 := bstep (se 1 (by rfl) ⟨536936, by rfl⟩ : syracuseStep 715915 = 1073873) B1073873
theorem B1076363 : Blo 714321 1076363 := bstep (se 1 (by rfl) ⟨807272, by rfl⟩ : syracuseStep 1076363 = 1614545) B1614545
theorem B715927 : Blo 714321 715927 := bstep (se 1 (by rfl) ⟨536945, by rfl⟩ : syracuseStep 715927 = 1073891) B1073891
theorem B1076375 : Blo 714321 1076375 := bstep (se 1 (by rfl) ⟨807281, by rfl⟩ : syracuseStep 1076375 = 1614563) B1614563
theorem B715947 : Blo 714321 715947 := bstep (se 1 (by rfl) ⟨536960, by rfl⟩ : syracuseStep 715947 = 1073921) B1073921
theorem B715959 : Blo 714321 715959 := bstep (se 1 (by rfl) ⟨536969, by rfl⟩ : syracuseStep 715959 = 1073939) B1073939
theorem B715979 : Blo 714321 715979 := bstep (se 1 (by rfl) ⟨536984, by rfl⟩ : syracuseStep 715979 = 1073969) B1073969
theorem B715991 : Blo 714321 715991 := bstep (se 1 (by rfl) ⟨536993, by rfl⟩ : syracuseStep 715991 = 1073987) B1073987
theorem B1076441 : Blo 714321 1076441 := bstep (se 2 (by rfl) ⟨403665, by rfl⟩ : syracuseStep 1076441 = 807331) B807331
theorem B716011 : Blo 714321 716011 := bstep (se 1 (by rfl) ⟨537008, by rfl⟩ : syracuseStep 716011 = 1074017) B1074017
theorem B716023 : Blo 714321 716023 := bstep (se 1 (by rfl) ⟨537017, by rfl⟩ : syracuseStep 716023 = 1074035) B1074035
theorem B716043 : Blo 714321 716043 := bstep (se 1 (by rfl) ⟨537032, by rfl⟩ : syracuseStep 716043 = 1074065) B1074065
theorem B2714903 : Blo 714321 2714903 := bstep (se 1 (by rfl) ⟨2036177, by rfl⟩ : syracuseStep 2714903 = 4072355) B4072355
theorem B716055 : Blo 714321 716055 := bstep (se 1 (by rfl) ⟨537041, by rfl⟩ : syracuseStep 716055 = 1074083) B1074083
theorem B716075 : Blo 714321 716075 := bstep (se 1 (by rfl) ⟨537056, by rfl⟩ : syracuseStep 716075 = 1074113) B1074113
theorem B716087 : Blo 714321 716087 := bstep (se 1 (by rfl) ⟨537065, by rfl⟩ : syracuseStep 716087 = 1074131) B1074131
theorem B716107 : Blo 714321 716107 := bstep (se 1 (by rfl) ⟨537080, by rfl⟩ : syracuseStep 716107 = 1074161) B1074161
theorem B1076555 : Blo 714321 1076555 := bstep (se 1 (by rfl) ⟨807416, by rfl⟩ : syracuseStep 1076555 = 1614833) B1614833
theorem B716119 : Blo 714321 716119 := bstep (se 1 (by rfl) ⟨537089, by rfl⟩ : syracuseStep 716119 = 1074179) B1074179
theorem B1076567 : Blo 714321 1076567 := bstep (se 1 (by rfl) ⟨807425, by rfl⟩ : syracuseStep 1076567 = 1614851) B1614851
theorem B4582757 : Blo 714321 4582757 := bstep (se 4 (by rfl) ⟨429633, by rfl⟩ : syracuseStep 4582757 = 859267) B859267
theorem B7761253 : Blo 714321 7761253 := bstep (se 4 (by rfl) ⟨727617, by rfl⟩ : syracuseStep 7761253 = 1455235) B1455235
theorem B716139 : Blo 714321 716139 := bstep (se 1 (by rfl) ⟨537104, by rfl⟩ : syracuseStep 716139 = 1074209) B1074209
theorem B716151 : Blo 714321 716151 := bstep (se 1 (by rfl) ⟨537113, by rfl⟩ : syracuseStep 716151 = 1074227) B1074227
theorem B716171 : Blo 714321 716171 := bstep (se 1 (by rfl) ⟨537128, by rfl⟩ : syracuseStep 716171 = 1074257) B1074257
theorem B1207703 : Blo 714321 1207703 := bstep (se 1 (by rfl) ⟨905777, by rfl⟩ : syracuseStep 1207703 = 1811555) B1811555
theorem B716183 : Blo 714321 716183 := bstep (se 1 (by rfl) ⟨537137, by rfl⟩ : syracuseStep 716183 = 1074275) B1074275
theorem B1076633 : Blo 714321 1076633 := bstep (se 2 (by rfl) ⟨403737, by rfl⟩ : syracuseStep 1076633 = 807475) B807475
theorem B716203 : Blo 714321 716203 := bstep (se 1 (by rfl) ⟨537152, by rfl⟩ : syracuseStep 716203 = 1074305) B1074305
theorem B716215 : Blo 714321 716215 := bstep (se 1 (by rfl) ⟨537161, by rfl⟩ : syracuseStep 716215 = 1074323) B1074323
theorem B2584001 : Blo 714321 2584001 := bstep (se 2 (by rfl) ⟨969000, by rfl⟩ : syracuseStep 2584001 = 1938001) B1938001
theorem B716235 : Blo 714321 716235 := bstep (se 1 (by rfl) ⟨537176, by rfl⟩ : syracuseStep 716235 = 1074353) B1074353
theorem B2420171 : Blo 714321 2420171 := bstep (se 1 (by rfl) ⟨1815128, by rfl⟩ : syracuseStep 2420171 = 3630257) B3630257
theorem B716247 : Blo 714321 716247 := bstep (se 1 (by rfl) ⟨537185, by rfl⟩ : syracuseStep 716247 = 1074371) B1074371
theorem B716267 : Blo 714321 716267 := bstep (se 1 (by rfl) ⟨537200, by rfl⟩ : syracuseStep 716267 = 1074401) B1074401
theorem B716279 : Blo 714321 716279 := bstep (se 1 (by rfl) ⟨537209, by rfl⟩ : syracuseStep 716279 = 1074419) B1074419
theorem B716299 : Blo 714321 716299 := bstep (se 1 (by rfl) ⟨537224, by rfl⟩ : syracuseStep 716299 = 1074449) B1074449
theorem B1076747 : Blo 714321 1076747 := bstep (se 1 (by rfl) ⟨807560, by rfl⟩ : syracuseStep 1076747 = 1615121) B1615121
theorem B1207831 : Blo 714321 1207831 := bstep (se 1 (by rfl) ⟨905873, by rfl⟩ : syracuseStep 1207831 = 1811747) B1811747
theorem B716311 : Blo 714321 716311 := bstep (se 1 (by rfl) ⟨537233, by rfl⟩ : syracuseStep 716311 = 1074467) B1074467
theorem B1076759 : Blo 714321 1076759 := bstep (se 1 (by rfl) ⟨807569, by rfl⟩ : syracuseStep 1076759 = 1615139) B1615139
theorem B716331 : Blo 714321 716331 := bstep (se 1 (by rfl) ⟨537248, by rfl⟩ : syracuseStep 716331 = 1074497) B1074497
theorem B6123053 : Blo 714321 6123053 := bstep (se 3 (by rfl) ⟨1148072, by rfl⟩ : syracuseStep 6123053 = 2296145) B2296145
theorem B716343 : Blo 714321 716343 := bstep (se 1 (by rfl) ⟨537257, by rfl⟩ : syracuseStep 716343 = 1074515) B1074515
theorem B716363 : Blo 714321 716363 := bstep (se 1 (by rfl) ⟨537272, by rfl⟩ : syracuseStep 716363 = 1074545) B1074545
theorem B716375 : Blo 714321 716375 := bstep (se 1 (by rfl) ⟨537281, by rfl⟩ : syracuseStep 716375 = 1074563) B1074563
theorem B1076825 : Blo 714321 1076825 := bstep (se 2 (by rfl) ⟨403809, by rfl⟩ : syracuseStep 1076825 = 807619) B807619
theorem B3862117 : Blo 714321 3862117 := bstep (se 4 (by rfl) ⟨362073, by rfl⟩ : syracuseStep 3862117 = 724147) B724147
theorem B716395 : Blo 714321 716395 := bstep (se 1 (by rfl) ⟨537296, by rfl⟩ : syracuseStep 716395 = 1074593) B1074593
theorem B716407 : Blo 714321 716407 := bstep (se 1 (by rfl) ⟨537305, by rfl⟩ : syracuseStep 716407 = 1074611) B1074611
theorem B716427 : Blo 714321 716427 := bstep (se 1 (by rfl) ⟨537320, by rfl⟩ : syracuseStep 716427 = 1074641) B1074641
theorem B716439 : Blo 714321 716439 := bstep (se 1 (by rfl) ⟨537329, by rfl⟩ : syracuseStep 716439 = 1074659) B1074659
theorem B716459 : Blo 714321 716459 := bstep (se 1 (by rfl) ⟨537344, by rfl⟩ : syracuseStep 716459 = 1074689) B1074689
theorem B716471 : Blo 714321 716471 := bstep (se 1 (by rfl) ⟨537353, by rfl⟩ : syracuseStep 716471 = 1074707) B1074707
theorem B716491 : Blo 714321 716491 := bstep (se 1 (by rfl) ⟨537368, by rfl⟩ : syracuseStep 716491 = 1074737) B1074737
theorem B1076939 : Blo 714321 1076939 := bstep (se 1 (by rfl) ⟨807704, by rfl⟩ : syracuseStep 1076939 = 1615409) B1615409
theorem B716503 : Blo 714321 716503 := bstep (se 1 (by rfl) ⟨537377, by rfl⟩ : syracuseStep 716503 = 1074755) B1074755
theorem B1076951 : Blo 714321 1076951 := bstep (se 1 (by rfl) ⟨807713, by rfl⟩ : syracuseStep 1076951 = 1615427) B1615427
theorem B2420441 : Blo 714321 2420441 := bstep (se 2 (by rfl) ⟨907665, by rfl⟩ : syracuseStep 2420441 = 1815331) B1815331
theorem B716523 : Blo 714321 716523 := bstep (se 1 (by rfl) ⟨537392, by rfl⟩ : syracuseStep 716523 = 1074785) B1074785
theorem B716535 : Blo 714321 716535 := bstep (se 1 (by rfl) ⟨537401, by rfl⟩ : syracuseStep 716535 = 1074803) B1074803
theorem B716555 : Blo 714321 716555 := bstep (se 1 (by rfl) ⟨537416, by rfl⟩ : syracuseStep 716555 = 1074833) B1074833
theorem B716567 : Blo 714321 716567 := bstep (se 1 (by rfl) ⟨537425, by rfl⟩ : syracuseStep 716567 = 1074851) B1074851
theorem B1077017 : Blo 714321 1077017 := bstep (se 2 (by rfl) ⟨403881, by rfl⟩ : syracuseStep 1077017 = 807763) B807763
theorem B716587 : Blo 714321 716587 := bstep (se 1 (by rfl) ⟨537440, by rfl⟩ : syracuseStep 716587 = 1074881) B1074881
theorem B716599 : Blo 714321 716599 := bstep (se 1 (by rfl) ⟨537449, by rfl⟩ : syracuseStep 716599 = 1074899) B1074899
theorem B716619 : Blo 714321 716619 := bstep (se 1 (by rfl) ⟨537464, by rfl⟩ : syracuseStep 716619 = 1074929) B1074929
theorem B716631 : Blo 714321 716631 := bstep (se 1 (by rfl) ⟨537473, by rfl⟩ : syracuseStep 716631 = 1074947) B1074947
theorem B3108701 : Blo 714321 3108701 := bstep (se 3 (by rfl) ⟨582881, by rfl⟩ : syracuseStep 3108701 = 1165763) B1165763
theorem B716651 : Blo 714321 716651 := bstep (se 1 (by rfl) ⟨537488, by rfl⟩ : syracuseStep 716651 = 1074977) B1074977
theorem B716663 : Blo 714321 716663 := bstep (se 1 (by rfl) ⟨537497, by rfl⟩ : syracuseStep 716663 = 1074995) B1074995
theorem B716683 : Blo 714321 716683 := bstep (se 1 (by rfl) ⟨537512, by rfl⟩ : syracuseStep 716683 = 1075025) B1075025
theorem B1077131 : Blo 714321 1077131 := bstep (se 1 (by rfl) ⟨807848, by rfl⟩ : syracuseStep 1077131 = 1615697) B1615697
theorem B716695 : Blo 714321 716695 := bstep (se 1 (by rfl) ⟨537521, by rfl⟩ : syracuseStep 716695 = 1075043) B1075043
theorem B1077143 : Blo 714321 1077143 := bstep (se 1 (by rfl) ⟨807857, by rfl⟩ : syracuseStep 1077143 = 1615715) B1615715
theorem B716715 : Blo 714321 716715 := bstep (se 1 (by rfl) ⟨537536, by rfl⟩ : syracuseStep 716715 = 1075073) B1075073
theorem B2584493 : Blo 714321 2584493 := bstep (se 3 (by rfl) ⟨484592, by rfl⟩ : syracuseStep 2584493 = 969185) B969185
theorem B716727 : Blo 714321 716727 := bstep (se 1 (by rfl) ⟨537545, by rfl⟩ : syracuseStep 716727 = 1075091) B1075091
theorem B716747 : Blo 714321 716747 := bstep (se 1 (by rfl) ⟨537560, by rfl⟩ : syracuseStep 716747 = 1075121) B1075121
theorem B716759 : Blo 714321 716759 := bstep (se 1 (by rfl) ⟨537569, by rfl⟩ : syracuseStep 716759 = 1075139) B1075139
theorem B1077209 : Blo 714321 1077209 := bstep (se 2 (by rfl) ⟨403953, by rfl⟩ : syracuseStep 1077209 = 807907) B807907
theorem B716779 : Blo 714321 716779 := bstep (se 1 (by rfl) ⟨537584, by rfl⟩ : syracuseStep 716779 = 1075169) B1075169
theorem B716791 : Blo 714321 716791 := bstep (se 1 (by rfl) ⟨537593, by rfl⟩ : syracuseStep 716791 = 1075187) B1075187
theorem B716811 : Blo 714321 716811 := bstep (se 1 (by rfl) ⟨537608, by rfl⟩ : syracuseStep 716811 = 1075217) B1075217
theorem B716823 : Blo 714321 716823 := bstep (se 1 (by rfl) ⟨537617, by rfl⟩ : syracuseStep 716823 = 1075235) B1075235
theorem B716843 : Blo 714321 716843 := bstep (se 1 (by rfl) ⟨537632, by rfl⟩ : syracuseStep 716843 = 1075265) B1075265
theorem B716855 : Blo 714321 716855 := bstep (se 1 (by rfl) ⟨537641, by rfl⟩ : syracuseStep 716855 = 1075283) B1075283
theorem B716875 : Blo 714321 716875 := bstep (se 1 (by rfl) ⟨537656, by rfl⟩ : syracuseStep 716875 = 1075313) B1075313
theorem B1077323 : Blo 714321 1077323 := bstep (se 1 (by rfl) ⟨807992, by rfl⟩ : syracuseStep 1077323 = 1615985) B1615985
theorem B716887 : Blo 714321 716887 := bstep (se 1 (by rfl) ⟨537665, by rfl⟩ : syracuseStep 716887 = 1075331) B1075331
theorem B1077335 : Blo 714321 1077335 := bstep (se 1 (by rfl) ⟨808001, by rfl⟩ : syracuseStep 1077335 = 1616003) B1616003
theorem B4911205 : Blo 714321 4911205 := bstep (se 4 (by rfl) ⟨460425, by rfl⟩ : syracuseStep 4911205 = 920851) B920851
theorem B716907 : Blo 714321 716907 := bstep (se 1 (by rfl) ⟨537680, by rfl⟩ : syracuseStep 716907 = 1075361) B1075361
theorem B716919 : Blo 714321 716919 := bstep (se 1 (by rfl) ⟨537689, by rfl⟩ : syracuseStep 716919 = 1075379) B1075379
theorem B4124803 : Blo 714321 4124803 := bstep (se 1 (by rfl) ⟨3093602, by rfl⟩ : syracuseStep 4124803 = 6187205) B6187205
theorem B1208459 : Blo 714321 1208459 := bstep (se 1 (by rfl) ⟨906344, by rfl⟩ : syracuseStep 1208459 = 1812689) B1812689
theorem B716939 : Blo 714321 716939 := bstep (se 1 (by rfl) ⟨537704, by rfl⟩ : syracuseStep 716939 = 1075409) B1075409
theorem B1241239 : Blo 714321 1241239 := bstep (se 1 (by rfl) ⟨930929, by rfl⟩ : syracuseStep 1241239 = 1861859) B1861859
theorem B716951 : Blo 714321 716951 := bstep (se 1 (by rfl) ⟨537713, by rfl⟩ : syracuseStep 716951 = 1075427) B1075427
theorem B1077401 : Blo 714321 1077401 := bstep (se 2 (by rfl) ⟨404025, by rfl⟩ : syracuseStep 1077401 = 808051) B808051
theorem B716971 : Blo 714321 716971 := bstep (se 1 (by rfl) ⟨537728, by rfl⟩ : syracuseStep 716971 = 1075457) B1075457
theorem B716983 : Blo 714321 716983 := bstep (se 1 (by rfl) ⟨537737, by rfl⟩ : syracuseStep 716983 = 1075475) B1075475
theorem B717003 : Blo 714321 717003 := bstep (se 1 (by rfl) ⟨537752, by rfl⟩ : syracuseStep 717003 = 1075505) B1075505
theorem B717015 : Blo 714321 717015 := bstep (se 1 (by rfl) ⟨537761, by rfl⟩ : syracuseStep 717015 = 1075523) B1075523
theorem B717035 : Blo 714321 717035 := bstep (se 1 (by rfl) ⟨537776, by rfl⟩ : syracuseStep 717035 = 1075553) B1075553
theorem B717047 : Blo 714321 717047 := bstep (se 1 (by rfl) ⟨537785, by rfl⟩ : syracuseStep 717047 = 1075571) B1075571
theorem B1208587 : Blo 714321 1208587 := bstep (se 1 (by rfl) ⟨906440, by rfl⟩ : syracuseStep 1208587 = 1812881) B1812881
theorem B717067 : Blo 714321 717067 := bstep (se 1 (by rfl) ⟨537800, by rfl⟩ : syracuseStep 717067 = 1075601) B1075601
theorem B717079 : Blo 714321 717079 := bstep (se 1 (by rfl) ⟨537809, by rfl⟩ : syracuseStep 717079 = 1075619) B1075619
theorem B717099 : Blo 714321 717099 := bstep (se 1 (by rfl) ⟨537824, by rfl⟩ : syracuseStep 717099 = 1075649) B1075649
theorem B717111 : Blo 714321 717111 := bstep (se 1 (by rfl) ⟨537833, by rfl⟩ : syracuseStep 717111 = 1075667) B1075667
theorem B2289995 : Blo 714321 2289995 := bstep (se 1 (by rfl) ⟨1717496, by rfl⟩ : syracuseStep 2289995 = 3434993) B3434993
theorem B717131 : Blo 714321 717131 := bstep (se 1 (by rfl) ⟨537848, by rfl⟩ : syracuseStep 717131 = 1075697) B1075697
theorem B717143 : Blo 714321 717143 := bstep (se 1 (by rfl) ⟨537857, by rfl⟩ : syracuseStep 717143 = 1075715) B1075715
theorem B717163 : Blo 714321 717163 := bstep (se 1 (by rfl) ⟨537872, by rfl⟩ : syracuseStep 717163 = 1075745) B1075745
theorem B717175 : Blo 714321 717175 := bstep (se 1 (by rfl) ⟨537881, by rfl⟩ : syracuseStep 717175 = 1075763) B1075763
theorem B717195 : Blo 714321 717195 := bstep (se 1 (by rfl) ⟨537896, by rfl⟩ : syracuseStep 717195 = 1075793) B1075793
theorem B717207 : Blo 714321 717207 := bstep (se 1 (by rfl) ⟨537905, by rfl⟩ : syracuseStep 717207 = 1075811) B1075811
theorem B2421143 : Blo 714321 2421143 := bstep (se 1 (by rfl) ⟨1815857, by rfl⟩ : syracuseStep 2421143 = 3631715) B3631715
theorem B1208729 : Blo 714321 1208729 := bstep (se 2 (by rfl) ⟨453273, by rfl⟩ : syracuseStep 1208729 = 906547) B906547
theorem B717227 : Blo 714321 717227 := bstep (se 1 (by rfl) ⟨537920, by rfl⟩ : syracuseStep 717227 = 1075841) B1075841
theorem B717239 : Blo 714321 717239 := bstep (se 1 (by rfl) ⟨537929, by rfl⟩ : syracuseStep 717239 = 1075859) B1075859
theorem B717259 : Blo 714321 717259 := bstep (se 1 (by rfl) ⟨537944, by rfl⟩ : syracuseStep 717259 = 1075889) B1075889
theorem B2290123 : Blo 714321 2290123 := bstep (se 1 (by rfl) ⟨1717592, by rfl⟩ : syracuseStep 2290123 = 3435185) B3435185
theorem B717271 : Blo 714321 717271 := bstep (se 1 (by rfl) ⟨537953, by rfl⟩ : syracuseStep 717271 = 1075907) B1075907
theorem B717291 : Blo 714321 717291 := bstep (se 1 (by rfl) ⟨537968, by rfl⟩ : syracuseStep 717291 = 1075937) B1075937
theorem B717303 : Blo 714321 717303 := bstep (se 1 (by rfl) ⟨537977, by rfl⟩ : syracuseStep 717303 = 1075955) B1075955
theorem B2716163 : Blo 714321 2716163 := bstep (se 1 (by rfl) ⟨2037122, by rfl⟩ : syracuseStep 2716163 = 4074245) B4074245
theorem B5435909 : Blo 714321 5435909 := bstep (se 4 (by rfl) ⟨509616, by rfl⟩ : syracuseStep 5435909 = 1019233) B1019233
theorem B717323 : Blo 714321 717323 := bstep (se 1 (by rfl) ⟨537992, by rfl⟩ : syracuseStep 717323 = 1075985) B1075985
theorem B2290199 : Blo 714321 2290199 := bstep (se 1 (by rfl) ⟨1717649, by rfl⟩ : syracuseStep 2290199 = 3435299) B3435299
theorem B717335 : Blo 714321 717335 := bstep (se 1 (by rfl) ⟨538001, by rfl⟩ : syracuseStep 717335 = 1076003) B1076003
theorem B1208857 : Blo 714321 1208857 := bstep (se 2 (by rfl) ⟨453321, by rfl⟩ : syracuseStep 1208857 = 906643) B906643
theorem B717355 : Blo 714321 717355 := bstep (se 1 (by rfl) ⟨538016, by rfl⟩ : syracuseStep 717355 = 1076033) B1076033
theorem B717367 : Blo 714321 717367 := bstep (se 1 (by rfl) ⟨538025, by rfl⟩ : syracuseStep 717367 = 1076051) B1076051
theorem B717387 : Blo 714321 717387 := bstep (se 1 (by rfl) ⟨538040, by rfl⟩ : syracuseStep 717387 = 1076081) B1076081
theorem B717399 : Blo 714321 717399 := bstep (se 1 (by rfl) ⟨538049, by rfl⟩ : syracuseStep 717399 = 1076099) B1076099
theorem B717419 : Blo 714321 717419 := bstep (se 1 (by rfl) ⟨538064, by rfl⟩ : syracuseStep 717419 = 1076129) B1076129
theorem B717431 : Blo 714321 717431 := bstep (se 1 (by rfl) ⟨538073, by rfl⟩ : syracuseStep 717431 = 1076147) B1076147
theorem B717451 : Blo 714321 717451 := bstep (se 1 (by rfl) ⟨538088, by rfl⟩ : syracuseStep 717451 = 1076177) B1076177
theorem B2585239 : Blo 714321 2585239 := bstep (se 1 (by rfl) ⟨1938929, by rfl⟩ : syracuseStep 2585239 = 3877859) B3877859
theorem B717463 : Blo 714321 717463 := bstep (se 1 (by rfl) ⟨538097, by rfl⟩ : syracuseStep 717463 = 1076195) B1076195
theorem B717483 : Blo 714321 717483 := bstep (se 1 (by rfl) ⟨538112, by rfl⟩ : syracuseStep 717483 = 1076225) B1076225
theorem B717495 : Blo 714321 717495 := bstep (se 1 (by rfl) ⟨538121, by rfl⟩ : syracuseStep 717495 = 1076243) B1076243
theorem B717515 : Blo 714321 717515 := bstep (se 1 (by rfl) ⟨538136, by rfl⟩ : syracuseStep 717515 = 1076273) B1076273
theorem B717527 : Blo 714321 717527 := bstep (se 1 (by rfl) ⟨538145, by rfl⟩ : syracuseStep 717527 = 1076291) B1076291
theorem B717547 : Blo 714321 717547 := bstep (se 1 (by rfl) ⟨538160, by rfl⟩ : syracuseStep 717547 = 1076321) B1076321
theorem B717559 : Blo 714321 717559 := bstep (se 1 (by rfl) ⟨538169, by rfl⟩ : syracuseStep 717559 = 1076339) B1076339
theorem B717579 : Blo 714321 717579 := bstep (se 1 (by rfl) ⟨538184, by rfl⟩ : syracuseStep 717579 = 1076369) B1076369
theorem B717591 : Blo 714321 717591 := bstep (se 1 (by rfl) ⟨538193, by rfl⟩ : syracuseStep 717591 = 1076387) B1076387
theorem B717611 : Blo 714321 717611 := bstep (se 1 (by rfl) ⟨538208, by rfl⟩ : syracuseStep 717611 = 1076417) B1076417
theorem B717623 : Blo 714321 717623 := bstep (se 1 (by rfl) ⟨538217, by rfl⟩ : syracuseStep 717623 = 1076435) B1076435
theorem B717643 : Blo 714321 717643 := bstep (se 1 (by rfl) ⟨538232, by rfl⟩ : syracuseStep 717643 = 1076465) B1076465
theorem B717655 : Blo 714321 717655 := bstep (se 1 (by rfl) ⟨538241, by rfl⟩ : syracuseStep 717655 = 1076483) B1076483
theorem B717675 : Blo 714321 717675 := bstep (se 1 (by rfl) ⟨538256, by rfl⟩ : syracuseStep 717675 = 1076513) B1076513
theorem B717687 : Blo 714321 717687 := bstep (se 1 (by rfl) ⟨538265, by rfl⟩ : syracuseStep 717687 = 1076531) B1076531
theorem B717707 : Blo 714321 717707 := bstep (se 1 (by rfl) ⟨538280, by rfl⟩ : syracuseStep 717707 = 1076561) B1076561
theorem B717719 : Blo 714321 717719 := bstep (se 1 (by rfl) ⟨538289, by rfl⟩ : syracuseStep 717719 = 1076579) B1076579
theorem B717739 : Blo 714321 717739 := bstep (se 1 (by rfl) ⟨538304, by rfl⟩ : syracuseStep 717739 = 1076609) B1076609
theorem B2421683 : Blo 714321 2421683 := bstep (se 1 (by rfl) ⟨1816262, by rfl⟩ : syracuseStep 2421683 = 3632525) B3632525
theorem B717751 : Blo 714321 717751 := bstep (se 1 (by rfl) ⟨538313, by rfl⟩ : syracuseStep 717751 = 1076627) B1076627
theorem B717771 : Blo 714321 717771 := bstep (se 1 (by rfl) ⟨538328, by rfl⟩ : syracuseStep 717771 = 1076657) B1076657
theorem B717783 : Blo 714321 717783 := bstep (se 1 (by rfl) ⟨538337, by rfl⟩ : syracuseStep 717783 = 1076675) B1076675
theorem B717803 : Blo 714321 717803 := bstep (se 1 (by rfl) ⟨538352, by rfl⟩ : syracuseStep 717803 = 1076705) B1076705
theorem B717815 : Blo 714321 717815 := bstep (se 1 (by rfl) ⟨538361, by rfl⟩ : syracuseStep 717815 = 1076723) B1076723
theorem B717835 : Blo 714321 717835 := bstep (se 1 (by rfl) ⟨538376, by rfl⟩ : syracuseStep 717835 = 1076753) B1076753
theorem B717847 : Blo 714321 717847 := bstep (se 1 (by rfl) ⟨538385, by rfl⟩ : syracuseStep 717847 = 1076771) B1076771
theorem B717867 : Blo 714321 717867 := bstep (se 1 (by rfl) ⟨538400, by rfl⟩ : syracuseStep 717867 = 1076801) B1076801
theorem B2585645 : Blo 714321 2585645 := bstep (se 3 (by rfl) ⟨484808, by rfl⟩ : syracuseStep 2585645 = 969617) B969617
theorem B717879 : Blo 714321 717879 := bstep (se 1 (by rfl) ⟨538409, by rfl⟩ : syracuseStep 717879 = 1076819) B1076819
theorem B717899 : Blo 714321 717899 := bstep (se 1 (by rfl) ⟨538424, by rfl⟩ : syracuseStep 717899 = 1076849) B1076849
theorem B1209431 : Blo 714321 1209431 := bstep (se 1 (by rfl) ⟨907073, by rfl⟩ : syracuseStep 1209431 = 1814147) B1814147
theorem B717911 : Blo 714321 717911 := bstep (se 1 (by rfl) ⟨538433, by rfl⟩ : syracuseStep 717911 = 1076867) B1076867
theorem B717931 : Blo 714321 717931 := bstep (se 1 (by rfl) ⟨538448, by rfl⟩ : syracuseStep 717931 = 1076897) B1076897
theorem B717943 : Blo 714321 717943 := bstep (se 1 (by rfl) ⟨538457, by rfl⟩ : syracuseStep 717943 = 1076915) B1076915
theorem B3634307 : Blo 714321 3634307 := bstep (se 1 (by rfl) ⟨2725730, by rfl⟩ : syracuseStep 3634307 = 5451461) B5451461
theorem B717963 : Blo 714321 717963 := bstep (se 1 (by rfl) ⟨538472, by rfl⟩ : syracuseStep 717963 = 1076945) B1076945
theorem B717975 : Blo 714321 717975 := bstep (se 1 (by rfl) ⟨538481, by rfl⟩ : syracuseStep 717975 = 1076963) B1076963
theorem B717995 : Blo 714321 717995 := bstep (se 1 (by rfl) ⟨538496, by rfl⟩ : syracuseStep 717995 = 1076993) B1076993
theorem B718007 : Blo 714321 718007 := bstep (se 1 (by rfl) ⟨538505, by rfl⟩ : syracuseStep 718007 = 1077011) B1077011
theorem B2421953 : Blo 714321 2421953 := bstep (se 2 (by rfl) ⟨908232, by rfl⟩ : syracuseStep 2421953 = 1816465) B1816465
theorem B718027 : Blo 714321 718027 := bstep (se 1 (by rfl) ⟨538520, by rfl⟩ : syracuseStep 718027 = 1077041) B1077041
theorem B1209559 : Blo 714321 1209559 := bstep (se 1 (by rfl) ⟨907169, by rfl⟩ : syracuseStep 1209559 = 1814339) B1814339
theorem B718039 : Blo 714321 718039 := bstep (se 1 (by rfl) ⟨538529, by rfl⟩ : syracuseStep 718039 = 1077059) B1077059
theorem B718059 : Blo 714321 718059 := bstep (se 1 (by rfl) ⟨538544, by rfl⟩ : syracuseStep 718059 = 1077089) B1077089
theorem B718071 : Blo 714321 718071 := bstep (se 1 (by rfl) ⟨538553, by rfl⟩ : syracuseStep 718071 = 1077107) B1077107
theorem B718091 : Blo 714321 718091 := bstep (se 1 (by rfl) ⟨538568, by rfl⟩ : syracuseStep 718091 = 1077137) B1077137
theorem B718103 : Blo 714321 718103 := bstep (se 1 (by rfl) ⟨538577, by rfl⟩ : syracuseStep 718103 = 1077155) B1077155
theorem B816427 : Blo 714321 816427 := bstep (se 1 (by rfl) ⟨612320, by rfl⟩ : syracuseStep 816427 = 1224641) B1224641
theorem B718123 : Blo 714321 718123 := bstep (se 1 (by rfl) ⟨538592, by rfl⟩ : syracuseStep 718123 = 1077185) B1077185
theorem B718135 : Blo 714321 718135 := bstep (se 1 (by rfl) ⟨538601, by rfl⟩ : syracuseStep 718135 = 1077203) B1077203
theorem B718155 : Blo 714321 718155 := bstep (se 1 (by rfl) ⟨538616, by rfl⟩ : syracuseStep 718155 = 1077233) B1077233
theorem B718167 : Blo 714321 718167 := bstep (se 1 (by rfl) ⟨538625, by rfl⟩ : syracuseStep 718167 = 1077251) B1077251
theorem B718187 : Blo 714321 718187 := bstep (se 1 (by rfl) ⟨538640, by rfl⟩ : syracuseStep 718187 = 1077281) B1077281
theorem B718199 : Blo 714321 718199 := bstep (se 1 (by rfl) ⟨538649, by rfl⟩ : syracuseStep 718199 = 1077299) B1077299
theorem B718219 : Blo 714321 718219 := bstep (se 1 (by rfl) ⟨538664, by rfl⟩ : syracuseStep 718219 = 1077329) B1077329
theorem B718231 : Blo 714321 718231 := bstep (se 1 (by rfl) ⟨538673, by rfl⟩ : syracuseStep 718231 = 1077347) B1077347
theorem B718251 : Blo 714321 718251 := bstep (se 1 (by rfl) ⟨538688, by rfl⟩ : syracuseStep 718251 = 1077377) B1077377
theorem B718263 : Blo 714321 718263 := bstep (se 1 (by rfl) ⟨538697, by rfl⟩ : syracuseStep 718263 = 1077395) B1077395
theorem B718283 : Blo 714321 718283 := bstep (se 1 (by rfl) ⟨538712, by rfl⟩ : syracuseStep 718283 = 1077425) B1077425
theorem B718295 : Blo 714321 718295 := bstep (se 1 (by rfl) ⟨538721, by rfl⟩ : syracuseStep 718295 = 1077443) B1077443
theorem B2586077 : Blo 714321 2586077 := bstep (se 3 (by rfl) ⟨484889, by rfl⟩ : syracuseStep 2586077 = 969779) B969779
theorem B718315 : Blo 714321 718315 := bstep (se 1 (by rfl) ⟨538736, by rfl⟩ : syracuseStep 718315 = 1077473) B1077473
theorem B1570291 : Blo 714321 1570291 := bstep (se 1 (by rfl) ⟨1177718, by rfl⟩ : syracuseStep 1570291 = 2355437) B2355437
theorem B1570379 : Blo 714321 1570379 := bstep (se 1 (by rfl) ⟨1177784, by rfl⟩ : syracuseStep 1570379 = 2355569) B2355569
theorem B1144459 : Blo 714321 1144459 := bstep (se 1 (by rfl) ⟨858344, by rfl⟩ : syracuseStep 1144459 = 1716689) B1716689
theorem B2422493 : Blo 714321 2422493 := bstep (se 3 (by rfl) ⟨454217, by rfl⟩ : syracuseStep 2422493 = 908435) B908435
theorem B1144601 : Blo 714321 1144601 := bstep (se 2 (by rfl) ⟨429225, by rfl⟩ : syracuseStep 1144601 = 858451) B858451
theorem B1210187 : Blo 714321 1210187 := bstep (se 1 (by rfl) ⟨907640, by rfl⟩ : syracuseStep 1210187 = 1815281) B1815281
theorem B2619229 : Blo 714321 2619229 := bstep (se 3 (by rfl) ⟨491105, by rfl⟩ : syracuseStep 2619229 = 982211) B982211
theorem B1210315 : Blo 714321 1210315 := bstep (se 1 (by rfl) ⟨907736, by rfl⟩ : syracuseStep 1210315 = 1815473) B1815473
theorem B1210457 : Blo 714321 1210457 := bstep (se 2 (by rfl) ⟨453921, by rfl⟩ : syracuseStep 1210457 = 907843) B907843
theorem B1210585 : Blo 714321 1210585 := bstep (se 2 (by rfl) ⟨453969, by rfl⟩ : syracuseStep 1210585 = 907939) B907939
theorem B1309043 : Blo 714321 1309043 := bstep (se 1 (by rfl) ⟨981782, by rfl⟩ : syracuseStep 1309043 = 1963565) B1963565
theorem B6126029 : Blo 714321 6126029 := bstep (se 3 (by rfl) ⟨1148630, by rfl⟩ : syracuseStep 6126029 = 2297261) B2297261
theorem B2587187 : Blo 714321 2587187 := bstep (se 1 (by rfl) ⟨1940390, by rfl⟩ : syracuseStep 2587187 = 3880781) B3880781
theorem B1145561 : Blo 714321 1145561 := bstep (se 2 (by rfl) ⟨429585, by rfl⟩ : syracuseStep 1145561 = 859171) B859171
theorem B1211159 : Blo 714321 1211159 := bstep (se 1 (by rfl) ⟨908369, by rfl⟩ : syracuseStep 1211159 = 1816739) B1816739
theorem B6552355 : Blo 714321 6552355 := bstep (se 1 (by rfl) ⟨4914266, by rfl⟩ : syracuseStep 6552355 = 9828533) B9828533
theorem B2423627 : Blo 714321 2423627 := bstep (se 1 (by rfl) ⟨1817720, by rfl⟩ : syracuseStep 2423627 = 3635441) B3635441
theorem B5438339 : Blo 714321 5438339 := bstep (se 1 (by rfl) ⟨4078754, by rfl⟩ : syracuseStep 5438339 = 8157509) B8157509
theorem B1211287 : Blo 714321 1211287 := bstep (se 1 (by rfl) ⟨908465, by rfl⟩ : syracuseStep 1211287 = 1816931) B1816931
theorem B1309783 : Blo 714321 1309783 := bstep (se 1 (by rfl) ⟨982337, by rfl⟩ : syracuseStep 1309783 = 1964675) B1964675
theorem B2423897 : Blo 714321 2423897 := bstep (se 2 (by rfl) ⟨908961, by rfl⟩ : syracuseStep 2423897 = 1817923) B1817923
theorem B3865751 : Blo 714321 3865751 := bstep (se 1 (by rfl) ⟨2899313, by rfl⟩ : syracuseStep 3865751 = 5798627) B5798627
theorem B3276035 : Blo 714321 3276035 := bstep (se 1 (by rfl) ⟨2457026, by rfl⟩ : syracuseStep 3276035 = 4914053) B4914053
theorem B1211915 : Blo 714321 1211915 := bstep (se 1 (by rfl) ⟨908936, by rfl⟩ : syracuseStep 1211915 = 1817873) B1817873
theorem B2588183 : Blo 714321 2588183 := bstep (se 1 (by rfl) ⟨1941137, by rfl⟩ : syracuseStep 2588183 = 3882275) B3882275
theorem B2719277 : Blo 714321 2719277 := bstep (se 3 (by rfl) ⟨509864, by rfl⟩ : syracuseStep 2719277 = 1019729) B1019729
theorem B1212043 : Blo 714321 1212043 := bstep (se 1 (by rfl) ⟨909032, by rfl⟩ : syracuseStep 1212043 = 1818065) B1818065
theorem B1835095 : Blo 714321 1835095 := bstep (se 1 (by rfl) ⟨1376321, by rfl⟩ : syracuseStep 1835095 = 2752643) B2752643
theorem B2293879 : Blo 714321 2293879 := bstep (se 1 (by rfl) ⟨1720409, by rfl⟩ : syracuseStep 2293879 = 3440819) B3440819
theorem B23298293 : Blo 714321 23298293 := bstep (se 5 (by rfl) ⟨1092107, by rfl⟩ : syracuseStep 23298293 = 2184215) B2184215
theorem B4587961 : Blo 714321 4587961 := bstep (se 2 (by rfl) ⟨1720485, by rfl⟩ : syracuseStep 4587961 = 3440971) B3440971
theorem B4358609 : Blo 714321 4358609 := bstep (se 2 (by rfl) ⟨1634478, by rfl⟩ : syracuseStep 4358609 = 3268957) B3268957
theorem B13763033 : Blo 714321 13763033 := bstep (se 2 (by rfl) ⟨5161137, by rfl⟩ : syracuseStep 13763033 = 10322275) B10322275
theorem B983723 : Blo 714321 983723 := bstep (se 1 (by rfl) ⟨737792, by rfl⟩ : syracuseStep 983723 = 1475585) B1475585
theorem B2294813 : Blo 714321 2294813 := bstep (se 3 (by rfl) ⟨430277, by rfl⟩ : syracuseStep 2294813 = 860555) B860555
theorem B2295325 : Blo 714321 2295325 := bstep (se 3 (by rfl) ⟨430373, by rfl⟩ : syracuseStep 2295325 = 860747) B860747
theorem B5506627 : Blo 714321 5506627 := bstep (se 1 (by rfl) ⟨4129970, by rfl⟩ : syracuseStep 5506627 = 8259941) B8259941
theorem B1017479 : Blo 714321 1017479 := bstep (se 1 (by rfl) ⟨763109, by rfl⟩ : syracuseStep 1017479 = 1526219) B1526219
theorem B1607543 : Blo 714321 1607543 := bstep (se 1 (by rfl) ⟨1205657, by rfl⟩ : syracuseStep 1607543 = 2411315) B2411315
theorem B2721721 : Blo 714321 2721721 := bstep (se 2 (by rfl) ⟨1020645, by rfl⟩ : syracuseStep 2721721 = 2041291) B2041291
theorem B1017787 : Blo 714321 1017787 := bstep (se 1 (by rfl) ⟨763340, by rfl⟩ : syracuseStep 1017787 = 1526681) B1526681
theorem B1607723 : Blo 714321 1607723 := bstep (se 1 (by rfl) ⟨1205792, by rfl⟩ : syracuseStep 1607723 = 2411585) B2411585
theorem B1149047 : Blo 714321 1149047 := bstep (se 1 (by rfl) ⟨861785, by rfl⟩ : syracuseStep 1149047 = 1723571) B1723571
theorem B1837313 : Blo 714321 1837313 := bstep (se 2 (by rfl) ⟨688992, by rfl⟩ : syracuseStep 1837313 = 1377985) B1377985
theorem B1608083 : Blo 714321 1608083 := bstep (se 1 (by rfl) ⟨1206062, by rfl⟩ : syracuseStep 1608083 = 2412125) B2412125
theorem B1608137 : Blo 714321 1608137 := bstep (se 2 (by rfl) ⟨603051, by rfl⟩ : syracuseStep 1608137 = 1206103) B1206103
theorem B9178019 : Blo 714321 9178019 := bstep (se 1 (by rfl) ⟨6883514, by rfl⟩ : syracuseStep 9178019 = 13767029) B13767029
theorem B8293387 : Blo 714321 8293387 := bstep (se 1 (by rfl) ⟨6220040, by rfl⟩ : syracuseStep 8293387 = 12440081) B12440081
theorem B3443741 : Blo 714321 3443741 := bstep (se 3 (by rfl) ⟨645701, by rfl⟩ : syracuseStep 3443741 = 1291403) B1291403
theorem B1149995 : Blo 714321 1149995 := bstep (se 1 (by rfl) ⟨862496, by rfl⟩ : syracuseStep 1149995 = 1724993) B1724993
theorem B1018937 : Blo 714321 1018937 := bstep (se 2 (by rfl) ⟨382101, by rfl⟩ : syracuseStep 1018937 = 764203) B764203
theorem B1608839 : Blo 714321 1608839 := bstep (se 1 (by rfl) ⟨1206629, by rfl⟩ : syracuseStep 1608839 = 2413259) B2413259
theorem B1936585 : Blo 714321 1936585 := bstep (se 2 (by rfl) ⟨726219, by rfl⟩ : syracuseStep 1936585 = 1452439) B1452439
theorem B2067713 : Blo 714321 2067713 := bstep (se 2 (by rfl) ⟨775392, by rfl⟩ : syracuseStep 2067713 = 1550785) B1550785
theorem B1609019 : Blo 714321 1609019 := bstep (se 1 (by rfl) ⟨1206764, by rfl⟩ : syracuseStep 1609019 = 2413529) B2413529
theorem B1609145 : Blo 714321 1609145 := bstep (se 2 (by rfl) ⟨603429, by rfl⟩ : syracuseStep 1609145 = 1206859) B1206859
theorem B7179853 : Blo 714321 7179853 := bstep (se 3 (by rfl) ⟨1346222, by rfl⟩ : syracuseStep 7179853 = 2692445) B2692445
theorem B1609487 : Blo 714321 1609487 := bstep (se 1 (by rfl) ⟨1207115, by rfl⟩ : syracuseStep 1609487 = 2414231) B2414231
theorem B1609505 : Blo 714321 1609505 := bstep (se 2 (by rfl) ⟨603564, by rfl⟩ : syracuseStep 1609505 = 1207129) B1207129
theorem B2068267 : Blo 714321 2068267 := bstep (se 1 (by rfl) ⟨1551200, by rfl⟩ : syracuseStep 2068267 = 3102401) B3102401
theorem B1937287 : Blo 714321 1937287 := bstep (se 1 (by rfl) ⟨1452965, by rfl⟩ : syracuseStep 1937287 = 2905931) B2905931
theorem B1609847 : Blo 714321 1609847 := bstep (se 1 (by rfl) ⟨1207385, by rfl⟩ : syracuseStep 1609847 = 2414771) B2414771
theorem B2035847 : Blo 714321 2035847 := bstep (se 1 (by rfl) ⟨1526885, by rfl⟩ : syracuseStep 2035847 = 3053771) B3053771
theorem B4657441 : Blo 714321 4657441 := bstep (se 2 (by rfl) ⟨1746540, by rfl⟩ : syracuseStep 4657441 = 3493081) B3493081
theorem B2298145 : Blo 714321 2298145 := bstep (se 2 (by rfl) ⟨861804, by rfl⟩ : syracuseStep 2298145 = 1723609) B1723609
theorem B1610027 : Blo 714321 1610027 := bstep (se 1 (by rfl) ⟨1207520, by rfl⟩ : syracuseStep 1610027 = 2415041) B2415041
theorem B2036029 : Blo 714321 2036029 := bstep (se 3 (by rfl) ⟨381755, by rfl⟩ : syracuseStep 2036029 = 763511) B763511
theorem B2036087 : Blo 714321 2036087 := bstep (se 1 (by rfl) ⟨1527065, by rfl⟩ : syracuseStep 2036087 = 3054131) B3054131
theorem B1937849 : Blo 714321 1937849 := bstep (se 2 (by rfl) ⟨726693, by rfl⟩ : syracuseStep 1937849 = 1453387) B1453387
theorem B1020475 : Blo 714321 1020475 := bstep (se 1 (by rfl) ⟨765356, by rfl⟩ : syracuseStep 1020475 = 1530713) B1530713
theorem B1610387 : Blo 714321 1610387 := bstep (se 1 (by rfl) ⟨1207790, by rfl⟩ : syracuseStep 1610387 = 2415581) B2415581
theorem B1610441 : Blo 714321 1610441 := bstep (se 2 (by rfl) ⟨603915, by rfl⟩ : syracuseStep 1610441 = 1207831) B1207831
theorem B2724623 : Blo 714321 2724623 := bstep (se 1 (by rfl) ⟨2043467, by rfl⟩ : syracuseStep 2724623 = 4086935) B4086935
theorem B5149489 : Blo 714321 5149489 := bstep (se 2 (by rfl) ⟨1931058, by rfl⟩ : syracuseStep 5149489 = 3862117) B3862117
theorem B1020919 : Blo 714321 1020919 := bstep (se 1 (by rfl) ⟨765689, by rfl⟩ : syracuseStep 1020919 = 1531379) B1531379
theorem B4068413 : Blo 714321 4068413 := bstep (se 3 (by rfl) ⟨762827, by rfl⟩ : syracuseStep 4068413 = 1525655) B1525655
theorem B5805371 : Blo 714321 5805371 := bstep (se 1 (by rfl) ⟨4354028, by rfl⟩ : syracuseStep 5805371 = 8708057) B8708057
theorem B1611143 : Blo 714321 1611143 := bstep (se 1 (by rfl) ⟨1208357, by rfl⟩ : syracuseStep 1611143 = 2416715) B2416715
theorem B2037145 : Blo 714321 2037145 := bstep (se 2 (by rfl) ⟨763929, by rfl⟩ : syracuseStep 2037145 = 1527859) B1527859
theorem B1611323 : Blo 714321 1611323 := bstep (se 1 (by rfl) ⟨1208492, by rfl⟩ : syracuseStep 1611323 = 2416985) B2416985
theorem B3872323 : Blo 714321 3872323 := bstep (se 1 (by rfl) ⟨2904242, by rfl⟩ : syracuseStep 3872323 = 5808485) B5808485
theorem B1611449 : Blo 714321 1611449 := bstep (se 2 (by rfl) ⟨604293, by rfl⟩ : syracuseStep 1611449 = 1208587) B1208587
theorem B6133441 : Blo 714321 6133441 := bstep (se 2 (by rfl) ⟨2300040, by rfl⟩ : syracuseStep 6133441 = 4600081) B4600081
theorem B1021739 : Blo 714321 1021739 := bstep (se 1 (by rfl) ⟨766304, by rfl⟩ : syracuseStep 1021739 = 1532609) B1532609
theorem B3053447 : Blo 714321 3053447 := bstep (se 1 (by rfl) ⟨2290085, by rfl⟩ : syracuseStep 3053447 = 4580171) B4580171
theorem B3053497 : Blo 714321 3053497 := bstep (se 2 (by rfl) ⟨1145061, by rfl⟩ : syracuseStep 3053497 = 2290123) B2290123
theorem B2037761 : Blo 714321 2037761 := bstep (se 2 (by rfl) ⟨764160, by rfl⟩ : syracuseStep 2037761 = 1528321) B1528321
theorem B1611791 : Blo 714321 1611791 := bstep (se 1 (by rfl) ⟨1208843, by rfl⟩ : syracuseStep 1611791 = 2417687) B2417687
theorem B1611809 : Blo 714321 1611809 := bstep (se 2 (by rfl) ⟨604428, by rfl⟩ : syracuseStep 1611809 = 1208857) B1208857
theorem B16750709 : Blo 714321 16750709 := bstep (se 5 (by rfl) ⟨785189, by rfl⟩ : syracuseStep 16750709 = 1570379) B1570379
theorem B17406197 : Blo 714321 17406197 := bstep (se 5 (by rfl) ⟨815915, by rfl⟩ : syracuseStep 17406197 = 1631831) B1631831
theorem B235411757 : Blo 714321 235411757 := bstep (se 3 (by rfl) ⟨44139704, by rfl⟩ : syracuseStep 235411757 = 88279409) B88279409
theorem B1612151 : Blo 714321 1612151 := bstep (se 1 (by rfl) ⟨1209113, by rfl⟩ : syracuseStep 1612151 = 2418227) B2418227
theorem B8264195 : Blo 714321 8264195 := bstep (se 1 (by rfl) ⟨6198146, by rfl⟩ : syracuseStep 8264195 = 12396293) B12396293
theorem B1612331 : Blo 714321 1612331 := bstep (se 1 (by rfl) ⟨1209248, by rfl⟩ : syracuseStep 1612331 = 2418497) B2418497
theorem B1809287 : Blo 714321 1809287 := bstep (se 1 (by rfl) ⟨1356965, by rfl⟩ : syracuseStep 1809287 = 2713931) B2713931
theorem B727951 : Blo 714321 727951 := bstep (se 1 (by rfl) ⟨545963, by rfl⟩ : syracuseStep 727951 = 1091927) B1091927
theorem B1612691 : Blo 714321 1612691 := bstep (se 1 (by rfl) ⟨1209518, by rfl⟩ : syracuseStep 1612691 = 2419037) B2419037
theorem B1809337 : Blo 714321 1809337 := bstep (se 2 (by rfl) ⟨678501, by rfl⟩ : syracuseStep 1809337 = 1357003) B1357003
theorem B2038729 : Blo 714321 2038729 := bstep (se 2 (by rfl) ⟨764523, by rfl⟩ : syracuseStep 2038729 = 1529047) B1529047
theorem B1612745 : Blo 714321 1612745 := bstep (se 2 (by rfl) ⟨604779, by rfl⟩ : syracuseStep 1612745 = 1209559) B1209559
theorem B3447755 : Blo 714321 3447755 := bstep (se 1 (by rfl) ⟨2585816, by rfl⟩ : syracuseStep 3447755 = 5171633) B5171633
theorem B1088569 : Blo 714321 1088569 := bstep (se 2 (by rfl) ⟨408213, by rfl⟩ : syracuseStep 1088569 = 816427) B816427
theorem B3054829 : Blo 714321 3054829 := bstep (se 3 (by rfl) ⟨572780, by rfl⟩ : syracuseStep 3054829 = 1145561) B1145561
theorem B1809935 : Blo 714321 1809935 := bstep (se 1 (by rfl) ⟨1357451, by rfl⟩ : syracuseStep 1809935 = 2714903) B2714903
theorem B3055171 : Blo 714321 3055171 := bstep (se 1 (by rfl) ⟨2291378, by rfl⟩ : syracuseStep 3055171 = 4582757) B4582757
theorem B1613447 : Blo 714321 1613447 := bstep (se 1 (by rfl) ⟨1210085, by rfl⟩ : syracuseStep 1613447 = 2420171) B2420171
theorem B1613627 : Blo 714321 1613627 := bstep (se 1 (by rfl) ⟨1210220, by rfl⟩ : syracuseStep 1613627 = 2420441) B2420441
theorem B1613753 : Blo 714321 1613753 := bstep (se 2 (by rfl) ⟨605157, by rfl⟩ : syracuseStep 1613753 = 1210315) B1210315
theorem B6529085 : Blo 714321 6529085 := bstep (se 3 (by rfl) ⟨1224203, by rfl⟩ : syracuseStep 6529085 = 2448407) B2448407
theorem B1810633 : Blo 714321 1810633 := bstep (se 2 (by rfl) ⟨678987, by rfl⟩ : syracuseStep 1810633 = 1357975) B1357975
theorem B1614095 : Blo 714321 1614095 := bstep (se 1 (by rfl) ⟨1210571, by rfl⟩ : syracuseStep 1614095 = 2421143) B2421143
theorem B1614113 : Blo 714321 1614113 := bstep (se 2 (by rfl) ⟨605292, by rfl⟩ : syracuseStep 1614113 = 1210585) B1210585
theorem B1810775 : Blo 714321 1810775 := bstep (se 1 (by rfl) ⟨1358081, by rfl⟩ : syracuseStep 1810775 = 2716163) B2716163
theorem B2040335 : Blo 714321 2040335 := bstep (se 1 (by rfl) ⟨1530251, by rfl⟩ : syracuseStep 2040335 = 3060503) B3060503
theorem B1614455 : Blo 714321 1614455 := bstep (se 1 (by rfl) ⟨1210841, by rfl⟩ : syracuseStep 1614455 = 2421683) B2421683
theorem B1450631 : Blo 714321 1450631 := bstep (se 1 (by rfl) ⟨1087973, by rfl⟩ : syracuseStep 1450631 = 2175947) B2175947
theorem B6103781 : Blo 714321 6103781 := bstep (se 4 (by rfl) ⟨572229, by rfl⟩ : syracuseStep 6103781 = 1144459) B1144459
theorem B1614635 : Blo 714321 1614635 := bstep (se 1 (by rfl) ⟨1210976, by rfl⟩ : syracuseStep 1614635 = 2421953) B2421953
theorem B1614995 : Blo 714321 1614995 := bstep (se 1 (by rfl) ⟨1211246, by rfl⟩ : syracuseStep 1614995 = 2422493) B2422493
theorem B6890669 : Blo 714321 6890669 := bstep (se 3 (by rfl) ⟨1292000, by rfl⟩ : syracuseStep 6890669 = 2584001) B2584001
theorem B763067 : Blo 714321 763067 := bstep (se 1 (by rfl) ⟨572300, by rfl⟩ : syracuseStep 763067 = 1144601) B1144601
theorem B1615049 : Blo 714321 1615049 := bstep (se 2 (by rfl) ⟨605643, by rfl⟩ : syracuseStep 1615049 = 1211287) B1211287
theorem B1746377 : Blo 714321 1746377 := bstep (se 2 (by rfl) ⟨654891, by rfl⟩ : syracuseStep 1746377 = 1309783) B1309783
theorem B13936157 : Blo 714321 13936157 := bstep (se 3 (by rfl) ⟨2613029, by rfl⟩ : syracuseStep 13936157 = 5226059) B5226059
theorem B1287713 : Blo 714321 1287713 := bstep (se 2 (by rfl) ⟨482892, by rfl⟩ : syracuseStep 1287713 = 965785) B965785
theorem B2041463 : Blo 714321 2041463 := bstep (se 1 (by rfl) ⟨1531097, by rfl⟩ : syracuseStep 2041463 = 3062195) B3062195
theorem B4597519 : Blo 714321 4597519 := bstep (se 1 (by rfl) ⟨3448139, by rfl⟩ : syracuseStep 4597519 = 6896279) B6896279
theorem B1615751 : Blo 714321 1615751 := bstep (se 1 (by rfl) ⟨1211813, by rfl⟩ : syracuseStep 1615751 = 2423627) B2423627
theorem B993211 : Blo 714321 993211 := bstep (se 1 (by rfl) ⟨744908, by rfl⟩ : syracuseStep 993211 = 1489817) B1489817
theorem B1615931 : Blo 714321 1615931 := bstep (se 1 (by rfl) ⟨1211948, by rfl⟩ : syracuseStep 1615931 = 2423897) B2423897
theorem B1616057 : Blo 714321 1616057 := bstep (se 2 (by rfl) ⟨606021, by rfl⟩ : syracuseStep 1616057 = 1212043) B1212043
theorem B1812851 : Blo 714321 1812851 := bstep (se 1 (by rfl) ⟨1359638, by rfl⟩ : syracuseStep 1812851 = 2719277) B2719277
theorem B33499541 : Blo 714321 33499541 := bstep (se 6 (by rfl) ⟨785145, by rfl⟩ : syracuseStep 33499541 = 1570291) B1570291
theorem B4139581 : Blo 714321 4139581 := bstep (se 3 (by rfl) ⟨776171, by rfl⟩ : syracuseStep 4139581 = 1552343) B1552343
theorem B1813367 : Blo 714321 1813367 := bstep (se 1 (by rfl) ⟨1360025, by rfl⟩ : syracuseStep 1813367 = 2720051) B2720051
theorem B3779531 : Blo 714321 3779531 := bstep (se 1 (by rfl) ⟨2834648, by rfl⟩ : syracuseStep 3779531 = 5669297) B5669297
theorem B4074563 : Blo 714321 4074563 := bstep (se 1 (by rfl) ⟨3055922, by rfl⟩ : syracuseStep 4074563 = 6111845) B6111845
theorem B2043137 : Blo 714321 2043137 := bstep (se 2 (by rfl) ⟨766176, by rfl⟩ : syracuseStep 2043137 = 1532353) B1532353
theorem B2043251 : Blo 714321 2043251 := bstep (se 1 (by rfl) ⟨1532438, by rfl⟩ : syracuseStep 2043251 = 3064877) B3064877
theorem B4075019 : Blo 714321 4075019 := bstep (se 1 (by rfl) ⟨3056264, by rfl⟩ : syracuseStep 4075019 = 6112529) B6112529
theorem B30912151 : Blo 714321 30912151 := bstep (se 1 (by rfl) ⟨23184113, by rfl⟩ : syracuseStep 30912151 = 46368227) B46368227
theorem B2043593 : Blo 714321 2043593 := bstep (se 2 (by rfl) ⟨766347, by rfl⟩ : syracuseStep 2043593 = 1532695) B1532695
theorem B1814359 : Blo 714321 1814359 := bstep (se 1 (by rfl) ⟨1360769, by rfl⟩ : syracuseStep 1814359 = 2721539) B2721539
theorem B3616811 : Blo 714321 3616811 := bstep (se 1 (by rfl) ⟨2712608, by rfl⟩ : syracuseStep 3616811 = 5425217) B5425217
theorem B6107197 : Blo 714321 6107197 := bstep (se 3 (by rfl) ⟨1145099, by rfl⟩ : syracuseStep 6107197 = 2290199) B2290199
theorem B1814663 : Blo 714321 1814663 := bstep (se 1 (by rfl) ⟨1360997, by rfl⟩ : syracuseStep 1814663 = 2721995) B2721995
theorem B5157101 : Blo 714321 5157101 := bstep (se 3 (by rfl) ⟨966956, by rfl⟩ : syracuseStep 5157101 = 1933913) B1933913
theorem B1814795 : Blo 714321 1814795 := bstep (se 1 (by rfl) ⟨1361096, by rfl⟩ : syracuseStep 1814795 = 2722193) B2722193
theorem B1815311 : Blo 714321 1815311 := bstep (se 1 (by rfl) ⟨1361483, by rfl⟩ : syracuseStep 1815311 = 2722967) B2722967
theorem B1815443 : Blo 714321 1815443 := bstep (se 1 (by rfl) ⟨1361582, by rfl⟩ : syracuseStep 1815443 = 2723165) B2723165
theorem B1356745 : Blo 714321 1356745 := bstep (se 2 (by rfl) ⟨508779, by rfl⟩ : syracuseStep 1356745 = 1017559) B1017559
theorem B8696965 : Blo 714321 8696965 := bstep (se 4 (by rfl) ⟨815340, by rfl⟩ : syracuseStep 8696965 = 1630681) B1630681
theorem B8140013 : Blo 714321 8140013 := bstep (se 3 (by rfl) ⟨1526252, by rfl⟩ : syracuseStep 8140013 = 3052505) B3052505
theorem B3618107 : Blo 714321 3618107 := bstep (se 1 (by rfl) ⟨2713580, by rfl⟩ : syracuseStep 3618107 = 5427161) B5427161
theorem B3683731 : Blo 714321 3683731 := bstep (se 1 (by rfl) ⟨2762798, by rfl⟩ : syracuseStep 3683731 = 5525597) B5525597
theorem B3618269 : Blo 714321 3618269 := bstep (se 3 (by rfl) ⟨678425, by rfl⟩ : syracuseStep 3618269 = 1356851) B1356851
theorem B2045483 : Blo 714321 2045483 := bstep (se 1 (by rfl) ⟨1534112, by rfl⟩ : syracuseStep 2045483 = 3068225) B3068225
theorem B3618593 : Blo 714321 3618593 := bstep (se 2 (by rfl) ⟨1356972, by rfl⟩ : syracuseStep 3618593 = 2713945) B2713945
theorem B6895475 : Blo 714321 6895475 := bstep (se 1 (by rfl) ⟨5171606, by rfl⟩ : syracuseStep 6895475 = 10343213) B10343213
theorem B1816577 : Blo 714321 1816577 := bstep (se 2 (by rfl) ⟨681216, by rfl⟩ : syracuseStep 1816577 = 1362433) B1362433
theorem B6895817 : Blo 714321 6895817 := bstep (se 2 (by rfl) ⟨2585931, by rfl⟩ : syracuseStep 6895817 = 5171863) B5171863
theorem B1816951 : Blo 714321 1816951 := bstep (se 1 (by rfl) ⟨1362713, by rfl⟩ : syracuseStep 1816951 = 2725427) B2725427
theorem B3979655 : Blo 714321 3979655 := bstep (se 1 (by rfl) ⟨2984741, by rfl⟩ : syracuseStep 3979655 = 5969483) B5969483
theorem B3684761 : Blo 714321 3684761 := bstep (se 2 (by rfl) ⟨1381785, by rfl⟩ : syracuseStep 3684761 = 2763571) B2763571
theorem B1718795 : Blo 714321 1718795 := bstep (se 1 (by rfl) ⟨1289096, by rfl⟩ : syracuseStep 1718795 = 2578193) B2578193
theorem B3619565 : Blo 714321 3619565 := bstep (se 3 (by rfl) ⟨678668, by rfl⟩ : syracuseStep 3619565 = 1357337) B1357337
theorem B1719073 : Blo 714321 1719073 := bstep (se 2 (by rfl) ⟨644652, by rfl⟩ : syracuseStep 1719073 = 1289305) B1289305
theorem B1817387 : Blo 714321 1817387 := bstep (se 1 (by rfl) ⟨1363040, by rfl⟩ : syracuseStep 1817387 = 2726081) B2726081
theorem B3881843 : Blo 714321 3881843 := bstep (se 1 (by rfl) ⟨2911382, by rfl⟩ : syracuseStep 3881843 = 5822765) B5822765
theorem B1719187 : Blo 714321 1719187 := bstep (se 1 (by rfl) ⟨1289390, by rfl⟩ : syracuseStep 1719187 = 2578781) B2578781
theorem B4078937 : Blo 714321 4078937 := bstep (se 2 (by rfl) ⟨1529601, by rfl⟩ : syracuseStep 4078937 = 3059203) B3059203
theorem B1359251 : Blo 714321 1359251 := bstep (se 1 (by rfl) ⟨1019438, by rfl⟩ : syracuseStep 1359251 = 2038877) B2038877
theorem B3620375 : Blo 714321 3620375 := bstep (se 1 (by rfl) ⟨2715281, by rfl⟩ : syracuseStep 3620375 = 5430563) B5430563
theorem B1818227 : Blo 714321 1818227 := bstep (se 1 (by rfl) ⟨1363670, by rfl⟩ : syracuseStep 1818227 = 2727341) B2727341
theorem B1359479 : Blo 714321 1359479 := bstep (se 1 (by rfl) ⟨1019609, by rfl⟩ : syracuseStep 1359479 = 2039219) B2039219
theorem B1818247 : Blo 714321 1818247 := bstep (se 1 (by rfl) ⟨1363685, by rfl⟩ : syracuseStep 1818247 = 2727371) B2727371
theorem B27836045 : Blo 714321 27836045 := bstep (se 3 (by rfl) ⟨5219258, by rfl⟩ : syracuseStep 27836045 = 10438517) B10438517
theorem B966287 : Blo 714321 966287 := bstep (se 1 (by rfl) ⟨724715, by rfl⟩ : syracuseStep 966287 = 1449431) B1449431
theorem B9191141 : Blo 714321 9191141 := bstep (se 4 (by rfl) ⟨861669, by rfl⟩ : syracuseStep 9191141 = 1723339) B1723339
theorem B4079393 : Blo 714321 4079393 := bstep (se 2 (by rfl) ⟨1529772, by rfl⟩ : syracuseStep 4079393 = 3059545) B3059545
theorem B31768523 : Blo 714321 31768523 := bstep (se 1 (by rfl) ⟨23826392, by rfl⟩ : syracuseStep 31768523 = 47652785) B47652785
theorem B4079645 : Blo 714321 4079645 := bstep (se 3 (by rfl) ⟨764933, by rfl⟩ : syracuseStep 4079645 = 1529867) B1529867
theorem B3063851 : Blo 714321 3063851 := bstep (se 1 (by rfl) ⟨2297888, by rfl⟩ : syracuseStep 3063851 = 4595777) B4595777
theorem B1654985 : Blo 714321 1654985 := bstep (se 2 (by rfl) ⟨620619, by rfl⟩ : syracuseStep 1654985 = 1241239) B1241239
theorem B1720919 : Blo 714321 1720919 := bstep (se 1 (by rfl) ⟨1290689, by rfl⟩ : syracuseStep 1720919 = 2581379) B2581379
theorem B6898277 : Blo 714321 6898277 := bstep (se 4 (by rfl) ⟨646713, by rfl⟩ : syracuseStep 6898277 = 1293427) B1293427
theorem B4899599 : Blo 714321 4899599 := bstep (se 1 (by rfl) ⟨3674699, by rfl⟩ : syracuseStep 4899599 = 7349399) B7349399
theorem B3490781 : Blo 714321 3490781 := bstep (se 3 (by rfl) ⟨654521, by rfl⟩ : syracuseStep 3490781 = 1309043) B1309043
theorem B803983 : Blo 714321 803983 := bstep (se 1 (by rfl) ⟨602987, by rfl⟩ : syracuseStep 803983 = 1205975) B1205975
theorem B1361195 : Blo 714321 1361195 := bstep (se 1 (by rfl) ⟨1020896, by rfl⟩ : syracuseStep 1361195 = 2041793) B2041793
theorem B6899165 : Blo 714321 6899165 := bstep (se 3 (by rfl) ⟨1293593, by rfl⟩ : syracuseStep 6899165 = 2587187) B2587187
theorem B8144387 : Blo 714321 8144387 := bstep (se 1 (by rfl) ⟨6108290, by rfl⟩ : syracuseStep 8144387 = 12216581) B12216581
theorem B1361423 : Blo 714321 1361423 := bstep (se 1 (by rfl) ⟨1021067, by rfl⟩ : syracuseStep 1361423 = 2042135) B2042135
theorem B804487 : Blo 714321 804487 := bstep (se 1 (by rfl) ⟨603365, by rfl⟩ : syracuseStep 804487 = 1206731) B1206731
theorem B804667 : Blo 714321 804667 := bstep (se 1 (by rfl) ⟨603500, by rfl⟩ : syracuseStep 804667 = 1207001) B1207001
theorem B1722379 : Blo 714321 1722379 := bstep (se 1 (by rfl) ⟨1291784, by rfl⟩ : syracuseStep 1722379 = 2583569) B2583569
theorem B805135 : Blo 714321 805135 := bstep (se 1 (by rfl) ⟨603851, by rfl⟩ : syracuseStep 805135 = 1207703) B1207703
theorem B4082035 : Blo 714321 4082035 := bstep (se 1 (by rfl) ⟨3061526, by rfl⟩ : syracuseStep 4082035 = 6123053) B6123053
theorem B2410937 : Blo 714321 2410937 := bstep (se 2 (by rfl) ⟨904101, by rfl⟩ : syracuseStep 2410937 = 1808203) B1808203
theorem B3492305 : Blo 714321 3492305 := bstep (se 2 (by rfl) ⟨1309614, by rfl⟩ : syracuseStep 3492305 = 2619229) B2619229
theorem B3623453 : Blo 714321 3623453 := bstep (se 3 (by rfl) ⟨679397, by rfl⟩ : syracuseStep 3623453 = 1358795) B1358795
theorem B1722995 : Blo 714321 1722995 := bstep (se 1 (by rfl) ⟨1292246, by rfl⟩ : syracuseStep 1722995 = 2584493) B2584493
theorem B3066569 : Blo 714321 3066569 := bstep (se 2 (by rfl) ⟨1149963, by rfl⟩ : syracuseStep 3066569 = 2299927) B2299927
theorem B805639 : Blo 714321 805639 := bstep (se 1 (by rfl) ⟨604229, by rfl⟩ : syracuseStep 805639 = 1208459) B1208459
theorem B1526663 : Blo 714321 1526663 := bstep (se 1 (by rfl) ⟨1144997, by rfl⟩ : syracuseStep 1526663 = 2289995) B2289995
theorem B1362835 : Blo 714321 1362835 := bstep (se 1 (by rfl) ⟨1022126, by rfl⟩ : syracuseStep 1362835 = 2044253) B2044253
theorem B805819 : Blo 714321 805819 := bstep (se 1 (by rfl) ⟨604364, by rfl⟩ : syracuseStep 805819 = 1208729) B1208729
theorem B3623939 : Blo 714321 3623939 := bstep (se 1 (by rfl) ⟨2717954, by rfl⟩ : syracuseStep 3623939 = 5435909) B5435909
theorem B2411531 : Blo 714321 2411531 := bstep (se 1 (by rfl) ⟨1808648, by rfl⟩ : syracuseStep 2411531 = 3617297) B3617297
theorem B68111381 : Blo 714321 68111381 := bstep (se 6 (by rfl) ⟨1596360, by rfl⟩ : syracuseStep 68111381 = 3192721) B3192721
theorem B2411639 : Blo 714321 2411639 := bstep (se 1 (by rfl) ⟨1808729, by rfl⟩ : syracuseStep 2411639 = 3617459) B3617459
theorem B1363063 : Blo 714321 1363063 := bstep (se 1 (by rfl) ⟨1022297, by rfl⟩ : syracuseStep 1363063 = 2044595) B2044595
theorem B4345177 : Blo 714321 4345177 := bstep (se 2 (by rfl) ⟨1629441, by rfl⟩ : syracuseStep 4345177 = 3258883) B3258883
theorem B1723763 : Blo 714321 1723763 := bstep (se 1 (by rfl) ⟨1292822, by rfl⟩ : syracuseStep 1723763 = 2585645) B2585645
theorem B806287 : Blo 714321 806287 := bstep (se 1 (by rfl) ⟨604715, by rfl⟩ : syracuseStep 806287 = 1209431) B1209431
theorem B1724051 : Blo 714321 1724051 := bstep (se 1 (by rfl) ⟨1293038, by rfl⟩ : syracuseStep 1724051 = 2586077) B2586077
theorem B8179379 : Blo 714321 8179379 := bstep (se 1 (by rfl) ⟨6134534, by rfl⟩ : syracuseStep 8179379 = 12269069) B12269069
theorem B2412233 : Blo 714321 2412233 := bstep (se 2 (by rfl) ⟨904587, by rfl⟩ : syracuseStep 2412233 = 1809175) B1809175
theorem B8736473 : Blo 714321 8736473 := bstep (se 2 (by rfl) ⟨3276177, by rfl⟩ : syracuseStep 8736473 = 6552355) B6552355
theorem B4083493 : Blo 714321 4083493 := bstep (se 4 (by rfl) ⟨382827, by rfl⟩ : syracuseStep 4083493 = 765655) B765655
theorem B806791 : Blo 714321 806791 := bstep (se 1 (by rfl) ⟨605093, by rfl⟩ : syracuseStep 806791 = 1210187) B1210187
theorem B806971 : Blo 714321 806971 := bstep (se 1 (by rfl) ⟨605228, by rfl⟩ : syracuseStep 806971 = 1210457) B1210457
theorem B4084019 : Blo 714321 4084019 := bstep (se 1 (by rfl) ⟨3063014, by rfl⟩ : syracuseStep 4084019 = 6126029) B6126029
theorem B2412935 : Blo 714321 2412935 := bstep (se 1 (by rfl) ⟨1809701, by rfl⟩ : syracuseStep 2412935 = 3619403) B3619403
theorem B807439 : Blo 714321 807439 := bstep (se 1 (by rfl) ⟨605579, by rfl⟩ : syracuseStep 807439 = 1211159) B1211159
theorem B3265085 : Blo 714321 3265085 := bstep (se 3 (by rfl) ⟨612203, by rfl⟩ : syracuseStep 3265085 = 1224407) B1224407
theorem B3625559 : Blo 714321 3625559 := bstep (se 1 (by rfl) ⟨2719169, by rfl⟩ : syracuseStep 3625559 = 5438339) B5438339
theorem B905899 : Blo 714321 905899 := bstep (se 1 (by rfl) ⟨679424, by rfl⟩ : syracuseStep 905899 = 1358849) B1358849
theorem B2413313 : Blo 714321 2413313 := bstep (se 2 (by rfl) ⟨904992, by rfl⟩ : syracuseStep 2413313 = 1809985) B1809985
theorem B1725185 : Blo 714321 1725185 := bstep (se 2 (by rfl) ⟨646944, by rfl⟩ : syracuseStep 1725185 = 1293889) B1293889
theorem B2577167 : Blo 714321 2577167 := bstep (se 1 (by rfl) ⟨1932875, by rfl⟩ : syracuseStep 2577167 = 3865751) B3865751
theorem B2184023 : Blo 714321 2184023 := bstep (se 1 (by rfl) ⟨1638017, by rfl⟩ : syracuseStep 2184023 = 3276035) B3276035
theorem B807943 : Blo 714321 807943 := bstep (se 1 (by rfl) ⟨605957, by rfl⟩ : syracuseStep 807943 = 1211915) B1211915
theorem B1725455 : Blo 714321 1725455 := bstep (se 1 (by rfl) ⟨1294091, by rfl⟩ : syracuseStep 1725455 = 2588183) B2588183
theorem B3626045 : Blo 714321 3626045 := bstep (se 3 (by rfl) ⟨679883, by rfl⟩ : syracuseStep 3626045 = 1359767) B1359767
theorem B4412645 : Blo 714321 4412645 := bstep (se 4 (by rfl) ⟨413685, by rfl⟩ : syracuseStep 4412645 = 827371) B827371
theorem B5952953 : Blo 714321 5952953 := bstep (se 2 (by rfl) ⟨2232357, by rfl⟩ : syracuseStep 5952953 = 4464715) B4464715
theorem B2414123 : Blo 714321 2414123 := bstep (se 1 (by rfl) ⟨1810592, by rfl⟩ : syracuseStep 2414123 = 3621185) B3621185
theorem B906871 : Blo 714321 906871 := bstep (se 1 (by rfl) ⟨680153, by rfl⟩ : syracuseStep 906871 = 1360307) B1360307
theorem B4085477 : Blo 714321 4085477 := bstep (se 4 (by rfl) ⟨383013, by rfl⟩ : syracuseStep 4085477 = 766027) B766027
theorem B874255 : Blo 714321 874255 := bstep (se 1 (by rfl) ⟨655691, by rfl⟩ : syracuseStep 874255 = 1311383) B1311383
theorem B907195 : Blo 714321 907195 := bstep (se 1 (by rfl) ⟨680396, by rfl⟩ : syracuseStep 907195 = 1360793) B1360793
theorem B1071503 : Blo 714321 1071503 := bstep (se 1 (by rfl) ⟨803627, by rfl⟩ : syracuseStep 1071503 = 1607255) B1607255
theorem B1071545 : Blo 714321 1071545 := bstep (se 2 (by rfl) ⟨401829, by rfl⟩ : syracuseStep 1071545 = 803659) B803659
theorem B1071623 : Blo 714321 1071623 := bstep (se 1 (by rfl) ⟨803717, by rfl⟩ : syracuseStep 1071623 = 1607435) B1607435
theorem B1071659 : Blo 714321 1071659 := bstep (se 1 (by rfl) ⟨803744, by rfl⟩ : syracuseStep 1071659 = 1607489) B1607489
theorem B1071689 : Blo 714321 1071689 := bstep (se 2 (by rfl) ⟨401883, by rfl⟩ : syracuseStep 1071689 = 803767) B803767
theorem B1071803 : Blo 714321 1071803 := bstep (se 1 (by rfl) ⟨803852, by rfl⟩ : syracuseStep 1071803 = 1607705) B1607705
theorem B1071863 : Blo 714321 1071863 := bstep (se 1 (by rfl) ⟨803897, by rfl⟩ : syracuseStep 1071863 = 1607795) B1607795
theorem B1071887 : Blo 714321 1071887 := bstep (se 1 (by rfl) ⟨803915, by rfl⟩ : syracuseStep 1071887 = 1607831) B1607831
theorem B5823247 : Blo 714321 5823247 := bstep (se 1 (by rfl) ⟨4367435, by rfl⟩ : syracuseStep 5823247 = 8734871) B8734871
theorem B3627827 : Blo 714321 3627827 := bstep (se 1 (by rfl) ⟨2720870, by rfl⟩ : syracuseStep 3627827 = 5441741) B5441741
theorem B1071929 : Blo 714321 1071929 := bstep (se 2 (by rfl) ⟨401973, by rfl⟩ : syracuseStep 1071929 = 803947) B803947
theorem B2415419 : Blo 714321 2415419 := bstep (se 1 (by rfl) ⟨1811564, by rfl⟩ : syracuseStep 2415419 = 3623129) B3623129
theorem B1072007 : Blo 714321 1072007 := bstep (se 1 (by rfl) ⟨804005, by rfl⟩ : syracuseStep 1072007 = 1608011) B1608011
theorem B908167 : Blo 714321 908167 := bstep (se 1 (by rfl) ⟨681125, by rfl⟩ : syracuseStep 908167 = 1362251) B1362251
theorem B1072043 : Blo 714321 1072043 := bstep (se 1 (by rfl) ⟨804032, by rfl⟩ : syracuseStep 1072043 = 1608065) B1608065
theorem B1072073 : Blo 714321 1072073 := bstep (se 2 (by rfl) ⟨402027, by rfl⟩ : syracuseStep 1072073 = 804055) B804055
theorem B12409861 : Blo 714321 12409861 := bstep (se 4 (by rfl) ⟨1163424, by rfl⟩ : syracuseStep 12409861 = 2326849) B2326849
theorem B1072187 : Blo 714321 1072187 := bstep (se 1 (by rfl) ⟨804140, by rfl⟩ : syracuseStep 1072187 = 1608281) B1608281
theorem B1072247 : Blo 714321 1072247 := bstep (se 1 (by rfl) ⟨804185, by rfl⟩ : syracuseStep 1072247 = 1608371) B1608371
theorem B3628151 : Blo 714321 3628151 := bstep (se 1 (by rfl) ⟨2721113, by rfl⟩ : syracuseStep 3628151 = 5442227) B5442227
theorem B1072271 : Blo 714321 1072271 := bstep (se 1 (by rfl) ⟨804203, by rfl⟩ : syracuseStep 1072271 = 1608407) B1608407
theorem B1072313 : Blo 714321 1072313 := bstep (se 2 (by rfl) ⟨402117, by rfl⟩ : syracuseStep 1072313 = 804235) B804235
theorem B39214277 : Blo 714321 39214277 := bstep (se 4 (by rfl) ⟨3676338, by rfl⟩ : syracuseStep 39214277 = 7352677) B7352677
theorem B1072391 : Blo 714321 1072391 := bstep (se 1 (by rfl) ⟨804293, by rfl⟩ : syracuseStep 1072391 = 1608587) B1608587
theorem B2415905 : Blo 714321 2415905 := bstep (se 2 (by rfl) ⟨905964, by rfl⟩ : syracuseStep 2415905 = 1811929) B1811929
theorem B1072427 : Blo 714321 1072427 := bstep (se 1 (by rfl) ⟨804320, by rfl⟩ : syracuseStep 1072427 = 1608641) B1608641
theorem B908587 : Blo 714321 908587 := bstep (se 1 (by rfl) ⟨681440, by rfl⟩ : syracuseStep 908587 = 1362881) B1362881
theorem B1072457 : Blo 714321 1072457 := bstep (se 2 (by rfl) ⟨402171, by rfl⟩ : syracuseStep 1072457 = 804343) B804343
theorem B5168519 : Blo 714321 5168519 := bstep (se 1 (by rfl) ⟨3876389, by rfl⟩ : syracuseStep 5168519 = 7752779) B7752779
theorem B1072571 : Blo 714321 1072571 := bstep (se 1 (by rfl) ⟨804428, by rfl⟩ : syracuseStep 1072571 = 1608857) B1608857
theorem B6872525 : Blo 714321 6872525 := bstep (se 3 (by rfl) ⟨1288598, by rfl⟩ : syracuseStep 6872525 = 2577197) B2577197
theorem B17456593 : Blo 714321 17456593 := bstep (se 2 (by rfl) ⟨6546222, by rfl⟩ : syracuseStep 17456593 = 13092445) B13092445
theorem B1072631 : Blo 714321 1072631 := bstep (se 1 (by rfl) ⟨804473, by rfl⟩ : syracuseStep 1072631 = 1608947) B1608947
theorem B1072655 : Blo 714321 1072655 := bstep (se 1 (by rfl) ⟨804491, by rfl⟩ : syracuseStep 1072655 = 1608983) B1608983
theorem B908815 : Blo 714321 908815 := bstep (se 1 (by rfl) ⟨681611, by rfl⟩ : syracuseStep 908815 = 1363223) B1363223
theorem B1072697 : Blo 714321 1072697 := bstep (se 2 (by rfl) ⟨402261, by rfl⟩ : syracuseStep 1072697 = 804523) B804523
theorem B1072775 : Blo 714321 1072775 := bstep (se 1 (by rfl) ⟨804581, by rfl⟩ : syracuseStep 1072775 = 1609163) B1609163
theorem B1859219 : Blo 714321 1859219 := bstep (se 1 (by rfl) ⟨1394414, by rfl⟩ : syracuseStep 1859219 = 2788829) B2788829
theorem B1072811 : Blo 714321 1072811 := bstep (se 1 (by rfl) ⟨804608, by rfl⟩ : syracuseStep 1072811 = 1609217) B1609217
theorem B1072841 : Blo 714321 1072841 := bstep (se 2 (by rfl) ⟨402315, by rfl⟩ : syracuseStep 1072841 = 804631) B804631
theorem B4349747 : Blo 714321 4349747 := bstep (se 1 (by rfl) ⟨3262310, by rfl⟩ : syracuseStep 4349747 = 6524621) B6524621
theorem B1072955 : Blo 714321 1072955 := bstep (se 1 (by rfl) ⟨804716, by rfl⟩ : syracuseStep 1072955 = 1609433) B1609433
theorem B2416499 : Blo 714321 2416499 := bstep (se 1 (by rfl) ⟨1812374, by rfl⟩ : syracuseStep 2416499 = 3624749) B3624749
theorem B1073015 : Blo 714321 1073015 := bstep (se 1 (by rfl) ⟨804761, by rfl⟩ : syracuseStep 1073015 = 1609523) B1609523
theorem B1073039 : Blo 714321 1073039 := bstep (se 1 (by rfl) ⟨804779, by rfl⟩ : syracuseStep 1073039 = 1609559) B1609559
theorem B1073081 : Blo 714321 1073081 := bstep (se 2 (by rfl) ⟨402405, by rfl⟩ : syracuseStep 1073081 = 804811) B804811
theorem B1073159 : Blo 714321 1073159 := bstep (se 1 (by rfl) ⟨804869, by rfl⟩ : syracuseStep 1073159 = 1609739) B1609739
theorem B1073195 : Blo 714321 1073195 := bstep (se 1 (by rfl) ⟨804896, by rfl⟩ : syracuseStep 1073195 = 1609793) B1609793
theorem B3629123 : Blo 714321 3629123 := bstep (se 1 (by rfl) ⟨2721842, by rfl⟩ : syracuseStep 3629123 = 5443685) B5443685
theorem B1073225 : Blo 714321 1073225 := bstep (se 2 (by rfl) ⟨402459, by rfl⟩ : syracuseStep 1073225 = 804919) B804919
theorem B1073339 : Blo 714321 1073339 := bstep (se 1 (by rfl) ⟨805004, by rfl⟩ : syracuseStep 1073339 = 1610009) B1610009
theorem B1073399 : Blo 714321 1073399 := bstep (se 1 (by rfl) ⟨805049, by rfl⟩ : syracuseStep 1073399 = 1610099) B1610099
theorem B1073423 : Blo 714321 1073423 := bstep (se 1 (by rfl) ⟨805067, by rfl⟩ : syracuseStep 1073423 = 1610135) B1610135
theorem B1073465 : Blo 714321 1073465 := bstep (se 2 (by rfl) ⟨402549, by rfl⟩ : syracuseStep 1073465 = 805099) B805099
theorem B1073543 : Blo 714321 1073543 := bstep (se 1 (by rfl) ⟨805157, by rfl⟩ : syracuseStep 1073543 = 1610315) B1610315
theorem B3629447 : Blo 714321 3629447 := bstep (se 1 (by rfl) ⟨2722085, by rfl⟩ : syracuseStep 3629447 = 5444171) B5444171
theorem B1073579 : Blo 714321 1073579 := bstep (se 1 (by rfl) ⟨805184, by rfl⟩ : syracuseStep 1073579 = 1610369) B1610369
theorem B1073609 : Blo 714321 1073609 := bstep (se 2 (by rfl) ⟨402603, by rfl⟩ : syracuseStep 1073609 = 805207) B805207
theorem B1073723 : Blo 714321 1073723 := bstep (se 1 (by rfl) ⟨805292, by rfl⟩ : syracuseStep 1073723 = 1610585) B1610585
theorem B1073783 : Blo 714321 1073783 := bstep (se 1 (by rfl) ⟨805337, by rfl⟩ : syracuseStep 1073783 = 1610675) B1610675
theorem B1073807 : Blo 714321 1073807 := bstep (se 1 (by rfl) ⟨805355, by rfl⟩ : syracuseStep 1073807 = 1610711) B1610711
theorem B1073849 : Blo 714321 1073849 := bstep (se 2 (by rfl) ⟨402693, by rfl⟩ : syracuseStep 1073849 = 805387) B805387
theorem B1073927 : Blo 714321 1073927 := bstep (se 1 (by rfl) ⟨805445, by rfl⟩ : syracuseStep 1073927 = 1610891) B1610891
theorem B13787941 : Blo 714321 13787941 := bstep (se 4 (by rfl) ⟨1292619, by rfl⟩ : syracuseStep 13787941 = 2585239) B2585239
theorem B1073963 : Blo 714321 1073963 := bstep (se 1 (by rfl) ⟨805472, by rfl⟩ : syracuseStep 1073963 = 1610945) B1610945
theorem B1073993 : Blo 714321 1073993 := bstep (se 2 (by rfl) ⟨402747, by rfl⟩ : syracuseStep 1073993 = 805495) B805495
theorem B2712473 : Blo 714321 2712473 := bstep (se 2 (by rfl) ⟨1017177, by rfl⟩ : syracuseStep 2712473 = 2034355) B2034355
theorem B5235619 : Blo 714321 5235619 := bstep (se 1 (by rfl) ⟨3926714, by rfl⟩ : syracuseStep 5235619 = 7853429) B7853429
theorem B1074107 : Blo 714321 1074107 := bstep (se 1 (by rfl) ⟨805580, by rfl⟩ : syracuseStep 1074107 = 1611161) B1611161
theorem B1106875 : Blo 714321 1106875 := bstep (se 1 (by rfl) ⟨830156, by rfl⟩ : syracuseStep 1106875 = 1660313) B1660313
theorem B1074167 : Blo 714321 1074167 := bstep (se 1 (by rfl) ⟨805625, by rfl⟩ : syracuseStep 1074167 = 1611251) B1611251
theorem B1074191 : Blo 714321 1074191 := bstep (se 1 (by rfl) ⟨805643, by rfl⟩ : syracuseStep 1074191 = 1611287) B1611287
theorem B1074233 : Blo 714321 1074233 := bstep (se 2 (by rfl) ⟨402837, by rfl⟩ : syracuseStep 1074233 = 805675) B805675
theorem B1074311 : Blo 714321 1074311 := bstep (se 1 (by rfl) ⟨805733, by rfl⟩ : syracuseStep 1074311 = 1611467) B1611467
theorem B1074347 : Blo 714321 1074347 := bstep (se 1 (by rfl) ⟨805760, by rfl⟩ : syracuseStep 1074347 = 1611521) B1611521
theorem B1074377 : Blo 714321 1074377 := bstep (se 2 (by rfl) ⟨402891, by rfl⟩ : syracuseStep 1074377 = 805783) B805783
theorem B1205563 : Blo 714321 1205563 := bstep (se 1 (by rfl) ⟨904172, by rfl⟩ : syracuseStep 1205563 = 1808345) B1808345
theorem B1074491 : Blo 714321 1074491 := bstep (se 1 (by rfl) ⟨805868, by rfl⟩ : syracuseStep 1074491 = 1611737) B1611737
theorem B1074551 : Blo 714321 1074551 := bstep (se 1 (by rfl) ⟨805913, by rfl⟩ : syracuseStep 1074551 = 1611827) B1611827
theorem B1074575 : Blo 714321 1074575 := bstep (se 1 (by rfl) ⟨805931, by rfl⟩ : syracuseStep 1074575 = 1611863) B1611863
theorem B26076593 : Blo 714321 26076593 := bstep (se 2 (by rfl) ⟨9778722, by rfl⟩ : syracuseStep 26076593 = 19557445) B19557445
theorem B1074617 : Blo 714321 1074617 := bstep (se 2 (by rfl) ⟨402981, by rfl⟩ : syracuseStep 1074617 = 805963) B805963
theorem B1205705 : Blo 714321 1205705 := bstep (se 2 (by rfl) ⟨452139, by rfl⟩ : syracuseStep 1205705 = 904279) B904279
theorem B8807939 : Blo 714321 8807939 := bstep (se 1 (by rfl) ⟨6605954, by rfl⟩ : syracuseStep 8807939 = 13211909) B13211909
theorem B1074695 : Blo 714321 1074695 := bstep (se 1 (by rfl) ⟨806021, by rfl⟩ : syracuseStep 1074695 = 1612043) B1612043
theorem B1074731 : Blo 714321 1074731 := bstep (se 1 (by rfl) ⟨806048, by rfl⟩ : syracuseStep 1074731 = 1612097) B1612097
theorem B2451005 : Blo 714321 2451005 := bstep (se 3 (by rfl) ⟨459563, by rfl⟩ : syracuseStep 2451005 = 919127) B919127
theorem B1074761 : Blo 714321 1074761 := bstep (se 2 (by rfl) ⟨403035, by rfl⟩ : syracuseStep 1074761 = 806071) B806071
theorem B714375 : Blo 714321 714375 := bstep (se 1 (by rfl) ⟨535781, by rfl⟩ : syracuseStep 714375 = 1071563) B1071563
theorem B1631879 : Blo 714321 1631879 := bstep (se 1 (by rfl) ⟨1223909, by rfl⟩ : syracuseStep 1631879 = 2447819) B2447819
theorem B714383 : Blo 714321 714383 := bstep (se 1 (by rfl) ⟨535787, by rfl⟩ : syracuseStep 714383 = 1071575) B1071575
theorem B714427 : Blo 714321 714427 := bstep (se 1 (by rfl) ⟨535820, by rfl⟩ : syracuseStep 714427 = 1071641) B1071641
theorem B1074875 : Blo 714321 1074875 := bstep (se 1 (by rfl) ⟨806156, by rfl⟩ : syracuseStep 1074875 = 1612313) B1612313
theorem B1074935 : Blo 714321 1074935 := bstep (se 1 (by rfl) ⟨806201, by rfl⟩ : syracuseStep 1074935 = 1612403) B1612403
theorem B714503 : Blo 714321 714503 := bstep (se 1 (by rfl) ⟨535877, by rfl⟩ : syracuseStep 714503 = 1071755) B1071755
theorem B714511 : Blo 714321 714511 := bstep (se 1 (by rfl) ⟨535883, by rfl⟩ : syracuseStep 714511 = 1071767) B1071767
theorem B1074959 : Blo 714321 1074959 := bstep (se 1 (by rfl) ⟨806219, by rfl⟩ : syracuseStep 1074959 = 1612439) B1612439
theorem B10348337 : Blo 714321 10348337 := bstep (se 2 (by rfl) ⟨3880626, by rfl⟩ : syracuseStep 10348337 = 7761253) B7761253
theorem B1075001 : Blo 714321 1075001 := bstep (se 2 (by rfl) ⟨403125, by rfl⟩ : syracuseStep 1075001 = 806251) B806251
theorem B714555 : Blo 714321 714555 := bstep (se 1 (by rfl) ⟨535916, by rfl⟩ : syracuseStep 714555 = 1071833) B1071833
theorem B2713459 : Blo 714321 2713459 := bstep (se 1 (by rfl) ⟨2035094, by rfl⟩ : syracuseStep 2713459 = 4070189) B4070189
theorem B2582387 : Blo 714321 2582387 := bstep (se 1 (by rfl) ⟨1936790, by rfl⟩ : syracuseStep 2582387 = 3873581) B3873581
theorem B714631 : Blo 714321 714631 := bstep (se 1 (by rfl) ⟨535973, by rfl⟩ : syracuseStep 714631 = 1071947) B1071947
theorem B1075079 : Blo 714321 1075079 := bstep (se 1 (by rfl) ⟨806309, by rfl⟩ : syracuseStep 1075079 = 1612619) B1612619
theorem B714639 : Blo 714321 714639 := bstep (se 1 (by rfl) ⟨535979, by rfl⟩ : syracuseStep 714639 = 1071959) B1071959
theorem B1075115 : Blo 714321 1075115 := bstep (se 1 (by rfl) ⟨806336, by rfl⟩ : syracuseStep 1075115 = 1612673) B1612673
theorem B714683 : Blo 714321 714683 := bstep (se 1 (by rfl) ⟨536012, by rfl⟩ : syracuseStep 714683 = 1072025) B1072025
theorem B1075145 : Blo 714321 1075145 := bstep (se 2 (by rfl) ⟨403179, by rfl⟩ : syracuseStep 1075145 = 806359) B806359
theorem B5171147 : Blo 714321 5171147 := bstep (se 1 (by rfl) ⟨3878360, by rfl⟩ : syracuseStep 5171147 = 7756721) B7756721
theorem B714759 : Blo 714321 714759 := bstep (se 1 (by rfl) ⟨536069, by rfl⟩ : syracuseStep 714759 = 1072139) B1072139
theorem B714767 : Blo 714321 714767 := bstep (se 1 (by rfl) ⟨536075, by rfl⟩ : syracuseStep 714767 = 1072151) B1072151
theorem B714811 : Blo 714321 714811 := bstep (se 1 (by rfl) ⟨536108, by rfl⟩ : syracuseStep 714811 = 1072217) B1072217
theorem B1075259 : Blo 714321 1075259 := bstep (se 1 (by rfl) ⟨806444, by rfl⟩ : syracuseStep 1075259 = 1612889) B1612889
theorem B1075319 : Blo 714321 1075319 := bstep (se 1 (by rfl) ⟨806489, by rfl⟩ : syracuseStep 1075319 = 1612979) B1612979
theorem B714887 : Blo 714321 714887 := bstep (se 1 (by rfl) ⟨536165, by rfl⟩ : syracuseStep 714887 = 1072331) B1072331
theorem B1206407 : Blo 714321 1206407 := bstep (se 1 (by rfl) ⟨904805, by rfl⟩ : syracuseStep 1206407 = 1809611) B1809611
theorem B714895 : Blo 714321 714895 := bstep (se 1 (by rfl) ⟨536171, by rfl⟩ : syracuseStep 714895 = 1072343) B1072343
theorem B1075343 : Blo 714321 1075343 := bstep (se 1 (by rfl) ⟨806507, by rfl⟩ : syracuseStep 1075343 = 1613015) B1613015
theorem B3434669 : Blo 714321 3434669 := bstep (se 3 (by rfl) ⟨644000, by rfl⟩ : syracuseStep 3434669 = 1288001) B1288001
theorem B1075385 : Blo 714321 1075385 := bstep (se 2 (by rfl) ⟨403269, by rfl⟩ : syracuseStep 1075385 = 806539) B806539
theorem B714939 : Blo 714321 714939 := bstep (se 1 (by rfl) ⟨536204, by rfl⟩ : syracuseStep 714939 = 1072409) B1072409
theorem B5171401 : Blo 714321 5171401 := bstep (se 2 (by rfl) ⟨1939275, by rfl⟩ : syracuseStep 5171401 = 3878551) B3878551
theorem B715015 : Blo 714321 715015 := bstep (se 1 (by rfl) ⟨536261, by rfl⟩ : syracuseStep 715015 = 1072523) B1072523
theorem B1075463 : Blo 714321 1075463 := bstep (se 1 (by rfl) ⟨806597, by rfl⟩ : syracuseStep 1075463 = 1613195) B1613195
theorem B715023 : Blo 714321 715023 := bstep (se 1 (by rfl) ⟨536267, by rfl⟩ : syracuseStep 715023 = 1072535) B1072535
theorem B1075499 : Blo 714321 1075499 := bstep (se 1 (by rfl) ⟨806624, by rfl⟩ : syracuseStep 1075499 = 1613249) B1613249
theorem B715067 : Blo 714321 715067 := bstep (se 1 (by rfl) ⟨536300, by rfl⟩ : syracuseStep 715067 = 1072601) B1072601
theorem B1075529 : Blo 714321 1075529 := bstep (se 2 (by rfl) ⟨403323, by rfl⟩ : syracuseStep 1075529 = 806647) B806647
theorem B1862003 : Blo 714321 1862003 := bstep (se 1 (by rfl) ⟨1396502, by rfl⟩ : syracuseStep 1862003 = 2793005) B2793005
theorem B5794183 : Blo 714321 5794183 := bstep (se 1 (by rfl) ⟨4345637, by rfl⟩ : syracuseStep 5794183 = 8691275) B8691275
theorem B715143 : Blo 714321 715143 := bstep (se 1 (by rfl) ⟨536357, by rfl⟩ : syracuseStep 715143 = 1072715) B1072715
theorem B715151 : Blo 714321 715151 := bstep (se 1 (by rfl) ⟨536363, by rfl⟩ : syracuseStep 715151 = 1072727) B1072727
theorem B2419091 : Blo 714321 2419091 := bstep (se 1 (by rfl) ⟨1814318, by rfl⟩ : syracuseStep 2419091 = 3628637) B3628637
theorem B715195 : Blo 714321 715195 := bstep (se 1 (by rfl) ⟨536396, by rfl⟩ : syracuseStep 715195 = 1072793) B1072793
theorem B1075643 : Blo 714321 1075643 := bstep (se 1 (by rfl) ⟨806732, by rfl⟩ : syracuseStep 1075643 = 1613465) B1613465
theorem B1075703 : Blo 714321 1075703 := bstep (se 1 (by rfl) ⟨806777, by rfl⟩ : syracuseStep 1075703 = 1613555) B1613555
theorem B715271 : Blo 714321 715271 := bstep (se 1 (by rfl) ⟨536453, by rfl⟩ : syracuseStep 715271 = 1072907) B1072907
theorem B715279 : Blo 714321 715279 := bstep (se 1 (by rfl) ⟨536459, by rfl⟩ : syracuseStep 715279 = 1072919) B1072919
theorem B1075727 : Blo 714321 1075727 := bstep (se 1 (by rfl) ⟨806795, by rfl⟩ : syracuseStep 1075727 = 1613591) B1613591
theorem B17885731 : Blo 714321 17885731 := bstep (se 1 (by rfl) ⟨13414298, by rfl⟩ : syracuseStep 17885731 = 26828597) B26828597
theorem B1075769 : Blo 714321 1075769 := bstep (se 2 (by rfl) ⟨403413, by rfl⟩ : syracuseStep 1075769 = 806827) B806827
theorem B715323 : Blo 714321 715323 := bstep (se 1 (by rfl) ⟨536492, by rfl⟩ : syracuseStep 715323 = 1072985) B1072985
theorem B715399 : Blo 714321 715399 := bstep (se 1 (by rfl) ⟨536549, by rfl⟩ : syracuseStep 715399 = 1073099) B1073099
theorem B1075847 : Blo 714321 1075847 := bstep (se 1 (by rfl) ⟨806885, by rfl⟩ : syracuseStep 1075847 = 1613771) B1613771
theorem B715407 : Blo 714321 715407 := bstep (se 1 (by rfl) ⟨536555, by rfl⟩ : syracuseStep 715407 = 1073111) B1073111
theorem B1075883 : Blo 714321 1075883 := bstep (se 1 (by rfl) ⟨806912, by rfl⟩ : syracuseStep 1075883 = 1613825) B1613825
theorem B715451 : Blo 714321 715451 := bstep (se 1 (by rfl) ⟨536588, by rfl⟩ : syracuseStep 715451 = 1073177) B1073177
theorem B1075913 : Blo 714321 1075913 := bstep (se 2 (by rfl) ⟨403467, by rfl⟩ : syracuseStep 1075913 = 806935) B806935
theorem B55896803 : Blo 714321 55896803 := bstep (se 1 (by rfl) ⟨41922602, by rfl⟩ : syracuseStep 55896803 = 83845205) B83845205
theorem B715527 : Blo 714321 715527 := bstep (se 1 (by rfl) ⟨536645, by rfl⟩ : syracuseStep 715527 = 1073291) B1073291
theorem B1207055 : Blo 714321 1207055 := bstep (se 1 (by rfl) ⟨905291, by rfl⟩ : syracuseStep 1207055 = 1810583) B1810583
theorem B715535 : Blo 714321 715535 := bstep (se 1 (by rfl) ⟨536651, by rfl⟩ : syracuseStep 715535 = 1073303) B1073303
theorem B944939 : Blo 714321 944939 := bstep (se 1 (by rfl) ⟨708704, by rfl⟩ : syracuseStep 944939 = 1417409) B1417409
theorem B6548273 : Blo 714321 6548273 := bstep (se 2 (by rfl) ⟨2455602, by rfl⟩ : syracuseStep 6548273 = 4911205) B4911205
theorem B715579 : Blo 714321 715579 := bstep (se 1 (by rfl) ⟨536684, by rfl⟩ : syracuseStep 715579 = 1073369) B1073369
theorem B1076027 : Blo 714321 1076027 := bstep (se 1 (by rfl) ⟨807020, by rfl⟩ : syracuseStep 1076027 = 1614041) B1614041
theorem B5499737 : Blo 714321 5499737 := bstep (se 2 (by rfl) ⟨2062401, by rfl⟩ : syracuseStep 5499737 = 4124803) B4124803
theorem B1076087 : Blo 714321 1076087 := bstep (se 1 (by rfl) ⟨807065, by rfl⟩ : syracuseStep 1076087 = 1614131) B1614131
theorem B715655 : Blo 714321 715655 := bstep (se 1 (by rfl) ⟨536741, by rfl⟩ : syracuseStep 715655 = 1073483) B1073483
theorem B715663 : Blo 714321 715663 := bstep (se 1 (by rfl) ⟨536747, by rfl⟩ : syracuseStep 715663 = 1073495) B1073495
theorem B1076111 : Blo 714321 1076111 := bstep (se 1 (by rfl) ⟨807083, by rfl⟩ : syracuseStep 1076111 = 1614167) B1614167
theorem B1076153 : Blo 714321 1076153 := bstep (se 2 (by rfl) ⟨403557, by rfl⟩ : syracuseStep 1076153 = 807115) B807115
theorem B715707 : Blo 714321 715707 := bstep (se 1 (by rfl) ⟨536780, by rfl⟩ : syracuseStep 715707 = 1073561) B1073561
theorem B715783 : Blo 714321 715783 := bstep (se 1 (by rfl) ⟨536837, by rfl⟩ : syracuseStep 715783 = 1073675) B1073675
theorem B1076231 : Blo 714321 1076231 := bstep (se 1 (by rfl) ⟨807173, by rfl⟩ : syracuseStep 1076231 = 1614347) B1614347
theorem B715791 : Blo 714321 715791 := bstep (se 1 (by rfl) ⟨536843, by rfl⟩ : syracuseStep 715791 = 1073687) B1073687
theorem B1076267 : Blo 714321 1076267 := bstep (se 1 (by rfl) ⟨807200, by rfl⟩ : syracuseStep 1076267 = 1614401) B1614401
theorem B715835 : Blo 714321 715835 := bstep (se 1 (by rfl) ⟨536876, by rfl⟩ : syracuseStep 715835 = 1073753) B1073753
theorem B1076297 : Blo 714321 1076297 := bstep (se 2 (by rfl) ⟨403611, by rfl⟩ : syracuseStep 1076297 = 807223) B807223
theorem B715911 : Blo 714321 715911 := bstep (se 1 (by rfl) ⟨536933, by rfl⟩ : syracuseStep 715911 = 1073867) B1073867
theorem B715919 : Blo 714321 715919 := bstep (se 1 (by rfl) ⟨536939, by rfl⟩ : syracuseStep 715919 = 1073879) B1073879
theorem B715963 : Blo 714321 715963 := bstep (se 1 (by rfl) ⟨536972, by rfl⟩ : syracuseStep 715963 = 1073945) B1073945
theorem B1076411 : Blo 714321 1076411 := bstep (se 1 (by rfl) ⟨807308, by rfl⟩ : syracuseStep 1076411 = 1614617) B1614617
theorem B1076471 : Blo 714321 1076471 := bstep (se 1 (by rfl) ⟨807353, by rfl⟩ : syracuseStep 1076471 = 1614707) B1614707
theorem B716039 : Blo 714321 716039 := bstep (se 1 (by rfl) ⟨537029, by rfl⟩ : syracuseStep 716039 = 1074059) B1074059
theorem B716047 : Blo 714321 716047 := bstep (se 1 (by rfl) ⟨537035, by rfl⟩ : syracuseStep 716047 = 1074071) B1074071
theorem B1076495 : Blo 714321 1076495 := bstep (se 1 (by rfl) ⟨807371, by rfl⟩ : syracuseStep 1076495 = 1614743) B1614743
theorem B1207595 : Blo 714321 1207595 := bstep (se 1 (by rfl) ⟨905696, by rfl⟩ : syracuseStep 1207595 = 1811393) B1811393
theorem B1076537 : Blo 714321 1076537 := bstep (se 2 (by rfl) ⟨403701, by rfl⟩ : syracuseStep 1076537 = 807403) B807403
theorem B716091 : Blo 714321 716091 := bstep (se 1 (by rfl) ⟨537068, by rfl⟩ : syracuseStep 716091 = 1074137) B1074137
theorem B716167 : Blo 714321 716167 := bstep (se 1 (by rfl) ⟨537125, by rfl⟩ : syracuseStep 716167 = 1074251) B1074251
theorem B1076615 : Blo 714321 1076615 := bstep (se 1 (by rfl) ⟨807461, by rfl⟩ : syracuseStep 1076615 = 1614923) B1614923
theorem B716175 : Blo 714321 716175 := bstep (se 1 (by rfl) ⟨537131, by rfl⟩ : syracuseStep 716175 = 1074263) B1074263
theorem B4353425 : Blo 714321 4353425 := bstep (se 2 (by rfl) ⟨1632534, by rfl⟩ : syracuseStep 4353425 = 3265069) B3265069
theorem B1076651 : Blo 714321 1076651 := bstep (se 1 (by rfl) ⟨807488, by rfl⟩ : syracuseStep 1076651 = 1614977) B1614977
theorem B716219 : Blo 714321 716219 := bstep (se 1 (by rfl) ⟨537164, by rfl⟩ : syracuseStep 716219 = 1074329) B1074329
theorem B1076681 : Blo 714321 1076681 := bstep (se 2 (by rfl) ⟨403755, by rfl⟩ : syracuseStep 1076681 = 807511) B807511
theorem B716295 : Blo 714321 716295 := bstep (se 1 (by rfl) ⟨537221, by rfl⟩ : syracuseStep 716295 = 1074443) B1074443
theorem B716303 : Blo 714321 716303 := bstep (se 1 (by rfl) ⟨537227, by rfl⟩ : syracuseStep 716303 = 1074455) B1074455
theorem B716347 : Blo 714321 716347 := bstep (se 1 (by rfl) ⟨537260, by rfl⟩ : syracuseStep 716347 = 1074521) B1074521
theorem B1076795 : Blo 714321 1076795 := bstep (se 1 (by rfl) ⟨807596, by rfl⟩ : syracuseStep 1076795 = 1615193) B1615193
theorem B1076855 : Blo 714321 1076855 := bstep (se 1 (by rfl) ⟨807641, by rfl⟩ : syracuseStep 1076855 = 1615283) B1615283
theorem B716423 : Blo 714321 716423 := bstep (se 1 (by rfl) ⟨537317, by rfl⟩ : syracuseStep 716423 = 1074635) B1074635
theorem B716431 : Blo 714321 716431 := bstep (se 1 (by rfl) ⟨537323, by rfl⟩ : syracuseStep 716431 = 1074647) B1074647
theorem B1076879 : Blo 714321 1076879 := bstep (se 1 (by rfl) ⟨807659, by rfl⟩ : syracuseStep 1076879 = 1615319) B1615319
theorem B9072307 : Blo 714321 9072307 := bstep (se 1 (by rfl) ⟨6804230, by rfl⟩ : syracuseStep 9072307 = 13608461) B13608461
theorem B1207993 : Blo 714321 1207993 := bstep (se 2 (by rfl) ⟨452997, by rfl⟩ : syracuseStep 1207993 = 905995) B905995
theorem B1076921 : Blo 714321 1076921 := bstep (se 2 (by rfl) ⟨403845, by rfl⟩ : syracuseStep 1076921 = 807691) B807691
theorem B716475 : Blo 714321 716475 := bstep (se 1 (by rfl) ⟨537356, by rfl⟩ : syracuseStep 716475 = 1074713) B1074713
theorem B4484845 : Blo 714321 4484845 := bstep (se 3 (by rfl) ⟨840908, by rfl⟩ : syracuseStep 4484845 = 1681817) B1681817
theorem B716551 : Blo 714321 716551 := bstep (se 1 (by rfl) ⟨537413, by rfl⟩ : syracuseStep 716551 = 1074827) B1074827
theorem B1076999 : Blo 714321 1076999 := bstep (se 1 (by rfl) ⟨807749, by rfl⟩ : syracuseStep 1076999 = 1615499) B1615499
theorem B716559 : Blo 714321 716559 := bstep (se 1 (by rfl) ⟨537419, by rfl⟩ : syracuseStep 716559 = 1074839) B1074839
theorem B2420495 : Blo 714321 2420495 := bstep (se 1 (by rfl) ⟨1815371, by rfl⟩ : syracuseStep 2420495 = 3630743) B3630743
theorem B1077035 : Blo 714321 1077035 := bstep (se 1 (by rfl) ⟨807776, by rfl⟩ : syracuseStep 1077035 = 1615553) B1615553
theorem B716603 : Blo 714321 716603 := bstep (se 1 (by rfl) ⟨537452, by rfl⟩ : syracuseStep 716603 = 1074905) B1074905
theorem B1077065 : Blo 714321 1077065 := bstep (se 2 (by rfl) ⟨403899, by rfl⟩ : syracuseStep 1077065 = 807799) B807799
theorem B1961815 : Blo 714321 1961815 := bstep (se 1 (by rfl) ⟨1471361, by rfl⟩ : syracuseStep 1961815 = 2942723) B2942723
theorem B3633011 : Blo 714321 3633011 := bstep (se 1 (by rfl) ⟨2724758, by rfl⟩ : syracuseStep 3633011 = 5449517) B5449517
theorem B716679 : Blo 714321 716679 := bstep (se 1 (by rfl) ⟨537509, by rfl⟩ : syracuseStep 716679 = 1075019) B1075019
theorem B716687 : Blo 714321 716687 := bstep (se 1 (by rfl) ⟨537515, by rfl⟩ : syracuseStep 716687 = 1075031) B1075031
theorem B716731 : Blo 714321 716731 := bstep (se 1 (by rfl) ⟨537548, by rfl⟩ : syracuseStep 716731 = 1075097) B1075097
theorem B1077179 : Blo 714321 1077179 := bstep (se 1 (by rfl) ⟨807884, by rfl⟩ : syracuseStep 1077179 = 1615769) B1615769
theorem B1077239 : Blo 714321 1077239 := bstep (se 1 (by rfl) ⟨807929, by rfl⟩ : syracuseStep 1077239 = 1615859) B1615859
theorem B716807 : Blo 714321 716807 := bstep (se 1 (by rfl) ⟨537605, by rfl⟩ : syracuseStep 716807 = 1075211) B1075211
theorem B716815 : Blo 714321 716815 := bstep (se 1 (by rfl) ⟨537611, by rfl⟩ : syracuseStep 716815 = 1075223) B1075223
theorem B1077263 : Blo 714321 1077263 := bstep (se 1 (by rfl) ⟨807947, by rfl⟩ : syracuseStep 1077263 = 1615895) B1615895
theorem B2715677 : Blo 714321 2715677 := bstep (se 3 (by rfl) ⟨509189, by rfl⟩ : syracuseStep 2715677 = 1018379) B1018379
theorem B2420765 : Blo 714321 2420765 := bstep (se 3 (by rfl) ⟨453893, by rfl⟩ : syracuseStep 2420765 = 907787) B907787
theorem B1077305 : Blo 714321 1077305 := bstep (se 2 (by rfl) ⟨403989, by rfl⟩ : syracuseStep 1077305 = 807979) B807979
theorem B716859 : Blo 714321 716859 := bstep (se 1 (by rfl) ⟨537644, by rfl⟩ : syracuseStep 716859 = 1075289) B1075289
theorem B15921269 : Blo 714321 15921269 := bstep (se 5 (by rfl) ⟨746309, by rfl⟩ : syracuseStep 15921269 = 1492619) B1492619
theorem B716935 : Blo 714321 716935 := bstep (se 1 (by rfl) ⟨537701, by rfl⟩ : syracuseStep 716935 = 1075403) B1075403
theorem B1077383 : Blo 714321 1077383 := bstep (se 1 (by rfl) ⟨808037, by rfl⟩ : syracuseStep 1077383 = 1616075) B1616075
theorem B716943 : Blo 714321 716943 := bstep (se 1 (by rfl) ⟨537707, by rfl⟩ : syracuseStep 716943 = 1075415) B1075415
theorem B1077419 : Blo 714321 1077419 := bstep (se 1 (by rfl) ⟨808064, by rfl⟩ : syracuseStep 1077419 = 1616129) B1616129
theorem B716987 : Blo 714321 716987 := bstep (se 1 (by rfl) ⟨537740, by rfl⟩ : syracuseStep 716987 = 1075481) B1075481
theorem B1077449 : Blo 714321 1077449 := bstep (se 2 (by rfl) ⟨404043, by rfl⟩ : syracuseStep 1077449 = 808087) B808087
theorem B717063 : Blo 714321 717063 := bstep (se 1 (by rfl) ⟨537797, by rfl⟩ : syracuseStep 717063 = 1075595) B1075595
theorem B717071 : Blo 714321 717071 := bstep (se 1 (by rfl) ⟨537803, by rfl⟩ : syracuseStep 717071 = 1075607) B1075607
theorem B717115 : Blo 714321 717115 := bstep (se 1 (by rfl) ⟨537836, by rfl⟩ : syracuseStep 717115 = 1075673) B1075673
theorem B3633497 : Blo 714321 3633497 := bstep (se 2 (by rfl) ⟨1362561, by rfl⟩ : syracuseStep 3633497 = 2725123) B2725123
theorem B1208695 : Blo 714321 1208695 := bstep (se 1 (by rfl) ⟨906521, by rfl⟩ : syracuseStep 1208695 = 1813043) B1813043
theorem B717191 : Blo 714321 717191 := bstep (se 1 (by rfl) ⟨537893, by rfl⟩ : syracuseStep 717191 = 1075787) B1075787
theorem B717199 : Blo 714321 717199 := bstep (se 1 (by rfl) ⟨537899, by rfl⟩ : syracuseStep 717199 = 1075799) B1075799
theorem B717243 : Blo 714321 717243 := bstep (se 1 (by rfl) ⟨537932, by rfl⟩ : syracuseStep 717243 = 1075865) B1075865
theorem B717319 : Blo 714321 717319 := bstep (se 1 (by rfl) ⟨537989, by rfl⟩ : syracuseStep 717319 = 1075979) B1075979
theorem B717327 : Blo 714321 717327 := bstep (se 1 (by rfl) ⟨537995, by rfl⟩ : syracuseStep 717327 = 1075991) B1075991
theorem B1208891 : Blo 714321 1208891 := bstep (se 1 (by rfl) ⟨906668, by rfl⟩ : syracuseStep 1208891 = 1813337) B1813337
theorem B717371 : Blo 714321 717371 := bstep (se 1 (by rfl) ⟨538028, by rfl⟩ : syracuseStep 717371 = 1076057) B1076057
theorem B2585155 : Blo 714321 2585155 := bstep (se 1 (by rfl) ⟨1938866, by rfl⟩ : syracuseStep 2585155 = 3877733) B3877733
theorem B717447 : Blo 714321 717447 := bstep (se 1 (by rfl) ⟨538085, by rfl⟩ : syracuseStep 717447 = 1076171) B1076171
theorem B717455 : Blo 714321 717455 := bstep (se 1 (by rfl) ⟨538091, by rfl⟩ : syracuseStep 717455 = 1076183) B1076183
theorem B717499 : Blo 714321 717499 := bstep (se 1 (by rfl) ⟨538124, by rfl⟩ : syracuseStep 717499 = 1076249) B1076249
theorem B2716361 : Blo 714321 2716361 := bstep (se 2 (by rfl) ⟨1018635, by rfl⟩ : syracuseStep 2716361 = 2037271) B2037271
theorem B717575 : Blo 714321 717575 := bstep (se 1 (by rfl) ⟨538181, by rfl⟩ : syracuseStep 717575 = 1076363) B1076363
theorem B717583 : Blo 714321 717583 := bstep (se 1 (by rfl) ⟨538187, by rfl⟩ : syracuseStep 717583 = 1076375) B1076375
theorem B717627 : Blo 714321 717627 := bstep (se 1 (by rfl) ⟨538220, by rfl⟩ : syracuseStep 717627 = 1076441) B1076441
theorem B717703 : Blo 714321 717703 := bstep (se 1 (by rfl) ⟨538277, by rfl⟩ : syracuseStep 717703 = 1076555) B1076555
theorem B717711 : Blo 714321 717711 := bstep (se 1 (by rfl) ⟨538283, by rfl⟩ : syracuseStep 717711 = 1076567) B1076567
theorem B717755 : Blo 714321 717755 := bstep (se 1 (by rfl) ⟨538316, by rfl⟩ : syracuseStep 717755 = 1076633) B1076633
theorem B1209289 : Blo 714321 1209289 := bstep (se 2 (by rfl) ⟨453483, by rfl⟩ : syracuseStep 1209289 = 906967) B906967
theorem B717831 : Blo 714321 717831 := bstep (se 1 (by rfl) ⟨538373, by rfl⟩ : syracuseStep 717831 = 1076747) B1076747
theorem B717839 : Blo 714321 717839 := bstep (se 1 (by rfl) ⟨538379, by rfl⟩ : syracuseStep 717839 = 1076759) B1076759
theorem B717883 : Blo 714321 717883 := bstep (se 1 (by rfl) ⟨538412, by rfl⟩ : syracuseStep 717883 = 1076825) B1076825
theorem B717959 : Blo 714321 717959 := bstep (se 1 (by rfl) ⟨538469, by rfl⟩ : syracuseStep 717959 = 1076939) B1076939
theorem B717967 : Blo 714321 717967 := bstep (se 1 (by rfl) ⟨538475, by rfl⟩ : syracuseStep 717967 = 1076951) B1076951
theorem B718011 : Blo 714321 718011 := bstep (se 1 (by rfl) ⟨538508, by rfl⟩ : syracuseStep 718011 = 1077017) B1077017
theorem B718087 : Blo 714321 718087 := bstep (se 1 (by rfl) ⟨538565, by rfl⟩ : syracuseStep 718087 = 1077131) B1077131
theorem B718095 : Blo 714321 718095 := bstep (se 1 (by rfl) ⟨538571, by rfl⟩ : syracuseStep 718095 = 1077143) B1077143
theorem B718139 : Blo 714321 718139 := bstep (se 1 (by rfl) ⟨538604, by rfl⟩ : syracuseStep 718139 = 1077209) B1077209
theorem B718215 : Blo 714321 718215 := bstep (se 1 (by rfl) ⟨538661, by rfl⟩ : syracuseStep 718215 = 1077323) B1077323
theorem B816527 : Blo 714321 816527 := bstep (se 1 (by rfl) ⟨612395, by rfl⟩ : syracuseStep 816527 = 1224791) B1224791
theorem B718223 : Blo 714321 718223 := bstep (se 1 (by rfl) ⟨538667, by rfl⟩ : syracuseStep 718223 = 1077335) B1077335
theorem B2422169 : Blo 714321 2422169 := bstep (se 2 (by rfl) ⟨908313, by rfl⟩ : syracuseStep 2422169 = 1816627) B1816627
theorem B718267 : Blo 714321 718267 := bstep (se 1 (by rfl) ⟨538700, by rfl⟩ : syracuseStep 718267 = 1077401) B1077401
theorem B5436881 : Blo 714321 5436881 := bstep (se 2 (by rfl) ⟨2038830, by rfl⟩ : syracuseStep 5436881 = 4077661) B4077661
theorem B1209991 : Blo 714321 1209991 := bstep (se 1 (by rfl) ⟨907493, by rfl⟩ : syracuseStep 1209991 = 1814987) B1814987
theorem B2422871 : Blo 714321 2422871 := bstep (se 1 (by rfl) ⟨1817153, by rfl⟩ : syracuseStep 2422871 = 3634307) B3634307
theorem B2291969 : Blo 714321 2291969 := bstep (se 2 (by rfl) ⟨859488, by rfl⟩ : syracuseStep 2291969 = 1718977) B1718977
theorem B1210639 : Blo 714321 1210639 := bstep (se 1 (by rfl) ⟨907979, by rfl⟩ : syracuseStep 1210639 = 1815959) B1815959
theorem B3635603 : Blo 714321 3635603 := bstep (se 1 (by rfl) ⟨2726702, by rfl⟩ : syracuseStep 3635603 = 5453405) B5453405
theorem B2718137 : Blo 714321 2718137 := bstep (se 2 (by rfl) ⟨1019301, by rfl⟩ : syracuseStep 2718137 = 2038603) B2038603
theorem B2423357 : Blo 714321 2423357 := bstep (se 3 (by rfl) ⟨454379, by rfl⟩ : syracuseStep 2423357 = 908759) B908759
theorem B3439297 : Blo 714321 3439297 := bstep (se 2 (by rfl) ⟨1289736, by rfl⟩ : syracuseStep 3439297 = 2579473) B2579473
theorem B26114831 : Blo 714321 26114831 := bstep (se 1 (by rfl) ⟨19586123, by rfl⟩ : syracuseStep 26114831 = 39172247) B39172247
theorem B1211179 : Blo 714321 1211179 := bstep (se 1 (by rfl) ⟨908384, by rfl⟩ : syracuseStep 1211179 = 1816769) B1816769
theorem B1211321 : Blo 714321 1211321 := bstep (se 2 (by rfl) ⟨454245, by rfl⟩ : syracuseStep 1211321 = 908491) B908491
theorem B9305549 : Blo 714321 9305549 := bstep (se 3 (by rfl) ⟨1744790, by rfl⟩ : syracuseStep 9305549 = 3489581) B3489581
theorem B5799377 : Blo 714321 5799377 := bstep (se 2 (by rfl) ⟨2174766, by rfl⟩ : syracuseStep 5799377 = 4349533) B4349533
theorem B8289869 : Blo 714321 8289869 := bstep (se 3 (by rfl) ⟨1554350, by rfl⟩ : syracuseStep 8289869 = 3108701) B3108701
theorem B1212023 : Blo 714321 1212023 := bstep (se 1 (by rfl) ⟨909017, by rfl⟩ : syracuseStep 1212023 = 1818035) B1818035
theorem B2752237 : Blo 714321 2752237 := bstep (se 3 (by rfl) ⟨516044, by rfl⟩ : syracuseStep 2752237 = 1032089) B1032089
theorem B1146683 : Blo 714321 1146683 := bstep (se 1 (by rfl) ⟨860012, by rfl⟩ : syracuseStep 1146683 = 1720025) B1720025
theorem B2719763 : Blo 714321 2719763 := bstep (se 1 (by rfl) ⟨2039822, by rfl⟩ : syracuseStep 2719763 = 4079645) B4079645
theorem B15532195 : Blo 714321 15532195 := bstep (se 1 (by rfl) ⟨11649146, by rfl⟩ : syracuseStep 15532195 = 23298293) B23298293
theorem B9175355 : Blo 714321 9175355 := bstep (se 1 (by rfl) ⟨6881516, by rfl⟩ : syracuseStep 9175355 = 13763033) B13763033
theorem B1147279 : Blo 714321 1147279 := bstep (se 1 (by rfl) ⟨860459, by rfl⟩ : syracuseStep 1147279 = 1720919) B1720919
theorem B18383921 : Blo 714321 18383921 := bstep (se 2 (by rfl) ⟨6893970, by rfl⟩ : syracuseStep 18383921 = 13787941) B13787941
theorem B6980825 : Blo 714321 6980825 := bstep (se 2 (by rfl) ⟨2617809, by rfl⟩ : syracuseStep 6980825 = 5235619) B5235619
theorem B1475833 : Blo 714321 1475833 := bstep (se 2 (by rfl) ⟨553437, by rfl⟩ : syracuseStep 1475833 = 1106875) B1106875
theorem B1607291 : Blo 714321 1607291 := bstep (se 1 (by rfl) ⟨1205468, by rfl⟩ : syracuseStep 1607291 = 2410937) B2410937
theorem B2328203 : Blo 714321 2328203 := bstep (se 1 (by rfl) ⟨1746152, by rfl⟩ : syracuseStep 2328203 = 3492305) B3492305
theorem B1148663 : Blo 714321 1148663 := bstep (se 1 (by rfl) ⟨861497, by rfl⟩ : syracuseStep 1148663 = 1722995) B1722995
theorem B1607417 : Blo 714321 1607417 := bstep (se 2 (by rfl) ⟨602781, by rfl⟩ : syracuseStep 1607417 = 1205563) B1205563
theorem B2623261 : Blo 714321 2623261 := bstep (se 3 (by rfl) ⟨491861, by rfl⟩ : syracuseStep 2623261 = 983723) B983723
theorem B1017775 : Blo 714321 1017775 := bstep (se 1 (by rfl) ⟨763331, by rfl⟩ : syracuseStep 1017775 = 1526663) B1526663
theorem B1607687 : Blo 714321 1607687 := bstep (se 1 (by rfl) ⟨1205765, by rfl⟩ : syracuseStep 1607687 = 2411531) B2411531
theorem B2295827 : Blo 714321 2295827 := bstep (se 1 (by rfl) ⟨1721870, by rfl⟩ : syracuseStep 2295827 = 3443741) B3443741
theorem B30902309 : Blo 714321 30902309 := bstep (se 4 (by rfl) ⟨2897091, by rfl⟩ : syracuseStep 30902309 = 5794183) B5794183
theorem B1607759 : Blo 714321 1607759 := bstep (se 1 (by rfl) ⟨1205819, by rfl⟩ : syracuseStep 1607759 = 2411639) B2411639
theorem B7342169 : Blo 714321 7342169 := bstep (se 2 (by rfl) ⟨2753313, by rfl⟩ : syracuseStep 7342169 = 5506627) B5506627
theorem B1378475 : Blo 714321 1378475 := bstep (se 1 (by rfl) ⟨1033856, by rfl⟩ : syracuseStep 1378475 = 2067713) B2067713
theorem B1149175 : Blo 714321 1149175 := bstep (se 1 (by rfl) ⟨861881, by rfl⟩ : syracuseStep 1149175 = 1723763) B1723763
theorem B6130025 : Blo 714321 6130025 := bstep (se 2 (by rfl) ⟨2298759, by rfl⟩ : syracuseStep 6130025 = 4597519) B4597519
theorem B1608155 : Blo 714321 1608155 := bstep (se 1 (by rfl) ⟨1206116, by rfl⟩ : syracuseStep 1608155 = 2412233) B2412233
theorem B2296505 : Blo 714321 2296505 := bstep (se 2 (by rfl) ⟨861189, by rfl⟩ : syracuseStep 2296505 = 1722379) B1722379
theorem B2722679 : Blo 714321 2722679 := bstep (se 1 (by rfl) ⟨2042009, by rfl⟩ : syracuseStep 2722679 = 4084019) B4084019
theorem B1608623 : Blo 714321 1608623 := bstep (se 1 (by rfl) ⟨1206467, by rfl⟩ : syracuseStep 1608623 = 2412935) B2412935
theorem B5442713 : Blo 714321 5442713 := bstep (se 2 (by rfl) ⟨2041017, by rfl⟩ : syracuseStep 5442713 = 4082035) B4082035
theorem B2034845 : Blo 714321 2034845 := bstep (se 3 (by rfl) ⟨381533, by rfl⟩ : syracuseStep 2034845 = 763067) B763067
theorem B1608875 : Blo 714321 1608875 := bstep (se 1 (by rfl) ⟨1206656, by rfl⟩ : syracuseStep 1608875 = 2413313) B2413313
theorem B1150123 : Blo 714321 1150123 := bstep (se 1 (by rfl) ⟨862592, by rfl⟩ : syracuseStep 1150123 = 1725185) B1725185
theorem B1150303 : Blo 714321 1150303 := bstep (se 1 (by rfl) ⟨862727, by rfl⟩ : syracuseStep 1150303 = 1725455) B1725455
theorem B3968635 : Blo 714321 3968635 := bstep (se 1 (by rfl) ⟨2976476, by rfl⟩ : syracuseStep 3968635 = 5952953) B5952953
theorem B1609415 : Blo 714321 1609415 := bstep (se 1 (by rfl) ⟨1207061, by rfl⟩ : syracuseStep 1609415 = 2414123) B2414123
theorem B2723651 : Blo 714321 2723651 := bstep (se 1 (by rfl) ⟨2042738, by rfl⟩ : syracuseStep 2723651 = 4085477) B4085477
theorem B2035631 : Blo 714321 2035631 := bstep (se 1 (by rfl) ⟨1526723, by rfl⟩ : syracuseStep 2035631 = 3053447) B3053447
theorem B11604131 : Blo 714321 11604131 := bstep (se 1 (by rfl) ⟨8703098, by rfl⟩ : syracuseStep 11604131 = 17406197) B17406197
theorem B5509463 : Blo 714321 5509463 := bstep (se 1 (by rfl) ⟨4132097, by rfl⟩ : syracuseStep 5509463 = 8264195) B8264195
theorem B1610279 : Blo 714321 1610279 := bstep (se 1 (by rfl) ⟨1207709, by rfl⟩ : syracuseStep 1610279 = 2415419) B2415419
theorem B2298503 : Blo 714321 2298503 := bstep (se 1 (by rfl) ⟨1723877, by rfl⟩ : syracuseStep 2298503 = 3447755) B3447755
theorem B9573137 : Blo 714321 9573137 := bstep (se 2 (by rfl) ⟨3589926, by rfl⟩ : syracuseStep 9573137 = 7179853) B7179853
theorem B2724637 : Blo 714321 2724637 := bstep (se 3 (by rfl) ⟨510869, by rfl⟩ : syracuseStep 2724637 = 1021739) B1021739
theorem B27595565 : Blo 714321 27595565 := bstep (se 3 (by rfl) ⟨5174168, by rfl⟩ : syracuseStep 27595565 = 10348337) B10348337
theorem B1610603 : Blo 714321 1610603 := bstep (se 1 (by rfl) ⟨1207952, by rfl⟩ : syracuseStep 1610603 = 2415905) B2415905
theorem B1610657 : Blo 714321 1610657 := bstep (se 2 (by rfl) ⟨603996, by rfl⟩ : syracuseStep 1610657 = 1207993) B1207993
theorem B3445679 : Blo 714321 3445679 := bstep (se 1 (by rfl) ⟨2584259, by rfl⟩ : syracuseStep 3445679 = 5168519) B5168519
theorem B5444657 : Blo 714321 5444657 := bstep (se 2 (by rfl) ⟨2041746, by rfl⟩ : syracuseStep 5444657 = 4083493) B4083493
theorem B2757689 : Blo 714321 2757689 := bstep (se 2 (by rfl) ⟨1034133, by rfl⟩ : syracuseStep 2757689 = 2068267) B2068267
theorem B1610999 : Blo 714321 1610999 := bstep (se 1 (by rfl) ⟨1208249, by rfl⟩ : syracuseStep 1610999 = 2416499) B2416499
theorem B5805701 : Blo 714321 5805701 := bstep (se 4 (by rfl) ⟨544284, by rfl⟩ : syracuseStep 5805701 = 1088569) B1088569
theorem B4069187 : Blo 714321 4069187 := bstep (se 1 (by rfl) ⟨3051890, by rfl⟩ : syracuseStep 4069187 = 6103781) B6103781
theorem B1611593 : Blo 714321 1611593 := bstep (se 2 (by rfl) ⟨604347, by rfl⟩ : syracuseStep 1611593 = 1208695) B1208695
theorem B1808315 : Blo 714321 1808315 := bstep (se 1 (by rfl) ⟨1356236, by rfl⟩ : syracuseStep 1808315 = 2712473) B2712473
theorem B3446873 : Blo 714321 3446873 := bstep (se 2 (by rfl) ⟨1292577, by rfl⟩ : syracuseStep 3446873 = 2585155) B2585155
theorem B4593779 : Blo 714321 4593779 := bstep (se 1 (by rfl) ⟨3445334, by rfl⟩ : syracuseStep 4593779 = 6890669) B6890669
theorem B5871959 : Blo 714321 5871959 := bstep (se 1 (by rfl) ⟨4403969, by rfl⟩ : syracuseStep 5871959 = 8807939) B8807939
theorem B858475 : Blo 714321 858475 := bstep (se 1 (by rfl) ⟨643856, by rfl⟩ : syracuseStep 858475 = 1287713) B1287713
theorem B89332109 : Blo 714321 89332109 := bstep (se 3 (by rfl) ⟨16749770, by rfl⟩ : syracuseStep 89332109 = 33499541) B33499541
theorem B1087919 : Blo 714321 1087919 := bstep (se 1 (by rfl) ⟨815939, by rfl⟩ : syracuseStep 1087919 = 1631879) B1631879
theorem B1808993 : Blo 714321 1808993 := bstep (se 2 (by rfl) ⟨678372, by rfl⟩ : syracuseStep 1808993 = 1356745) B1356745
theorem B1612385 : Blo 714321 1612385 := bstep (se 2 (by rfl) ⟨604644, by rfl⟩ : syracuseStep 1612385 = 1209289) B1209289
theorem B3447431 : Blo 714321 3447431 := bstep (se 1 (by rfl) ⟨2585573, by rfl⟩ : syracuseStep 3447431 = 5171147) B5171147
theorem B1612727 : Blo 714321 1612727 := bstep (se 1 (by rfl) ⟨1209545, by rfl⟩ : syracuseStep 1612727 = 2419091) B2419091
theorem B37264535 : Blo 714321 37264535 := bstep (se 1 (by rfl) ⟨27948401, by rfl⟩ : syracuseStep 37264535 = 55896803) B55896803
theorem B4365515 : Blo 714321 4365515 := bstep (se 1 (by rfl) ⟨3274136, by rfl⟩ : syracuseStep 4365515 = 6548273) B6548273
theorem B1613321 : Blo 714321 1613321 := bstep (se 2 (by rfl) ⟨604995, by rfl⟩ : syracuseStep 1613321 = 1209991) B1209991
theorem B1613663 : Blo 714321 1613663 := bstep (se 1 (by rfl) ⟨1210247, by rfl⟩ : syracuseStep 1613663 = 2420495) B2420495
theorem B4071329 : Blo 714321 4071329 := bstep (se 2 (by rfl) ⟨1526748, by rfl⟩ : syracuseStep 4071329 = 3053497) B3053497
theorem B1810451 : Blo 714321 1810451 := bstep (se 1 (by rfl) ⟨1357838, by rfl⟩ : syracuseStep 1810451 = 2715677) B2715677
theorem B1613843 : Blo 714321 1613843 := bstep (se 1 (by rfl) ⟨1210382, by rfl⟩ : syracuseStep 1613843 = 2420765) B2420765
theorem B1614185 : Blo 714321 1614185 := bstep (se 2 (by rfl) ⟨605319, by rfl⟩ : syracuseStep 1614185 = 1210639) B1210639
theorem B1810907 : Blo 714321 1810907 := bstep (se 1 (by rfl) ⟨1358180, by rfl⟩ : syracuseStep 1810907 = 2716361) B2716361
theorem B1614779 : Blo 714321 1614779 := bstep (se 1 (by rfl) ⟨1211084, by rfl⟩ : syracuseStep 1614779 = 2422169) B2422169
theorem B1614905 : Blo 714321 1614905 := bstep (se 2 (by rfl) ⟨605589, by rfl⟩ : syracuseStep 1614905 = 1211179) B1211179
theorem B4596983 : Blo 714321 4596983 := bstep (se 1 (by rfl) ⟨3447737, by rfl⟩ : syracuseStep 4596983 = 6895475) B6895475
theorem B1615247 : Blo 714321 1615247 := bstep (se 1 (by rfl) ⟨1211435, by rfl⟩ : syracuseStep 1615247 = 2422871) B2422871
theorem B4597211 : Blo 714321 4597211 := bstep (se 1 (by rfl) ⟨3447908, by rfl⟩ : syracuseStep 4597211 = 6895817) B6895817
theorem B1812091 : Blo 714321 1812091 := bstep (se 1 (by rfl) ⟨1359068, by rfl⟩ : syracuseStep 1812091 = 2718137) B2718137
theorem B4073105 : Blo 714321 4073105 := bstep (se 2 (by rfl) ⟨1527414, by rfl⟩ : syracuseStep 4073105 = 3054829) B3054829
theorem B1615571 : Blo 714321 1615571 := bstep (se 1 (by rfl) ⟨1211678, by rfl⟩ : syracuseStep 1615571 = 2423357) B2423357
theorem B4597469 : Blo 714321 4597469 := bstep (se 3 (by rfl) ⟨862025, by rfl⟩ : syracuseStep 4597469 = 1724051) B1724051
theorem B17409887 : Blo 714321 17409887 := bstep (se 1 (by rfl) ⟨13057415, by rfl⟩ : syracuseStep 17409887 = 26114831) B26114831
theorem B23275457 : Blo 714321 23275457 := bstep (se 2 (by rfl) ⟨8728296, by rfl⟩ : syracuseStep 23275457 = 17456593) B17456593
theorem B4073561 : Blo 714321 4073561 := bstep (se 2 (by rfl) ⟨1527585, by rfl⟩ : syracuseStep 4073561 = 3055171) B3055171
theorem B3057821 : Blo 714321 3057821 := bstep (se 3 (by rfl) ⟨573341, by rfl⟩ : syracuseStep 3057821 = 1146683) B1146683
theorem B6203699 : Blo 714321 6203699 := bstep (se 1 (by rfl) ⟨4652774, by rfl⟩ : syracuseStep 6203699 = 9305549) B9305549
theorem B37234997 : Blo 714321 37234997 := bstep (se 5 (by rfl) ⟨1745390, by rfl⟩ : syracuseStep 37234997 = 3490781) B3490781
theorem B18557363 : Blo 714321 18557363 := bstep (se 1 (by rfl) ⟨13918022, by rfl⟩ : syracuseStep 18557363 = 27836045) B27836045
theorem B21179015 : Blo 714321 21179015 := bstep (se 1 (by rfl) ⟨15884261, by rfl⟩ : syracuseStep 21179015 = 31768523) B31768523
theorem B2042567 : Blo 714321 2042567 := bstep (se 1 (by rfl) ⟨1531925, by rfl⟩ : syracuseStep 2042567 = 3063851) B3063851
theorem B3058505 : Blo 714321 3058505 := bstep (se 2 (by rfl) ⟨1146939, by rfl⟩ : syracuseStep 3058505 = 2293879) B2293879
theorem B4598851 : Blo 714321 4598851 := bstep (se 1 (by rfl) ⟨3449138, by rfl⟩ : syracuseStep 4598851 = 6898277) B6898277
theorem B4599443 : Blo 714321 4599443 := bstep (se 1 (by rfl) ⟨3449582, by rfl⟩ : syracuseStep 4599443 = 6899165) B6899165
theorem B766031 : Blo 714321 766031 := bstep (se 1 (by rfl) ⟨574523, by rfl⟩ : syracuseStep 766031 = 1149047) B1149047
theorem B1224875 : Blo 714321 1224875 := bstep (se 1 (by rfl) ⟨918656, by rfl⟩ : syracuseStep 1224875 = 1837313) B1837313
theorem B2044379 : Blo 714321 2044379 := bstep (se 1 (by rfl) ⟨1533284, by rfl⟩ : syracuseStep 2044379 = 3066569) B3066569
theorem B3060433 : Blo 714321 3060433 := bstep (se 2 (by rfl) ⟨1147662, by rfl⟩ : syracuseStep 3060433 = 2295325) B2295325
theorem B5452919 : Blo 714321 5452919 := bstep (se 1 (by rfl) ⟨4089689, by rfl⟩ : syracuseStep 5452919 = 8179379) B8179379
theorem B3617945 : Blo 714321 3617945 := bstep (se 2 (by rfl) ⟨1356729, by rfl⟩ : syracuseStep 3617945 = 2713459) B2713459
theorem B1357049 : Blo 714321 1357049 := bstep (se 2 (by rfl) ⟨508893, by rfl⟩ : syracuseStep 1357049 = 1017787) B1017787
theorem B1357231 : Blo 714321 1357231 := bstep (se 1 (by rfl) ⟨1017923, by rfl⟩ : syracuseStep 1357231 = 2035847) B2035847
theorem B1357391 : Blo 714321 1357391 := bstep (se 1 (by rfl) ⟨1018043, by rfl⟩ : syracuseStep 1357391 = 2036087) B2036087
theorem B6895201 : Blo 714321 6895201 := bstep (se 2 (by rfl) ⟨2585700, by rfl⟩ : syracuseStep 6895201 = 5171401) B5171401
theorem B2176723 : Blo 714321 2176723 := bstep (se 1 (by rfl) ⟨1632542, by rfl⟩ : syracuseStep 2176723 = 3265085) B3265085
theorem B1718111 : Blo 714321 1718111 := bstep (se 1 (by rfl) ⟨1288583, by rfl⟩ : syracuseStep 1718111 = 2577167) B2577167
theorem B1816415 : Blo 714321 1816415 := bstep (se 1 (by rfl) ⟨1362311, by rfl⟩ : syracuseStep 1816415 = 2724623) B2724623
theorem B1456015 : Blo 714321 1456015 := bstep (se 1 (by rfl) ⟨1092011, by rfl⟩ : syracuseStep 1456015 = 2184023) B2184023
theorem B5519441 : Blo 714321 5519441 := bstep (se 2 (by rfl) ⟨2069790, by rfl⟩ : syracuseStep 5519441 = 4139581) B4139581
theorem B15480989 : Blo 714321 15480989 := bstep (se 3 (by rfl) ⟨2902685, by rfl⟩ : syracuseStep 15480989 = 5805371) B5805371
theorem B2177405 : Blo 714321 2177405 := bstep (se 3 (by rfl) ⟨408263, by rfl⟩ : syracuseStep 2177405 = 816527) B816527
theorem B1817113 : Blo 714321 1817113 := bstep (se 2 (by rfl) ⟨681417, by rfl⟩ : syracuseStep 1817113 = 1362835) B1362835
theorem B1358507 : Blo 714321 1358507 := bstep (se 1 (by rfl) ⟨1018880, by rfl⟩ : syracuseStep 1358507 = 2037761) B2037761
theorem B11057849 : Blo 714321 11057849 := bstep (se 2 (by rfl) ⟨4146693, by rfl⟩ : syracuseStep 11057849 = 8293387) B8293387
theorem B1817417 : Blo 714321 1817417 := bstep (se 2 (by rfl) ⟨681531, by rfl⟩ : syracuseStep 1817417 = 1363063) B1363063
theorem B156941171 : Blo 714321 156941171 := bstep (se 1 (by rfl) ⟨117705878, by rfl⟩ : syracuseStep 156941171 = 235411757) B235411757
theorem B5979793 : Blo 714321 5979793 := bstep (se 2 (by rfl) ⟨2242422, by rfl⟩ : syracuseStep 5979793 = 4484845) B4484845
theorem B8142929 : Blo 714321 8142929 := bstep (se 2 (by rfl) ⟨3053598, by rfl⟩ : syracuseStep 8142929 = 6107197) B6107197
theorem B1360223 : Blo 714321 1360223 := bstep (se 1 (by rfl) ⟨1020167, by rfl⟩ : syracuseStep 1360223 = 2040335) B2040335
theorem B6209921 : Blo 714321 6209921 := bstep (se 2 (by rfl) ⟨2328720, by rfl⟩ : syracuseStep 6209921 = 4657441) B4657441
theorem B3064193 : Blo 714321 3064193 := bstep (se 2 (by rfl) ⟨1149072, by rfl⟩ : syracuseStep 3064193 = 2298145) B2298145
theorem B967087 : Blo 714321 967087 := bstep (se 1 (by rfl) ⟨725315, by rfl⟩ : syracuseStep 967087 = 1450631) B1450631
theorem B1360633 : Blo 714321 1360633 := bstep (se 2 (by rfl) ⟨510237, by rfl⟩ : syracuseStep 1360633 = 1020475) B1020475
theorem B17384395 : Blo 714321 17384395 := bstep (se 1 (by rfl) ⟨13038296, by rfl⟩ : syracuseStep 17384395 = 26076593) B26076593
theorem B803803 : Blo 714321 803803 := bstep (se 1 (by rfl) ⟨602852, by rfl⟩ : syracuseStep 803803 = 1205705) B1205705
theorem B1164251 : Blo 714321 1164251 := bstep (se 1 (by rfl) ⟨873188, by rfl⟩ : syracuseStep 1164251 = 1746377) B1746377
theorem B9290771 : Blo 714321 9290771 := bstep (se 1 (by rfl) ⟨6968078, by rfl⟩ : syracuseStep 9290771 = 13936157) B13936157
theorem B6865985 : Blo 714321 6865985 := bstep (se 2 (by rfl) ⟨2574744, by rfl⟩ : syracuseStep 6865985 = 5149489) B5149489
theorem B1360975 : Blo 714321 1360975 := bstep (se 1 (by rfl) ⟨1020731, by rfl⟩ : syracuseStep 1360975 = 2041463) B2041463
theorem B1721591 : Blo 714321 1721591 := bstep (se 1 (by rfl) ⟨1291193, by rfl⟩ : syracuseStep 1721591 = 2582387) B2582387
theorem B1361225 : Blo 714321 1361225 := bstep (se 2 (by rfl) ⟨510459, by rfl⟩ : syracuseStep 1361225 = 1020919) B1020919
theorem B804271 : Blo 714321 804271 := bstep (se 1 (by rfl) ⟨603203, by rfl⟩ : syracuseStep 804271 = 1206407) B1206407
theorem B804703 : Blo 714321 804703 := bstep (se 1 (by rfl) ⟨603527, by rfl⟩ : syracuseStep 804703 = 1207055) B1207055
theorem B5163097 : Blo 714321 5163097 := bstep (se 2 (by rfl) ⟨1936161, by rfl⟩ : syracuseStep 5163097 = 3872323) B3872323
theorem B1362091 : Blo 714321 1362091 := bstep (se 1 (by rfl) ⟨1021568, by rfl⟩ : syracuseStep 1362091 = 2043137) B2043137
theorem B805063 : Blo 714321 805063 := bstep (se 1 (by rfl) ⟨603797, by rfl⟩ : syracuseStep 805063 = 1207595) B1207595
theorem B1362167 : Blo 714321 1362167 := bstep (se 1 (by rfl) ⟨1021625, by rfl⟩ : syracuseStep 1362167 = 2043251) B2043251
theorem B8177921 : Blo 714321 8177921 := bstep (se 2 (by rfl) ⟨3066720, by rfl⟩ : syracuseStep 8177921 = 6133441) B6133441
theorem B2902283 : Blo 714321 2902283 := bstep (se 1 (by rfl) ⟨2176712, by rfl⟩ : syracuseStep 2902283 = 4353425) B4353425
theorem B1165673 : Blo 714321 1165673 := bstep (se 2 (by rfl) ⟨437127, by rfl⟩ : syracuseStep 1165673 = 874255) B874255
theorem B1362395 : Blo 714321 1362395 := bstep (se 1 (by rfl) ⟨1021796, by rfl⟩ : syracuseStep 1362395 = 2043593) B2043593
theorem B2411207 : Blo 714321 2411207 := bstep (se 1 (by rfl) ⟨1808405, by rfl⟩ : syracuseStep 2411207 = 3616811) B3616811
theorem B3066653 : Blo 714321 3066653 := bstep (se 3 (by rfl) ⟨574997, by rfl⟩ : syracuseStep 3066653 = 1149995) B1149995
theorem B805927 : Blo 714321 805927 := bstep (se 1 (by rfl) ⟨604445, by rfl⟩ : syracuseStep 805927 = 1208891) B1208891
theorem B5426675 : Blo 714321 5426675 := bstep (se 1 (by rfl) ⟨4070006, by rfl⟩ : syracuseStep 5426675 = 8140013) B8140013
theorem B2412071 : Blo 714321 2412071 := bstep (se 1 (by rfl) ⟨1809053, by rfl⟩ : syracuseStep 2412071 = 3618107) B3618107
theorem B48385637 : Blo 714321 48385637 := bstep (se 4 (by rfl) ⟨4536153, by rfl⟩ : syracuseStep 48385637 = 9072307) B9072307
theorem B3624587 : Blo 714321 3624587 := bstep (se 1 (by rfl) ⟨2718440, by rfl⟩ : syracuseStep 3624587 = 5436881) B5436881
theorem B2412179 : Blo 714321 2412179 := bstep (se 1 (by rfl) ⟨1809134, by rfl⟩ : syracuseStep 2412179 = 3618269) B3618269
theorem B1363655 : Blo 714321 1363655 := bstep (se 1 (by rfl) ⟨1022741, by rfl⟩ : syracuseStep 1363655 = 2045483) B2045483
theorem B970601 : Blo 714321 970601 := bstep (se 2 (by rfl) ⟨363975, by rfl⟩ : syracuseStep 970601 = 727951) B727951
theorem B2412395 : Blo 714321 2412395 := bstep (se 1 (by rfl) ⟨1809296, by rfl⟩ : syracuseStep 2412395 = 3618593) B3618593
theorem B2412449 : Blo 714321 2412449 := bstep (se 2 (by rfl) ⟨904668, by rfl⟩ : syracuseStep 2412449 = 1809337) B1809337
theorem B1527979 : Blo 714321 1527979 := bstep (se 1 (by rfl) ⟨1145984, by rfl⟩ : syracuseStep 1527979 = 2291969) B2291969
theorem B22106317 : Blo 714321 22106317 := bstep (se 3 (by rfl) ⟨4144934, by rfl⟩ : syracuseStep 22106317 = 8289869) B8289869
theorem B2576765 : Blo 714321 2576765 := bstep (se 3 (by rfl) ⟨483143, by rfl⟩ : syracuseStep 2576765 = 966287) B966287
theorem B2413043 : Blo 714321 2413043 := bstep (se 1 (by rfl) ⟨1809782, by rfl⟩ : syracuseStep 2413043 = 3619565) B3619565
theorem B807547 : Blo 714321 807547 := bstep (se 1 (by rfl) ⟨605660, by rfl⟩ : syracuseStep 807547 = 1211321) B1211321
theorem B906167 : Blo 714321 906167 := bstep (se 1 (by rfl) ⟨679625, by rfl⟩ : syracuseStep 906167 = 1359251) B1359251
theorem B5297125 : Blo 714321 5297125 := bstep (se 4 (by rfl) ⟨496605, by rfl⟩ : syracuseStep 5297125 = 993211) B993211
theorem B2413583 : Blo 714321 2413583 := bstep (se 1 (by rfl) ⟨1810187, by rfl⟩ : syracuseStep 2413583 = 3620375) B3620375
theorem B906319 : Blo 714321 906319 := bstep (se 1 (by rfl) ⟨679739, by rfl⟩ : syracuseStep 906319 = 1359479) B1359479
theorem B808015 : Blo 714321 808015 := bstep (se 1 (by rfl) ⟨606011, by rfl⟩ : syracuseStep 808015 = 1212023) B1212023
theorem B2446793 : Blo 714321 2446793 := bstep (se 2 (by rfl) ⟨917547, by rfl⟩ : syracuseStep 2446793 = 1835095) B1835095
theorem B1103323 : Blo 714321 1103323 := bstep (se 1 (by rfl) ⟨827492, by rfl⟩ : syracuseStep 1103323 = 1654985) B1654985
theorem B2414177 : Blo 714321 2414177 := bstep (se 2 (by rfl) ⟨905316, by rfl⟩ : syracuseStep 2414177 = 1810633) B1810633
theorem B2905739 : Blo 714321 2905739 := bstep (se 1 (by rfl) ⟨2179304, by rfl⟩ : syracuseStep 2905739 = 4358609) B4358609
theorem B3266399 : Blo 714321 3266399 := bstep (se 1 (by rfl) ⟨2449799, by rfl⟩ : syracuseStep 3266399 = 4899599) B4899599
theorem B6117281 : Blo 714321 6117281 := bstep (se 2 (by rfl) ⟨2293980, by rfl⟩ : syracuseStep 6117281 = 4587961) B4587961
theorem B1529875 : Blo 714321 1529875 := bstep (se 1 (by rfl) ⟨1147406, by rfl⟩ : syracuseStep 1529875 = 2294813) B2294813
theorem B907463 : Blo 714321 907463 := bstep (se 1 (by rfl) ⟨680597, by rfl⟩ : syracuseStep 907463 = 1361195) B1361195
theorem B5429591 : Blo 714321 5429591 := bstep (se 1 (by rfl) ⟨4072193, by rfl⟩ : syracuseStep 5429591 = 8144387) B8144387
theorem B907615 : Blo 714321 907615 := bstep (se 1 (by rfl) ⟨680711, by rfl⟩ : syracuseStep 907615 = 1361423) B1361423
theorem B5167597 : Blo 714321 5167597 := bstep (se 3 (by rfl) ⟨968924, by rfl⟩ : syracuseStep 5167597 = 1937849) B1937849
theorem B1071695 : Blo 714321 1071695 := bstep (se 1 (by rfl) ⟨803771, by rfl⟩ : syracuseStep 1071695 = 1607543) B1607543
theorem B1071815 : Blo 714321 1071815 := bstep (se 1 (by rfl) ⟨803861, by rfl⟩ : syracuseStep 1071815 = 1607723) B1607723
theorem B1071977 : Blo 714321 1071977 := bstep (se 2 (by rfl) ⟨401991, by rfl⟩ : syracuseStep 1071977 = 803983) B803983
theorem B1072055 : Blo 714321 1072055 := bstep (se 1 (by rfl) ⟨804041, by rfl⟩ : syracuseStep 1072055 = 1608083) B1608083
theorem B1072091 : Blo 714321 1072091 := bstep (se 1 (by rfl) ⟨804068, by rfl⟩ : syracuseStep 1072091 = 1608137) B1608137
theorem B2415635 : Blo 714321 2415635 := bstep (se 1 (by rfl) ⟨1811726, by rfl⟩ : syracuseStep 2415635 = 3623453) B3623453
theorem B6118679 : Blo 714321 6118679 := bstep (se 1 (by rfl) ⟨4589009, by rfl⟩ : syracuseStep 6118679 = 9178019) B9178019
theorem B2415959 : Blo 714321 2415959 := bstep (se 1 (by rfl) ⟨1811969, by rfl⟩ : syracuseStep 2415959 = 3623939) B3623939
theorem B1072559 : Blo 714321 1072559 := bstep (se 1 (by rfl) ⟨804419, by rfl⟩ : syracuseStep 1072559 = 1608839) B1608839
theorem B1072649 : Blo 714321 1072649 := bstep (se 2 (by rfl) ⟨402243, by rfl⟩ : syracuseStep 1072649 = 804487) B804487
theorem B1072679 : Blo 714321 1072679 := bstep (se 1 (by rfl) ⟨804509, by rfl⟩ : syracuseStep 1072679 = 1609019) B1609019
theorem B1072763 : Blo 714321 1072763 := bstep (se 1 (by rfl) ⟨804572, by rfl⟩ : syracuseStep 1072763 = 1609145) B1609145
theorem B1072889 : Blo 714321 1072889 := bstep (se 2 (by rfl) ⟨402333, by rfl⟩ : syracuseStep 1072889 = 804667) B804667
theorem B5824315 : Blo 714321 5824315 := bstep (se 1 (by rfl) ⟨4368236, by rfl⟩ : syracuseStep 5824315 = 8736473) B8736473
theorem B1072991 : Blo 714321 1072991 := bstep (se 1 (by rfl) ⟨804743, by rfl⟩ : syracuseStep 1072991 = 1609487) B1609487
theorem B1073003 : Blo 714321 1073003 := bstep (se 1 (by rfl) ⟨804752, by rfl⟩ : syracuseStep 1073003 = 1609505) B1609505
theorem B3628961 : Blo 714321 3628961 := bstep (se 2 (by rfl) ⟨1360860, by rfl⟩ : syracuseStep 3628961 = 2721721) B2721721
theorem B1073231 : Blo 714321 1073231 := bstep (se 1 (by rfl) ⟨804923, by rfl⟩ : syracuseStep 1073231 = 1609847) B1609847
theorem B1073351 : Blo 714321 1073351 := bstep (se 1 (by rfl) ⟨805013, by rfl⟩ : syracuseStep 1073351 = 1610027) B1610027
theorem B1073513 : Blo 714321 1073513 := bstep (se 2 (by rfl) ⟨402567, by rfl⟩ : syracuseStep 1073513 = 805135) B805135
theorem B2417039 : Blo 714321 2417039 := bstep (se 1 (by rfl) ⟨1812779, by rfl⟩ : syracuseStep 2417039 = 3625559) B3625559
theorem B1073591 : Blo 714321 1073591 := bstep (se 1 (by rfl) ⟨805193, by rfl⟩ : syracuseStep 1073591 = 1610387) B1610387
theorem B1073627 : Blo 714321 1073627 := bstep (se 1 (by rfl) ⟨805220, by rfl⟩ : syracuseStep 1073627 = 1610441) B1610441
theorem B2712275 : Blo 714321 2712275 := bstep (se 1 (by rfl) ⟨2034206, by rfl⟩ : syracuseStep 2712275 = 4068413) B4068413
theorem B2417363 : Blo 714321 2417363 := bstep (se 1 (by rfl) ⟨1813022, by rfl⟩ : syracuseStep 2417363 = 3626045) B3626045
theorem B23847641 : Blo 714321 23847641 := bstep (se 2 (by rfl) ⟨8942865, by rfl⟩ : syracuseStep 23847641 = 17885731) B17885731
theorem B2941763 : Blo 714321 2941763 := bstep (se 1 (by rfl) ⟨2206322, by rfl⟩ : syracuseStep 2941763 = 4412645) B4412645
theorem B1074095 : Blo 714321 1074095 := bstep (se 1 (by rfl) ⟨805571, by rfl⟩ : syracuseStep 1074095 = 1611143) B1611143
theorem B1074185 : Blo 714321 1074185 := bstep (se 2 (by rfl) ⟨402819, by rfl⟩ : syracuseStep 1074185 = 805639) B805639
theorem B1074215 : Blo 714321 1074215 := bstep (se 1 (by rfl) ⟨805661, by rfl⟩ : syracuseStep 1074215 = 1611323) B1611323
theorem B1074299 : Blo 714321 1074299 := bstep (se 1 (by rfl) ⟨805724, by rfl⟩ : syracuseStep 1074299 = 1611449) B1611449
theorem B1074425 : Blo 714321 1074425 := bstep (se 2 (by rfl) ⟨402909, by rfl⟩ : syracuseStep 1074425 = 805819) B805819
theorem B1074527 : Blo 714321 1074527 := bstep (se 1 (by rfl) ⟨805895, by rfl⟩ : syracuseStep 1074527 = 1611791) B1611791
theorem B1074539 : Blo 714321 1074539 := bstep (se 1 (by rfl) ⟨805904, by rfl⟩ : syracuseStep 1074539 = 1611809) B1611809
theorem B11167139 : Blo 714321 11167139 := bstep (se 1 (by rfl) ⟨8375354, by rfl⟩ : syracuseStep 11167139 = 16750709) B16750709
theorem B1074767 : Blo 714321 1074767 := bstep (se 1 (by rfl) ⟨806075, by rfl⟩ : syracuseStep 1074767 = 1612151) B1612151
theorem B714335 : Blo 714321 714335 := bstep (se 1 (by rfl) ⟨535751, by rfl⟩ : syracuseStep 714335 = 1071503) B1071503
theorem B2582113 : Blo 714321 2582113 := bstep (se 2 (by rfl) ⟨968292, by rfl⟩ : syracuseStep 2582113 = 1936585) B1936585
theorem B714363 : Blo 714321 714363 := bstep (se 1 (by rfl) ⟨535772, by rfl⟩ : syracuseStep 714363 = 1071545) B1071545
theorem B714415 : Blo 714321 714415 := bstep (se 1 (by rfl) ⟨535811, by rfl⟩ : syracuseStep 714415 = 1071623) B1071623
theorem B2713277 : Blo 714321 2713277 := bstep (se 3 (by rfl) ⟨508739, by rfl⟩ : syracuseStep 2713277 = 1017479) B1017479
theorem B714439 : Blo 714321 714439 := bstep (se 1 (by rfl) ⟨535829, by rfl⟩ : syracuseStep 714439 = 1071659) B1071659
theorem B1074887 : Blo 714321 1074887 := bstep (se 1 (by rfl) ⟨806165, by rfl⟩ : syracuseStep 1074887 = 1612331) B1612331
theorem B714459 : Blo 714321 714459 := bstep (se 1 (by rfl) ⟨535844, by rfl⟩ : syracuseStep 714459 = 1071689) B1071689
theorem B5793569 : Blo 714321 5793569 := bstep (se 2 (by rfl) ⟨2172588, by rfl⟩ : syracuseStep 5793569 = 4345177) B4345177
theorem B714535 : Blo 714321 714535 := bstep (se 1 (by rfl) ⟨535901, by rfl⟩ : syracuseStep 714535 = 1071803) B1071803
theorem B714575 : Blo 714321 714575 := bstep (se 1 (by rfl) ⟨535931, by rfl⟩ : syracuseStep 714575 = 1071863) B1071863
theorem B714591 : Blo 714321 714591 := bstep (se 1 (by rfl) ⟨535943, by rfl⟩ : syracuseStep 714591 = 1071887) B1071887
theorem B1075049 : Blo 714321 1075049 := bstep (se 2 (by rfl) ⟨403143, by rfl⟩ : syracuseStep 1075049 = 806287) B806287
theorem B2418551 : Blo 714321 2418551 := bstep (se 1 (by rfl) ⟨1813913, by rfl⟩ : syracuseStep 2418551 = 3627827) B3627827
theorem B714619 : Blo 714321 714619 := bstep (se 1 (by rfl) ⟨535964, by rfl⟩ : syracuseStep 714619 = 1071929) B1071929
theorem B714671 : Blo 714321 714671 := bstep (se 1 (by rfl) ⟨536003, by rfl⟩ : syracuseStep 714671 = 1072007) B1072007
theorem B1206191 : Blo 714321 1206191 := bstep (se 1 (by rfl) ⟨904643, by rfl⟩ : syracuseStep 1206191 = 1809287) B1809287
theorem B1075127 : Blo 714321 1075127 := bstep (se 1 (by rfl) ⟨806345, by rfl⟩ : syracuseStep 1075127 = 1612691) B1612691
theorem B714695 : Blo 714321 714695 := bstep (se 1 (by rfl) ⟨536021, by rfl⟩ : syracuseStep 714695 = 1072043) B1072043
theorem B714715 : Blo 714321 714715 := bstep (se 1 (by rfl) ⟨536036, by rfl⟩ : syracuseStep 714715 = 1072073) B1072073
theorem B1075163 : Blo 714321 1075163 := bstep (se 1 (by rfl) ⟨806372, by rfl⟩ : syracuseStep 1075163 = 1612745) B1612745
theorem B714791 : Blo 714321 714791 := bstep (se 1 (by rfl) ⟨536093, by rfl⟩ : syracuseStep 714791 = 1072187) B1072187
theorem B714831 : Blo 714321 714831 := bstep (se 1 (by rfl) ⟨536123, by rfl⟩ : syracuseStep 714831 = 1072247) B1072247
theorem B2418767 : Blo 714321 2418767 := bstep (se 1 (by rfl) ⟨1814075, by rfl⟩ : syracuseStep 2418767 = 3628151) B3628151
theorem B714847 : Blo 714321 714847 := bstep (se 1 (by rfl) ⟨536135, by rfl⟩ : syracuseStep 714847 = 1072271) B1072271
theorem B9168997 : Blo 714321 9168997 := bstep (se 4 (by rfl) ⟨859593, by rfl⟩ : syracuseStep 9168997 = 1719187) B1719187
theorem B714875 : Blo 714321 714875 := bstep (se 1 (by rfl) ⟨536156, by rfl⟩ : syracuseStep 714875 = 1072313) B1072313
theorem B26142851 : Blo 714321 26142851 := bstep (se 1 (by rfl) ⟨19607138, by rfl⟩ : syracuseStep 26142851 = 39214277) B39214277
theorem B714927 : Blo 714321 714927 := bstep (se 1 (by rfl) ⟨536195, by rfl⟩ : syracuseStep 714927 = 1072391) B1072391
theorem B714951 : Blo 714321 714951 := bstep (se 1 (by rfl) ⟨536213, by rfl⟩ : syracuseStep 714951 = 1072427) B1072427
theorem B41216201 : Blo 714321 41216201 := bstep (se 2 (by rfl) ⟨15456075, by rfl⟩ : syracuseStep 41216201 = 30912151) B30912151
theorem B714971 : Blo 714321 714971 := bstep (se 1 (by rfl) ⟨536228, by rfl⟩ : syracuseStep 714971 = 1072457) B1072457
theorem B715047 : Blo 714321 715047 := bstep (se 1 (by rfl) ⟨536285, by rfl⟩ : syracuseStep 715047 = 1072571) B1072571
theorem B4581683 : Blo 714321 4581683 := bstep (se 1 (by rfl) ⟨3436262, by rfl⟩ : syracuseStep 4581683 = 6872525) B6872525
theorem B715087 : Blo 714321 715087 := bstep (se 1 (by rfl) ⟨536315, by rfl⟩ : syracuseStep 715087 = 1072631) B1072631
theorem B1206623 : Blo 714321 1206623 := bstep (se 1 (by rfl) ⟨904967, by rfl⟩ : syracuseStep 1206623 = 1809935) B1809935
theorem B715103 : Blo 714321 715103 := bstep (se 1 (by rfl) ⟨536327, by rfl⟩ : syracuseStep 715103 = 1072655) B1072655
theorem B715131 : Blo 714321 715131 := bstep (se 1 (by rfl) ⟨536348, by rfl⟩ : syracuseStep 715131 = 1072697) B1072697
theorem B715183 : Blo 714321 715183 := bstep (se 1 (by rfl) ⟨536387, by rfl⟩ : syracuseStep 715183 = 1072775) B1072775
theorem B1075631 : Blo 714321 1075631 := bstep (se 1 (by rfl) ⟨806723, by rfl⟩ : syracuseStep 1075631 = 1613447) B1613447
theorem B1239479 : Blo 714321 1239479 := bstep (se 1 (by rfl) ⟨929609, by rfl⟩ : syracuseStep 1239479 = 1859219) B1859219
theorem B715207 : Blo 714321 715207 := bstep (se 1 (by rfl) ⟨536405, by rfl⟩ : syracuseStep 715207 = 1072811) B1072811
theorem B2615753 : Blo 714321 2615753 := bstep (se 2 (by rfl) ⟨980907, by rfl⟩ : syracuseStep 2615753 = 1961815) B1961815
theorem B2419145 : Blo 714321 2419145 := bstep (se 2 (by rfl) ⟨907179, by rfl⟩ : syracuseStep 2419145 = 1814359) B1814359
theorem B715227 : Blo 714321 715227 := bstep (se 1 (by rfl) ⟨536420, by rfl⟩ : syracuseStep 715227 = 1072841) B1072841
theorem B2583049 : Blo 714321 2583049 := bstep (se 2 (by rfl) ⟨968643, by rfl⟩ : syracuseStep 2583049 = 1937287) B1937287
theorem B1075721 : Blo 714321 1075721 := bstep (se 2 (by rfl) ⟨403395, by rfl⟩ : syracuseStep 1075721 = 806791) B806791
theorem B715303 : Blo 714321 715303 := bstep (se 1 (by rfl) ⟨536477, by rfl⟩ : syracuseStep 715303 = 1072955) B1072955
theorem B1075751 : Blo 714321 1075751 := bstep (se 1 (by rfl) ⟨806813, by rfl⟩ : syracuseStep 1075751 = 1613627) B1613627
theorem B715343 : Blo 714321 715343 := bstep (se 1 (by rfl) ⟨536507, by rfl⟩ : syracuseStep 715343 = 1073015) B1073015
theorem B715359 : Blo 714321 715359 := bstep (se 1 (by rfl) ⟨536519, by rfl⟩ : syracuseStep 715359 = 1073039) B1073039
theorem B715387 : Blo 714321 715387 := bstep (se 1 (by rfl) ⟨536540, by rfl⟩ : syracuseStep 715387 = 1073081) B1073081
theorem B1075835 : Blo 714321 1075835 := bstep (se 1 (by rfl) ⟨806876, by rfl⟩ : syracuseStep 1075835 = 1613753) B1613753
theorem B715439 : Blo 714321 715439 := bstep (se 1 (by rfl) ⟨536579, by rfl⟩ : syracuseStep 715439 = 1073159) B1073159
theorem B715463 : Blo 714321 715463 := bstep (se 1 (by rfl) ⟨536597, by rfl⟩ : syracuseStep 715463 = 1073195) B1073195
theorem B4352723 : Blo 714321 4352723 := bstep (se 1 (by rfl) ⟨3264542, by rfl⟩ : syracuseStep 4352723 = 6529085) B6529085
theorem B2419415 : Blo 714321 2419415 := bstep (se 1 (by rfl) ⟨1814561, by rfl⟩ : syracuseStep 2419415 = 3629123) B3629123
theorem B715483 : Blo 714321 715483 := bstep (se 1 (by rfl) ⟨536612, by rfl⟩ : syracuseStep 715483 = 1073225) B1073225
theorem B1075961 : Blo 714321 1075961 := bstep (se 2 (by rfl) ⟨403485, by rfl⟩ : syracuseStep 1075961 = 806971) B806971
theorem B715559 : Blo 714321 715559 := bstep (se 1 (by rfl) ⟨536669, by rfl⟩ : syracuseStep 715559 = 1073339) B1073339
theorem B715599 : Blo 714321 715599 := bstep (se 1 (by rfl) ⟨536699, by rfl⟩ : syracuseStep 715599 = 1073399) B1073399
theorem B715615 : Blo 714321 715615 := bstep (se 1 (by rfl) ⟨536711, by rfl⟩ : syracuseStep 715615 = 1073423) B1073423
theorem B1076063 : Blo 714321 1076063 := bstep (se 1 (by rfl) ⟨807047, by rfl⟩ : syracuseStep 1076063 = 1614095) B1614095
theorem B1076075 : Blo 714321 1076075 := bstep (se 1 (by rfl) ⟨807056, by rfl⟩ : syracuseStep 1076075 = 1614113) B1614113
theorem B715643 : Blo 714321 715643 := bstep (se 1 (by rfl) ⟨536732, by rfl⟩ : syracuseStep 715643 = 1073465) B1073465
theorem B1207183 : Blo 714321 1207183 := bstep (se 1 (by rfl) ⟨905387, by rfl⟩ : syracuseStep 1207183 = 1810775) B1810775
theorem B715695 : Blo 714321 715695 := bstep (se 1 (by rfl) ⟨536771, by rfl⟩ : syracuseStep 715695 = 1073543) B1073543
theorem B2419631 : Blo 714321 2419631 := bstep (se 1 (by rfl) ⟨1814723, by rfl⟩ : syracuseStep 2419631 = 3629447) B3629447
theorem B715719 : Blo 714321 715719 := bstep (se 1 (by rfl) ⟨536789, by rfl⟩ : syracuseStep 715719 = 1073579) B1073579
theorem B715739 : Blo 714321 715739 := bstep (se 1 (by rfl) ⟨536804, by rfl⟩ : syracuseStep 715739 = 1073609) B1073609
theorem B715815 : Blo 714321 715815 := bstep (se 1 (by rfl) ⟨536861, by rfl⟩ : syracuseStep 715815 = 1073723) B1073723
theorem B715855 : Blo 714321 715855 := bstep (se 1 (by rfl) ⟨536891, by rfl⟩ : syracuseStep 715855 = 1073783) B1073783
theorem B1076303 : Blo 714321 1076303 := bstep (se 1 (by rfl) ⟨807227, by rfl⟩ : syracuseStep 1076303 = 1614455) B1614455
theorem B2714705 : Blo 714321 2714705 := bstep (se 2 (by rfl) ⟨1018014, by rfl⟩ : syracuseStep 2714705 = 2036029) B2036029
theorem B715871 : Blo 714321 715871 := bstep (se 1 (by rfl) ⟨536903, by rfl⟩ : syracuseStep 715871 = 1073807) B1073807
theorem B715899 : Blo 714321 715899 := bstep (se 1 (by rfl) ⟨536924, by rfl⟩ : syracuseStep 715899 = 1073849) B1073849
theorem B715951 : Blo 714321 715951 := bstep (se 1 (by rfl) ⟨536963, by rfl⟩ : syracuseStep 715951 = 1073927) B1073927
theorem B715975 : Blo 714321 715975 := bstep (se 1 (by rfl) ⟨536981, by rfl⟩ : syracuseStep 715975 = 1073963) B1073963
theorem B1076423 : Blo 714321 1076423 := bstep (se 1 (by rfl) ⟨807317, by rfl⟩ : syracuseStep 1076423 = 1614635) B1614635
theorem B715995 : Blo 714321 715995 := bstep (se 1 (by rfl) ⟨536996, by rfl⟩ : syracuseStep 715995 = 1073993) B1073993
theorem B716071 : Blo 714321 716071 := bstep (se 1 (by rfl) ⟨537053, by rfl⟩ : syracuseStep 716071 = 1074107) B1074107
theorem B716111 : Blo 714321 716111 := bstep (se 1 (by rfl) ⟨537083, by rfl⟩ : syracuseStep 716111 = 1074167) B1074167
theorem B716127 : Blo 714321 716127 := bstep (se 1 (by rfl) ⟨537095, by rfl⟩ : syracuseStep 716127 = 1074191) B1074191
theorem B1076585 : Blo 714321 1076585 := bstep (se 2 (by rfl) ⟨403719, by rfl⟩ : syracuseStep 1076585 = 807439) B807439
theorem B716155 : Blo 714321 716155 := bstep (se 1 (by rfl) ⟨537116, by rfl⟩ : syracuseStep 716155 = 1074233) B1074233
theorem B716207 : Blo 714321 716207 := bstep (se 1 (by rfl) ⟨537155, by rfl⟩ : syracuseStep 716207 = 1074311) B1074311
theorem B1076663 : Blo 714321 1076663 := bstep (se 1 (by rfl) ⟨807497, by rfl⟩ : syracuseStep 1076663 = 1614995) B1614995
theorem B716231 : Blo 714321 716231 := bstep (se 1 (by rfl) ⟨537173, by rfl⟩ : syracuseStep 716231 = 1074347) B1074347
theorem B716251 : Blo 714321 716251 := bstep (se 1 (by rfl) ⟨537188, by rfl⟩ : syracuseStep 716251 = 1074377) B1074377
theorem B1076699 : Blo 714321 1076699 := bstep (se 1 (by rfl) ⟨807524, by rfl⟩ : syracuseStep 1076699 = 1615049) B1615049
theorem B716327 : Blo 714321 716327 := bstep (se 1 (by rfl) ⟨537245, by rfl⟩ : syracuseStep 716327 = 1074491) B1074491
theorem B1207865 : Blo 714321 1207865 := bstep (se 2 (by rfl) ⟨452949, by rfl⟩ : syracuseStep 1207865 = 905899) B905899
theorem B716367 : Blo 714321 716367 := bstep (se 1 (by rfl) ⟨537275, by rfl⟩ : syracuseStep 716367 = 1074551) B1074551
theorem B716383 : Blo 714321 716383 := bstep (se 1 (by rfl) ⟨537287, by rfl⟩ : syracuseStep 716383 = 1074575) B1074575
theorem B716411 : Blo 714321 716411 := bstep (se 1 (by rfl) ⟨537308, by rfl⟩ : syracuseStep 716411 = 1074617) B1074617
theorem B716463 : Blo 714321 716463 := bstep (se 1 (by rfl) ⟨537347, by rfl⟩ : syracuseStep 716463 = 1074695) B1074695
theorem B716487 : Blo 714321 716487 := bstep (se 1 (by rfl) ⟨537365, by rfl⟩ : syracuseStep 716487 = 1074731) B1074731
theorem B1634003 : Blo 714321 1634003 := bstep (se 1 (by rfl) ⟨1225502, by rfl⟩ : syracuseStep 1634003 = 2451005) B2451005
theorem B716507 : Blo 714321 716507 := bstep (se 1 (by rfl) ⟨537380, by rfl⟩ : syracuseStep 716507 = 1074761) B1074761
theorem B716583 : Blo 714321 716583 := bstep (se 1 (by rfl) ⟨537437, by rfl⟩ : syracuseStep 716583 = 1074875) B1074875
theorem B716623 : Blo 714321 716623 := bstep (se 1 (by rfl) ⟨537467, by rfl⟩ : syracuseStep 716623 = 1074935) B1074935
theorem B716639 : Blo 714321 716639 := bstep (se 1 (by rfl) ⟨537479, by rfl⟩ : syracuseStep 716639 = 1074959) B1074959
theorem B716667 : Blo 714321 716667 := bstep (se 1 (by rfl) ⟨537500, by rfl⟩ : syracuseStep 716667 = 1075001) B1075001
theorem B716719 : Blo 714321 716719 := bstep (se 1 (by rfl) ⟨537539, by rfl⟩ : syracuseStep 716719 = 1075079) B1075079
theorem B1077167 : Blo 714321 1077167 := bstep (se 1 (by rfl) ⟨807875, by rfl⟩ : syracuseStep 1077167 = 1615751) B1615751
theorem B716743 : Blo 714321 716743 := bstep (se 1 (by rfl) ⟨537557, by rfl⟩ : syracuseStep 716743 = 1075115) B1075115
theorem B716763 : Blo 714321 716763 := bstep (se 1 (by rfl) ⟨537572, by rfl⟩ : syracuseStep 716763 = 1075145) B1075145
theorem B1077257 : Blo 714321 1077257 := bstep (se 2 (by rfl) ⟨403971, by rfl⟩ : syracuseStep 1077257 = 807943) B807943
theorem B716839 : Blo 714321 716839 := bstep (se 1 (by rfl) ⟨537629, by rfl⟩ : syracuseStep 716839 = 1075259) B1075259
theorem B1077287 : Blo 714321 1077287 := bstep (se 1 (by rfl) ⟨807965, by rfl⟩ : syracuseStep 1077287 = 1615931) B1615931
theorem B716879 : Blo 714321 716879 := bstep (se 1 (by rfl) ⟨537659, by rfl⟩ : syracuseStep 716879 = 1075319) B1075319
theorem B716895 : Blo 714321 716895 := bstep (se 1 (by rfl) ⟨537671, by rfl⟩ : syracuseStep 716895 = 1075343) B1075343
theorem B2289779 : Blo 714321 2289779 := bstep (se 1 (by rfl) ⟨1717334, by rfl⟩ : syracuseStep 2289779 = 3434669) B3434669
theorem B716923 : Blo 714321 716923 := bstep (se 1 (by rfl) ⟨537692, by rfl⟩ : syracuseStep 716923 = 1075385) B1075385
theorem B1077371 : Blo 714321 1077371 := bstep (se 1 (by rfl) ⟨808028, by rfl⟩ : syracuseStep 1077371 = 1616057) B1616057
theorem B716975 : Blo 714321 716975 := bstep (se 1 (by rfl) ⟨537731, by rfl⟩ : syracuseStep 716975 = 1075463) B1075463
theorem B11595953 : Blo 714321 11595953 := bstep (se 2 (by rfl) ⟨4348482, by rfl⟩ : syracuseStep 11595953 = 8696965) B8696965
theorem B716999 : Blo 714321 716999 := bstep (se 1 (by rfl) ⟨537749, by rfl⟩ : syracuseStep 716999 = 1075499) B1075499
theorem B717019 : Blo 714321 717019 := bstep (se 1 (by rfl) ⟨537764, by rfl⟩ : syracuseStep 717019 = 1075529) B1075529
theorem B1241335 : Blo 714321 1241335 := bstep (se 1 (by rfl) ⟨931001, by rfl⟩ : syracuseStep 1241335 = 1862003) B1862003
theorem B1208567 : Blo 714321 1208567 := bstep (se 1 (by rfl) ⟨906425, by rfl⟩ : syracuseStep 1208567 = 1812851) B1812851
theorem B717095 : Blo 714321 717095 := bstep (se 1 (by rfl) ⟨537821, by rfl⟩ : syracuseStep 717095 = 1075643) B1075643
theorem B717135 : Blo 714321 717135 := bstep (se 1 (by rfl) ⟨537851, by rfl⟩ : syracuseStep 717135 = 1075703) B1075703
theorem B717151 : Blo 714321 717151 := bstep (se 1 (by rfl) ⟨537863, by rfl⟩ : syracuseStep 717151 = 1075727) B1075727
theorem B717179 : Blo 714321 717179 := bstep (se 1 (by rfl) ⟨537884, by rfl⟩ : syracuseStep 717179 = 1075769) B1075769
theorem B717231 : Blo 714321 717231 := bstep (se 1 (by rfl) ⟨537923, by rfl⟩ : syracuseStep 717231 = 1075847) B1075847
theorem B717255 : Blo 714321 717255 := bstep (se 1 (by rfl) ⟨537941, by rfl⟩ : syracuseStep 717255 = 1075883) B1075883
theorem B717275 : Blo 714321 717275 := bstep (se 1 (by rfl) ⟨537956, by rfl⟩ : syracuseStep 717275 = 1075913) B1075913
theorem B4911641 : Blo 714321 4911641 := bstep (se 2 (by rfl) ⟨1841865, by rfl⟩ : syracuseStep 4911641 = 3683731) B3683731
theorem B2716193 : Blo 714321 2716193 := bstep (se 2 (by rfl) ⟨1018572, by rfl⟩ : syracuseStep 2716193 = 2037145) B2037145
theorem B717351 : Blo 714321 717351 := bstep (se 1 (by rfl) ⟨538013, by rfl⟩ : syracuseStep 717351 = 1076027) B1076027
theorem B3666491 : Blo 714321 3666491 := bstep (se 1 (by rfl) ⟨2749868, by rfl⟩ : syracuseStep 3666491 = 5499737) B5499737
theorem B1208911 : Blo 714321 1208911 := bstep (se 1 (by rfl) ⟨906683, by rfl⟩ : syracuseStep 1208911 = 1813367) B1813367
theorem B717391 : Blo 714321 717391 := bstep (se 1 (by rfl) ⟨538043, by rfl⟩ : syracuseStep 717391 = 1076087) B1076087
theorem B717407 : Blo 714321 717407 := bstep (se 1 (by rfl) ⟨538055, by rfl⟩ : syracuseStep 717407 = 1076111) B1076111
theorem B717435 : Blo 714321 717435 := bstep (se 1 (by rfl) ⟨538076, by rfl⟩ : syracuseStep 717435 = 1076153) B1076153
theorem B2519687 : Blo 714321 2519687 := bstep (se 1 (by rfl) ⟨1889765, by rfl⟩ : syracuseStep 2519687 = 3779531) B3779531
theorem B717487 : Blo 714321 717487 := bstep (se 1 (by rfl) ⟨538115, by rfl⟩ : syracuseStep 717487 = 1076231) B1076231
theorem B717511 : Blo 714321 717511 := bstep (se 1 (by rfl) ⟨538133, by rfl⟩ : syracuseStep 717511 = 1076267) B1076267
theorem B2716375 : Blo 714321 2716375 := bstep (se 1 (by rfl) ⟨2037281, by rfl⟩ : syracuseStep 2716375 = 4074563) B4074563
theorem B717531 : Blo 714321 717531 := bstep (se 1 (by rfl) ⟨538148, by rfl⟩ : syracuseStep 717531 = 1076297) B1076297
theorem B2519837 : Blo 714321 2519837 := bstep (se 3 (by rfl) ⟨472469, by rfl⟩ : syracuseStep 2519837 = 944939) B944939
theorem B717607 : Blo 714321 717607 := bstep (se 1 (by rfl) ⟨538205, by rfl⟩ : syracuseStep 717607 = 1076411) B1076411
theorem B1209161 : Blo 714321 1209161 := bstep (se 2 (by rfl) ⟨453435, by rfl⟩ : syracuseStep 1209161 = 906871) B906871
theorem B717647 : Blo 714321 717647 := bstep (se 1 (by rfl) ⟨538235, by rfl⟩ : syracuseStep 717647 = 1076471) B1076471
theorem B717663 : Blo 714321 717663 := bstep (se 1 (by rfl) ⟨538247, by rfl⟩ : syracuseStep 717663 = 1076495) B1076495
theorem B717691 : Blo 714321 717691 := bstep (se 1 (by rfl) ⟨538268, by rfl⟩ : syracuseStep 717691 = 1076537) B1076537
theorem B717743 : Blo 714321 717743 := bstep (se 1 (by rfl) ⟨538307, by rfl⟩ : syracuseStep 717743 = 1076615) B1076615
theorem B717767 : Blo 714321 717767 := bstep (se 1 (by rfl) ⟨538325, by rfl⟩ : syracuseStep 717767 = 1076651) B1076651
theorem B717787 : Blo 714321 717787 := bstep (se 1 (by rfl) ⟨538340, by rfl⟩ : syracuseStep 717787 = 1076681) B1076681
theorem B2716679 : Blo 714321 2716679 := bstep (se 1 (by rfl) ⟨2037509, by rfl⟩ : syracuseStep 2716679 = 4075019) B4075019
theorem B717863 : Blo 714321 717863 := bstep (se 1 (by rfl) ⟨538397, by rfl⟩ : syracuseStep 717863 = 1076795) B1076795
theorem B717903 : Blo 714321 717903 := bstep (se 1 (by rfl) ⟨538427, by rfl⟩ : syracuseStep 717903 = 1076855) B1076855
theorem B717919 : Blo 714321 717919 := bstep (se 1 (by rfl) ⟨538439, by rfl⟩ : syracuseStep 717919 = 1076879) B1076879
theorem B717947 : Blo 714321 717947 := bstep (se 1 (by rfl) ⟨538460, by rfl⟩ : syracuseStep 717947 = 1076921) B1076921
theorem B717999 : Blo 714321 717999 := bstep (se 1 (by rfl) ⟨538499, by rfl⟩ : syracuseStep 717999 = 1076999) B1076999
theorem B718023 : Blo 714321 718023 := bstep (se 1 (by rfl) ⟨538517, by rfl⟩ : syracuseStep 718023 = 1077035) B1077035
theorem B718043 : Blo 714321 718043 := bstep (se 1 (by rfl) ⟨538532, by rfl⟩ : syracuseStep 718043 = 1077065) B1077065
theorem B2422007 : Blo 714321 2422007 := bstep (se 1 (by rfl) ⟨1816505, by rfl⟩ : syracuseStep 2422007 = 3633011) B3633011
theorem B1209593 : Blo 714321 1209593 := bstep (se 2 (by rfl) ⟨453597, by rfl⟩ : syracuseStep 1209593 = 907195) B907195
theorem B718119 : Blo 714321 718119 := bstep (se 1 (by rfl) ⟨538589, by rfl⟩ : syracuseStep 718119 = 1077179) B1077179
theorem B718159 : Blo 714321 718159 := bstep (se 1 (by rfl) ⟨538619, by rfl⟩ : syracuseStep 718159 = 1077239) B1077239
theorem B718175 : Blo 714321 718175 := bstep (se 1 (by rfl) ⟨538631, by rfl⟩ : syracuseStep 718175 = 1077263) B1077263
theorem B718203 : Blo 714321 718203 := bstep (se 1 (by rfl) ⟨538652, by rfl⟩ : syracuseStep 718203 = 1077305) B1077305
theorem B181630349 : Blo 714321 181630349 := bstep (se 3 (by rfl) ⟨34055690, by rfl⟩ : syracuseStep 181630349 = 68111381) B68111381
theorem B10614179 : Blo 714321 10614179 := bstep (se 1 (by rfl) ⟨7960634, by rfl⟩ : syracuseStep 10614179 = 15921269) B15921269
theorem B1209775 : Blo 714321 1209775 := bstep (se 1 (by rfl) ⟨907331, by rfl⟩ : syracuseStep 1209775 = 1814663) B1814663
theorem B718255 : Blo 714321 718255 := bstep (se 1 (by rfl) ⟨538691, by rfl⟩ : syracuseStep 718255 = 1077383) B1077383
theorem B718279 : Blo 714321 718279 := bstep (se 1 (by rfl) ⟨538709, by rfl⟩ : syracuseStep 718279 = 1077419) B1077419
theorem B718299 : Blo 714321 718299 := bstep (se 1 (by rfl) ⟨538724, by rfl⟩ : syracuseStep 718299 = 1077449) B1077449
theorem B2717165 : Blo 714321 2717165 := bstep (se 3 (by rfl) ⟨509468, by rfl⟩ : syracuseStep 2717165 = 1018937) B1018937
theorem B3438067 : Blo 714321 3438067 := bstep (se 1 (by rfl) ⟨2578550, by rfl⟩ : syracuseStep 3438067 = 5157101) B5157101
theorem B1209863 : Blo 714321 1209863 := bstep (se 1 (by rfl) ⟨907397, by rfl⟩ : syracuseStep 1209863 = 1814795) B1814795
theorem B2422331 : Blo 714321 2422331 := bstep (se 1 (by rfl) ⟨1816748, by rfl⟩ : syracuseStep 2422331 = 3633497) B3633497
theorem B2422601 : Blo 714321 2422601 := bstep (se 2 (by rfl) ⟨908475, by rfl⟩ : syracuseStep 2422601 = 1816951) B1816951
theorem B1210207 : Blo 714321 1210207 := bstep (se 1 (by rfl) ⟨907655, by rfl⟩ : syracuseStep 1210207 = 1815311) B1815311
theorem B1210295 : Blo 714321 1210295 := bstep (se 1 (by rfl) ⟨907721, by rfl⟩ : syracuseStep 1210295 = 1815443) B1815443
theorem B4585729 : Blo 714321 4585729 := bstep (se 2 (by rfl) ⟨1719648, by rfl⟩ : syracuseStep 4585729 = 3439297) B3439297
theorem B7764329 : Blo 714321 7764329 := bstep (se 2 (by rfl) ⟨2911623, by rfl⟩ : syracuseStep 7764329 = 5823247) B5823247
theorem B2292097 : Blo 714321 2292097 := bstep (se 2 (by rfl) ⟨859536, by rfl⟩ : syracuseStep 2292097 = 1719073) B1719073
theorem B1210889 : Blo 714321 1210889 := bstep (se 2 (by rfl) ⟨454083, by rfl⟩ : syracuseStep 1210889 = 908167) B908167
theorem B14678597 : Blo 714321 14678597 := bstep (se 4 (by rfl) ⟨1376118, by rfl⟩ : syracuseStep 14678597 = 2752237) B2752237
theorem B2718305 : Blo 714321 2718305 := bstep (se 2 (by rfl) ⟨1019364, by rfl⟩ : syracuseStep 2718305 = 2038729) B2038729
theorem B1211051 : Blo 714321 1211051 := bstep (se 1 (by rfl) ⟨908288, by rfl⟩ : syracuseStep 1211051 = 1816577) B1816577
theorem B16546481 : Blo 714321 16546481 := bstep (se 2 (by rfl) ⟨6204930, by rfl⟩ : syracuseStep 16546481 = 12409861) B12409861
theorem B2653103 : Blo 714321 2653103 := bstep (se 1 (by rfl) ⟨1989827, by rfl⟩ : syracuseStep 2653103 = 3979655) B3979655
theorem B2423735 : Blo 714321 2423735 := bstep (se 1 (by rfl) ⟨1817801, by rfl⟩ : syracuseStep 2423735 = 3635603) B3635603
theorem B2456507 : Blo 714321 2456507 := bstep (se 1 (by rfl) ⟨1842380, by rfl⟩ : syracuseStep 2456507 = 3684761) B3684761
theorem B1145863 : Blo 714321 1145863 := bstep (se 1 (by rfl) ⟨859397, by rfl⟩ : syracuseStep 1145863 = 1718795) B1718795
theorem B1211449 : Blo 714321 1211449 := bstep (se 2 (by rfl) ⟨454293, by rfl⟩ : syracuseStep 1211449 = 908587) B908587
theorem B1211591 : Blo 714321 1211591 := bstep (se 1 (by rfl) ⟨908693, by rfl⟩ : syracuseStep 1211591 = 1817387) B1817387
theorem B2587895 : Blo 714321 2587895 := bstep (se 1 (by rfl) ⟨1940921, by rfl⟩ : syracuseStep 2587895 = 3881843) B3881843
theorem B1211753 : Blo 714321 1211753 := bstep (se 2 (by rfl) ⟨454407, by rfl⟩ : syracuseStep 1211753 = 908815) B908815
theorem B11599325 : Blo 714321 11599325 := bstep (se 3 (by rfl) ⟨2174873, by rfl⟩ : syracuseStep 11599325 = 4349747) B4349747
theorem B2424329 : Blo 714321 2424329 := bstep (se 2 (by rfl) ⟨909123, by rfl⟩ : syracuseStep 2424329 = 1818247) B1818247
theorem B2719291 : Blo 714321 2719291 := bstep (se 1 (by rfl) ⟨2039468, by rfl⟩ : syracuseStep 2719291 = 4078937) B4078937
theorem B3866251 : Blo 714321 3866251 := bstep (se 1 (by rfl) ⟨2899688, by rfl⟩ : syracuseStep 3866251 = 5799377) B5799377
theorem B1212151 : Blo 714321 1212151 := bstep (se 1 (by rfl) ⟨909113, by rfl⟩ : syracuseStep 1212151 = 1818227) B1818227
theorem B6127427 : Blo 714321 6127427 := bstep (se 1 (by rfl) ⟨4595570, by rfl⟩ : syracuseStep 6127427 = 9191141) B9191141
theorem B2719595 : Blo 714321 2719595 := bstep (se 1 (by rfl) ⟨2039696, by rfl⟩ : syracuseStep 2719595 = 4079393) B4079393
theorem B20709593 : Blo 714321 20709593 := bstep (se 2 (by rfl) ⟨7766097, by rfl⟩ : syracuseStep 20709593 = 15532195) B15532195
theorem B6193847 : Blo 714321 6193847 := bstep (se 1 (by rfl) ⟨4645385, by rfl⟩ : syracuseStep 6193847 = 9290771) B9290771
theorem B12255947 : Blo 714321 12255947 := bstep (se 1 (by rfl) ⟨9191960, by rfl⟩ : syracuseStep 12255947 = 18383921) B18383921
theorem B4653883 : Blo 714321 4653883 := bstep (se 1 (by rfl) ⟨3490412, by rfl⟩ : syracuseStep 4653883 = 6980825) B6980825
theorem B1147727 : Blo 714321 1147727 := bstep (se 1 (by rfl) ⟨860795, by rfl⟩ : syracuseStep 1147727 = 1721591) B1721591
theorem B918983 : Blo 714321 918983 := bstep (se 1 (by rfl) ⟨689237, by rfl⟩ : syracuseStep 918983 = 1378475) B1378475
theorem B1934855 : Blo 714321 1934855 := bstep (se 1 (by rfl) ⟨1451141, by rfl⟩ : syracuseStep 1934855 = 2902283) B2902283
theorem B1967777 : Blo 714321 1967777 := bstep (se 2 (by rfl) ⟨737916, by rfl⟩ : syracuseStep 1967777 = 1475833) B1475833
theorem B6129341 : Blo 714321 6129341 := bstep (se 3 (by rfl) ⟨1149251, by rfl⟩ : syracuseStep 6129341 = 2298503) B2298503
theorem B1607471 : Blo 714321 1607471 := bstep (se 1 (by rfl) ⟨1205603, by rfl⟩ : syracuseStep 1607471 = 2411207) B2411207
theorem B3442817 : Blo 714321 3442817 := bstep (se 2 (by rfl) ⟨1291056, by rfl⟩ : syracuseStep 3442817 = 2582113) B2582113
theorem B1608047 : Blo 714321 1608047 := bstep (se 1 (by rfl) ⟨1206035, by rfl⟩ : syracuseStep 1608047 = 2412071) B2412071
theorem B1608119 : Blo 714321 1608119 := bstep (se 1 (by rfl) ⟨1206089, by rfl⟩ : syracuseStep 1608119 = 2412179) B2412179
theorem B1608263 : Blo 714321 1608263 := bstep (se 1 (by rfl) ⟨1206197, by rfl⟩ : syracuseStep 1608263 = 2412395) B2412395
theorem B1608299 : Blo 714321 1608299 := bstep (se 1 (by rfl) ⟨1206224, by rfl⟩ : syracuseStep 1608299 = 2412449) B2412449
theorem B7736087 : Blo 714321 7736087 := bstep (se 1 (by rfl) ⟨5802065, by rfl⟩ : syracuseStep 7736087 = 11604131) B11604131
theorem B6884129 : Blo 714321 6884129 := bstep (se 2 (by rfl) ⟨2581548, by rfl⟩ : syracuseStep 6884129 = 5163097) B5163097
theorem B12225329 : Blo 714321 12225329 := bstep (se 2 (by rfl) ⟨4584498, by rfl⟩ : syracuseStep 12225329 = 9168997) B9168997
theorem B1608695 : Blo 714321 1608695 := bstep (se 1 (by rfl) ⟨1206521, by rfl⟩ : syracuseStep 1608695 = 2413043) B2413043
theorem B1609055 : Blo 714321 1609055 := bstep (se 1 (by rfl) ⟨1206791, by rfl⟩ : syracuseStep 1609055 = 2413583) B2413583
theorem B3444065 : Blo 714321 3444065 := bstep (se 2 (by rfl) ⟨1291524, by rfl⟩ : syracuseStep 3444065 = 2583049) B2583049
theorem B1838459 : Blo 714321 1838459 := bstep (se 1 (by rfl) ⟨1378844, by rfl⟩ : syracuseStep 1838459 = 2757689) B2757689
theorem B1609451 : Blo 714321 1609451 := bstep (se 1 (by rfl) ⟨1207088, by rfl⟩ : syracuseStep 1609451 = 2414177) B2414177
theorem B3870467 : Blo 714321 3870467 := bstep (se 1 (by rfl) ⟨2902850, by rfl⟩ : syracuseStep 3870467 = 5805701) B5805701
theorem B1937159 : Blo 714321 1937159 := bstep (se 1 (by rfl) ⟨1452869, by rfl⟩ : syracuseStep 1937159 = 2905739) B2905739
theorem B1609577 : Blo 714321 1609577 := bstep (se 2 (by rfl) ⟨603591, by rfl⟩ : syracuseStep 1609577 = 1207183) B1207183
theorem B2297915 : Blo 714321 2297915 := bstep (se 1 (by rfl) ⟨1723436, by rfl⟩ : syracuseStep 2297915 = 3446873) B3446873
theorem B6131801 : Blo 714321 6131801 := bstep (se 2 (by rfl) ⟨2299425, by rfl⟩ : syracuseStep 6131801 = 4598851) B4598851
theorem B725279 : Blo 714321 725279 := bstep (se 1 (by rfl) ⟨543959, by rfl⟩ : syracuseStep 725279 = 1087919) B1087919
theorem B2298287 : Blo 714321 2298287 := bstep (se 1 (by rfl) ⟨1723715, by rfl⟩ : syracuseStep 2298287 = 3447431) B3447431
theorem B1610423 : Blo 714321 1610423 := bstep (se 1 (by rfl) ⟨1207817, by rfl⟩ : syracuseStep 1610423 = 2415635) B2415635
theorem B24843023 : Blo 714321 24843023 := bstep (se 1 (by rfl) ⟨18632267, by rfl⟩ : syracuseStep 24843023 = 37264535) B37264535
theorem B1610639 : Blo 714321 1610639 := bstep (se 1 (by rfl) ⟨1207979, by rfl⟩ : syracuseStep 1610639 = 2415959) B2415959
theorem B14718509 : Blo 714321 14718509 := bstep (se 3 (by rfl) ⟨2759720, by rfl⟩ : syracuseStep 14718509 = 5519441) B5519441
theorem B2037305 : Blo 714321 2037305 := bstep (se 2 (by rfl) ⟨763989, by rfl⟩ : syracuseStep 2037305 = 1527979) B1527979
theorem B1611359 : Blo 714321 1611359 := bstep (se 1 (by rfl) ⟨1208519, by rfl⟩ : syracuseStep 1611359 = 2417039) B2417039
theorem B1808183 : Blo 714321 1808183 := bstep (se 1 (by rfl) ⟨1356137, by rfl⟩ : syracuseStep 1808183 = 2712275) B2712275
theorem B1611575 : Blo 714321 1611575 := bstep (se 1 (by rfl) ⟨1208681, by rfl⟩ : syracuseStep 1611575 = 2417363) B2417363
theorem B15898427 : Blo 714321 15898427 := bstep (se 1 (by rfl) ⟨11923820, by rfl⟩ : syracuseStep 15898427 = 23847641) B23847641
theorem B1611881 : Blo 714321 1611881 := bstep (se 2 (by rfl) ⟨604455, by rfl⟩ : syracuseStep 1611881 = 1208911) B1208911
theorem B7444759 : Blo 714321 7444759 := bstep (se 1 (by rfl) ⟨5583569, by rfl⟩ : syracuseStep 7444759 = 11167139) B11167139
theorem B1808851 : Blo 714321 1808851 := bstep (se 1 (by rfl) ⟨1356638, by rfl⟩ : syracuseStep 1808851 = 2713277) B2713277
theorem B11606591 : Blo 714321 11606591 := bstep (se 1 (by rfl) ⟨8704943, by rfl⟩ : syracuseStep 11606591 = 17409887) B17409887
theorem B1612367 : Blo 714321 1612367 := bstep (se 1 (by rfl) ⟨1209275, by rfl⟩ : syracuseStep 1612367 = 2418551) B2418551
theorem B1612511 : Blo 714321 1612511 := bstep (se 1 (by rfl) ⟨1209383, by rfl⟩ : syracuseStep 1612511 = 2418767) B2418767
theorem B2038547 : Blo 714321 2038547 := bstep (se 1 (by rfl) ⟨1528910, by rfl⟩ : syracuseStep 2038547 = 3057821) B3057821
theorem B3054455 : Blo 714321 3054455 := bstep (se 1 (by rfl) ⟨2290841, by rfl⟩ : syracuseStep 3054455 = 4581683) B4581683
theorem B4135799 : Blo 714321 4135799 := bstep (se 1 (by rfl) ⟨3101849, by rfl⟩ : syracuseStep 4135799 = 6203699) B6203699
theorem B826319 : Blo 714321 826319 := bstep (se 1 (by rfl) ⟨619739, by rfl⟩ : syracuseStep 826319 = 1239479) B1239479
theorem B1743835 : Blo 714321 1743835 := bstep (se 1 (by rfl) ⟨1307876, by rfl⟩ : syracuseStep 1743835 = 2615753) B2615753
theorem B1612763 : Blo 714321 1612763 := bstep (se 1 (by rfl) ⟨1209572, by rfl⟩ : syracuseStep 1612763 = 2419145) B2419145
theorem B1612943 : Blo 714321 1612943 := bstep (se 1 (by rfl) ⟨1209707, by rfl⟩ : syracuseStep 1612943 = 2419415) B2419415
theorem B2039003 : Blo 714321 2039003 := bstep (se 1 (by rfl) ⟨1529252, by rfl⟩ : syracuseStep 2039003 = 3058505) B3058505
theorem B1809641 : Blo 714321 1809641 := bstep (se 2 (by rfl) ⟨678615, by rfl⟩ : syracuseStep 1809641 = 1357231) B1357231
theorem B1613033 : Blo 714321 1613033 := bstep (se 2 (by rfl) ⟨604887, by rfl⟩ : syracuseStep 1613033 = 1209775) B1209775
theorem B1613087 : Blo 714321 1613087 := bstep (se 1 (by rfl) ⟨1209815, by rfl⟩ : syracuseStep 1613087 = 2419631) B2419631
theorem B1809803 : Blo 714321 1809803 := bstep (se 1 (by rfl) ⟨1357352, by rfl⟩ : syracuseStep 1809803 = 2714705) B2714705
theorem B1613609 : Blo 714321 1613609 := bstep (se 2 (by rfl) ⟨605103, by rfl⟩ : syracuseStep 1613609 = 1210207) B1210207
theorem B1089335 : Blo 714321 1089335 := bstep (se 1 (by rfl) ⟨817001, by rfl⟩ : syracuseStep 1089335 = 1634003) B1634003
theorem B1941353 : Blo 714321 1941353 := bstep (se 2 (by rfl) ⟨728007, by rfl⟩ : syracuseStep 1941353 = 1456015) B1456015
theorem B2039833 : Blo 714321 2039833 := bstep (se 2 (by rfl) ⟨764937, by rfl⟩ : syracuseStep 2039833 = 1529875) B1529875
theorem B1810795 : Blo 714321 1810795 := bstep (se 1 (by rfl) ⟨1358096, by rfl⟩ : syracuseStep 1810795 = 2716193) B2716193
theorem B1679791 : Blo 714321 1679791 := bstep (se 1 (by rfl) ⟨1259843, by rfl⟩ : syracuseStep 1679791 = 2519687) B2519687
theorem B3056129 : Blo 714321 3056129 := bstep (se 2 (by rfl) ⟨1146048, by rfl⟩ : syracuseStep 3056129 = 2292097) B2292097
theorem B1679891 : Blo 714321 1679891 := bstep (se 1 (by rfl) ⟨1259918, by rfl⟩ : syracuseStep 1679891 = 2519837) B2519837
theorem B6890129 : Blo 714321 6890129 := bstep (se 2 (by rfl) ⟨2583798, by rfl⟩ : syracuseStep 6890129 = 5167597) B5167597
theorem B1811119 : Blo 714321 1811119 := bstep (se 1 (by rfl) ⟨1358339, by rfl⟩ : syracuseStep 1811119 = 2716679) B2716679
theorem B1614671 : Blo 714321 1614671 := bstep (se 1 (by rfl) ⟨1211003, by rfl⟩ : syracuseStep 1614671 = 2422007) B2422007
theorem B121086899 : Blo 714321 121086899 := bstep (se 1 (by rfl) ⟨90815174, by rfl⟩ : syracuseStep 121086899 = 181630349) B181630349
theorem B1811443 : Blo 714321 1811443 := bstep (se 1 (by rfl) ⟨1358582, by rfl⟩ : syracuseStep 1811443 = 2717165) B2717165
theorem B1614887 : Blo 714321 1614887 := bstep (se 1 (by rfl) ⟨1211165, by rfl⟩ : syracuseStep 1614887 = 2422331) B2422331
theorem B11609189 : Blo 714321 11609189 := bstep (se 4 (by rfl) ⟨1088361, by rfl⟩ : syracuseStep 11609189 = 2176723) B2176723
theorem B1615067 : Blo 714321 1615067 := bstep (se 1 (by rfl) ⟨1211300, by rfl⟩ : syracuseStep 1615067 = 2422601) B2422601
theorem B1615265 : Blo 714321 1615265 := bstep (se 2 (by rfl) ⟨605724, by rfl⟩ : syracuseStep 1615265 = 1211449) B1211449
theorem B1451603 : Blo 714321 1451603 := bstep (se 1 (by rfl) ⟨1088702, by rfl⟩ : syracuseStep 1451603 = 2177405) B2177405
theorem B1812203 : Blo 714321 1812203 := bstep (se 1 (by rfl) ⟨1359152, by rfl⟩ : syracuseStep 1812203 = 2718305) B2718305
theorem B1615823 : Blo 714321 1615823 := bstep (se 1 (by rfl) ⟨1211867, by rfl⟩ : syracuseStep 1615823 = 2423735) B2423735
theorem B5155001 : Blo 714321 5155001 := bstep (se 2 (by rfl) ⟨1933125, by rfl⟩ : syracuseStep 5155001 = 3866251) B3866251
theorem B7973057 : Blo 714321 7973057 := bstep (se 2 (by rfl) ⟨2989896, by rfl⟩ : syracuseStep 7973057 = 5979793) B5979793
theorem B1616201 : Blo 714321 1616201 := bstep (se 2 (by rfl) ⟨606075, by rfl⟩ : syracuseStep 1616201 = 1212151) B1212151
theorem B1616219 : Blo 714321 1616219 := bstep (se 1 (by rfl) ⟨1212164, by rfl⟩ : syracuseStep 1616219 = 2424329) B2424329
theorem B1813063 : Blo 714321 1813063 := bstep (se 1 (by rfl) ⟨1359797, by rfl⟩ : syracuseStep 1813063 = 2719595) B2719595
theorem B1813175 : Blo 714321 1813175 := bstep (se 1 (by rfl) ⟨1359881, by rfl⟩ : syracuseStep 1813175 = 2719763) B2719763
theorem B2042749 : Blo 714321 2042749 := bstep (se 3 (by rfl) ⟨383015, by rfl⟩ : syracuseStep 2042749 = 766031) B766031
theorem B4139947 : Blo 714321 4139947 := bstep (se 1 (by rfl) ⟨3104960, by rfl⟩ : syracuseStep 4139947 = 6209921) B6209921
theorem B2042795 : Blo 714321 2042795 := bstep (se 1 (by rfl) ⟨1532096, by rfl⟩ : syracuseStep 2042795 = 3064193) B3064193
theorem B1289449 : Blo 714321 1289449 := bstep (se 2 (by rfl) ⟨483543, by rfl⟩ : syracuseStep 1289449 = 967087) B967087
theorem B14691901 : Blo 714321 14691901 := bstep (se 3 (by rfl) ⟨2754731, by rfl⟩ : syracuseStep 14691901 = 5509463) B5509463
theorem B1814177 : Blo 714321 1814177 := bstep (se 2 (by rfl) ⟨680316, by rfl⟩ : syracuseStep 1814177 = 1360633) B1360633
theorem B1552135 : Blo 714321 1552135 := bstep (se 1 (by rfl) ⟨1164101, by rfl⟩ : syracuseStep 1552135 = 2328203) B2328203
theorem B765775 : Blo 714321 765775 := bstep (se 1 (by rfl) ⟨574331, by rfl⟩ : syracuseStep 765775 = 1148663) B1148663
theorem B23179193 : Blo 714321 23179193 := bstep (se 2 (by rfl) ⟨8692197, by rfl⟩ : syracuseStep 23179193 = 17384395) B17384395
theorem B1814633 : Blo 714321 1814633 := bstep (se 2 (by rfl) ⟨680487, by rfl⟩ : syracuseStep 1814633 = 1360975) B1360975
theorem B5451947 : Blo 714321 5451947 := bstep (se 1 (by rfl) ⟨4088960, by rfl⟩ : syracuseStep 5451947 = 8177921) B8177921
theorem B2044435 : Blo 714321 2044435 := bstep (se 1 (by rfl) ⟨1533326, by rfl⟩ : syracuseStep 2044435 = 3066653) B3066653
theorem B1815119 : Blo 714321 1815119 := bstep (se 1 (by rfl) ⟨1361339, by rfl⟩ : syracuseStep 1815119 = 2722679) B2722679
theorem B1356563 : Blo 714321 1356563 := bstep (se 1 (by rfl) ⟨1017422, by rfl⟩ : syracuseStep 1356563 = 2034845) B2034845
theorem B7844701 : Blo 714321 7844701 := bstep (se 3 (by rfl) ⟨1470881, by rfl⟩ : syracuseStep 7844701 = 2941763) B2941763
theorem B3617783 : Blo 714321 3617783 := bstep (se 1 (by rfl) ⟨2713337, by rfl⟩ : syracuseStep 3617783 = 5426675) B5426675
theorem B32257091 : Blo 714321 32257091 := bstep (se 1 (by rfl) ⟨24192818, by rfl⟩ : syracuseStep 32257091 = 48385637) B48385637
theorem B9188477 : Blo 714321 9188477 := bstep (se 3 (by rfl) ⟨1722839, by rfl⟩ : syracuseStep 9188477 = 3445679) B3445679
theorem B1815767 : Blo 714321 1815767 := bstep (se 1 (by rfl) ⟨1361825, by rfl⟩ : syracuseStep 1815767 = 2723651) B2723651
theorem B1357087 : Blo 714321 1357087 := bstep (se 1 (by rfl) ⟨1017815, by rfl⟩ : syracuseStep 1357087 = 2035631) B2035631
theorem B1816121 : Blo 714321 1816121 := bstep (se 2 (by rfl) ⟨681045, by rfl⟩ : syracuseStep 1816121 = 1362091) B1362091
theorem B1717843 : Blo 714321 1717843 := bstep (se 1 (by rfl) ⟨1288382, by rfl⟩ : syracuseStep 1717843 = 2576765) B2576765
theorem B18397043 : Blo 714321 18397043 := bstep (se 1 (by rfl) ⟨13797782, by rfl⟩ : syracuseStep 18397043 = 27595565) B27595565
theorem B2177599 : Blo 714321 2177599 := bstep (se 1 (by rfl) ⟨1633199, by rfl⟩ : syracuseStep 2177599 = 3266399) B3266399
theorem B4078187 : Blo 714321 4078187 := bstep (se 1 (by rfl) ⟨3058640, by rfl⟩ : syracuseStep 4078187 = 6117281) B6117281
theorem B3062519 : Blo 714321 3062519 := bstep (se 1 (by rfl) ⟨2296889, by rfl⟩ : syracuseStep 3062519 = 4593779) B4593779
theorem B3914639 : Blo 714321 3914639 := bstep (se 1 (by rfl) ⟨2935979, by rfl⟩ : syracuseStep 3914639 = 5871959) B5871959
theorem B3619727 : Blo 714321 3619727 := bstep (se 1 (by rfl) ⟨2714795, by rfl⟩ : syracuseStep 3619727 = 5429591) B5429591
theorem B59554739 : Blo 714321 59554739 := bstep (se 1 (by rfl) ⟨44666054, by rfl⟩ : syracuseStep 59554739 = 89332109) B89332109
theorem B5291513 : Blo 714321 5291513 := bstep (se 2 (by rfl) ⟨1984317, by rfl⟩ : syracuseStep 5291513 = 3968635) B3968635
theorem B4079119 : Blo 714321 4079119 := bstep (se 1 (by rfl) ⟨3059339, by rfl⟩ : syracuseStep 4079119 = 6118679) B6118679
theorem B19579117 : Blo 714321 19579117 := bstep (se 3 (by rfl) ⟨3671084, by rfl⟩ : syracuseStep 19579117 = 7342169) B7342169
theorem B29475089 : Blo 714321 29475089 := bstep (se 2 (by rfl) ⟨11053158, by rfl⟩ : syracuseStep 29475089 = 22106317) B22106317
theorem B1655113 : Blo 714321 1655113 := bstep (se 2 (by rfl) ⟨620667, by rfl⟩ : syracuseStep 1655113 = 1241335) B1241335
theorem B69714269 : Blo 714321 69714269 := bstep (se 3 (by rfl) ⟨13071425, by rfl⟩ : syracuseStep 69714269 = 26142851) B26142851
theorem B3064655 : Blo 714321 3064655 := bstep (se 1 (by rfl) ⟨2298491, by rfl⟩ : syracuseStep 3064655 = 4596983) B4596983
theorem B4080577 : Blo 714321 4080577 := bstep (se 2 (by rfl) ⟨1530216, by rfl⟩ : syracuseStep 4080577 = 3060433) B3060433
theorem B3621833 : Blo 714321 3621833 := bstep (se 2 (by rfl) ⟨1358187, by rfl⟩ : syracuseStep 3621833 = 2716375) B2716375
theorem B3064807 : Blo 714321 3064807 := bstep (se 1 (by rfl) ⟨2298605, by rfl⟩ : syracuseStep 3064807 = 4597211) B4597211
theorem B3064979 : Blo 714321 3064979 := bstep (se 1 (by rfl) ⟨2298734, by rfl⟩ : syracuseStep 3064979 = 4597469) B4597469
theorem B804127 : Blo 714321 804127 := bstep (se 1 (by rfl) ⟨603095, by rfl⟩ : syracuseStep 804127 = 1206191) B1206191
theorem B15516971 : Blo 714321 15516971 := bstep (se 1 (by rfl) ⟨11637728, by rfl⟩ : syracuseStep 15516971 = 23275457) B23275457
theorem B7062833 : Blo 714321 7062833 := bstep (se 2 (by rfl) ⟨2648562, by rfl⟩ : syracuseStep 7062833 = 5297125) B5297125
theorem B27477467 : Blo 714321 27477467 := bstep (se 1 (by rfl) ⟨20608100, by rfl⟩ : syracuseStep 27477467 = 41216201) B41216201
theorem B39142925 : Blo 714321 39142925 := bstep (se 3 (by rfl) ⟨7339298, by rfl⟩ : syracuseStep 39142925 = 14678597) B14678597
theorem B24823331 : Blo 714321 24823331 := bstep (se 1 (by rfl) ⟨18617498, by rfl⟩ : syracuseStep 24823331 = 37234997) B37234997
theorem B804415 : Blo 714321 804415 := bstep (se 1 (by rfl) ⟨603311, by rfl⟩ : syracuseStep 804415 = 1206623) B1206623
theorem B12371575 : Blo 714321 12371575 := bstep (se 1 (by rfl) ⟨9278681, by rfl⟩ : syracuseStep 12371575 = 18557363) B18557363
theorem B1361711 : Blo 714321 1361711 := bstep (se 1 (by rfl) ⟨1021283, by rfl⟩ : syracuseStep 1361711 = 2042567) B2042567
theorem B2901815 : Blo 714321 2901815 := bstep (se 1 (by rfl) ⟨2176361, by rfl⟩ : syracuseStep 2901815 = 4352723) B4352723
theorem B9193601 : Blo 714321 9193601 := bstep (se 2 (by rfl) ⟨3447600, by rfl⟩ : syracuseStep 9193601 = 6895201) B6895201
theorem B805243 : Blo 714321 805243 := bstep (se 1 (by rfl) ⟨603932, by rfl⟩ : syracuseStep 805243 = 1207865) B1207865
theorem B3066295 : Blo 714321 3066295 := bstep (se 1 (by rfl) ⟨2299721, by rfl⟩ : syracuseStep 3066295 = 4599443) B4599443
theorem B1526519 : Blo 714321 1526519 := bstep (se 1 (by rfl) ⟨1144889, by rfl⟩ : syracuseStep 1526519 = 2289779) B2289779
theorem B805711 : Blo 714321 805711 := bstep (se 1 (by rfl) ⟨604283, by rfl⟩ : syracuseStep 805711 = 1208567) B1208567
theorem B1362919 : Blo 714321 1362919 := bstep (se 1 (by rfl) ⟨1022189, by rfl⟩ : syracuseStep 1362919 = 2044379) B2044379
theorem B6114305 : Blo 714321 6114305 := bstep (se 2 (by rfl) ⟨2292864, by rfl⟩ : syracuseStep 6114305 = 4585729) B4585729
theorem B2444327 : Blo 714321 2444327 := bstep (se 1 (by rfl) ⟨1833245, by rfl⟩ : syracuseStep 2444327 = 3666491) B3666491
theorem B806107 : Blo 714321 806107 := bstep (se 1 (by rfl) ⟨604580, by rfl⟩ : syracuseStep 806107 = 1209161) B1209161
theorem B2411963 : Blo 714321 2411963 := bstep (se 1 (by rfl) ⟨1808972, by rfl⟩ : syracuseStep 2411963 = 3617945) B3617945
theorem B904699 : Blo 714321 904699 := bstep (se 1 (by rfl) ⟨678524, by rfl⟩ : syracuseStep 904699 = 1357049) B1357049
theorem B806395 : Blo 714321 806395 := bstep (se 1 (by rfl) ⟨604796, by rfl⟩ : syracuseStep 806395 = 1209593) B1209593
theorem B806575 : Blo 714321 806575 := bstep (se 1 (by rfl) ⟨604931, by rfl⟩ : syracuseStep 806575 = 1209863) B1209863
theorem B904927 : Blo 714321 904927 := bstep (se 1 (by rfl) ⟨678695, by rfl⟩ : syracuseStep 904927 = 1357391) B1357391
theorem B806863 : Blo 714321 806863 := bstep (se 1 (by rfl) ⟨605147, by rfl⟩ : syracuseStep 806863 = 1210295) B1210295
theorem B1527817 : Blo 714321 1527817 := bstep (se 2 (by rfl) ⟨572931, by rfl⟩ : syracuseStep 1527817 = 1145863) B1145863
theorem B807259 : Blo 714321 807259 := bstep (se 1 (by rfl) ⟨605444, by rfl⟩ : syracuseStep 807259 = 1210889) B1210889
theorem B905671 : Blo 714321 905671 := bstep (se 1 (by rfl) ⟨679253, by rfl⟩ : syracuseStep 905671 = 1358507) B1358507
theorem B807367 : Blo 714321 807367 := bstep (se 1 (by rfl) ⟨605525, by rfl⟩ : syracuseStep 807367 = 1211051) B1211051
theorem B11030987 : Blo 714321 11030987 := bstep (se 1 (by rfl) ⟨8273240, by rfl⟩ : syracuseStep 11030987 = 16546481) B16546481
theorem B3625721 : Blo 714321 3625721 := bstep (se 2 (by rfl) ⟨1359645, by rfl⟩ : syracuseStep 3625721 = 2719291) B2719291
theorem B807727 : Blo 714321 807727 := bstep (se 1 (by rfl) ⟨605795, by rfl⟩ : syracuseStep 807727 = 1211591) B1211591
theorem B1725263 : Blo 714321 1725263 := bstep (se 1 (by rfl) ⟨1293947, by rfl⟩ : syracuseStep 1725263 = 2587895) B2587895
theorem B807835 : Blo 714321 807835 := bstep (se 1 (by rfl) ⟨605876, by rfl⟩ : syracuseStep 807835 = 1211753) B1211753
theorem B5428133 : Blo 714321 5428133 := bstep (se 4 (by rfl) ⟨508887, by rfl⟩ : syracuseStep 5428133 = 1017775) B1017775
theorem B4084951 : Blo 714321 4084951 := bstep (se 1 (by rfl) ⟨3063713, by rfl⟩ : syracuseStep 4084951 = 6127427) B6127427
theorem B5428619 : Blo 714321 5428619 := bstep (se 1 (by rfl) ⟨4071464, by rfl⟩ : syracuseStep 5428619 = 8142929) B8142929
theorem B6116903 : Blo 714321 6116903 := bstep (se 1 (by rfl) ⟨4587677, by rfl⟩ : syracuseStep 6116903 = 9175355) B9175355
theorem B906815 : Blo 714321 906815 := bstep (se 1 (by rfl) ⟨680111, by rfl⟩ : syracuseStep 906815 = 1360223) B1360223
theorem B1529705 : Blo 714321 1529705 := bstep (se 2 (by rfl) ⟨573639, by rfl⟩ : syracuseStep 1529705 = 1147279) B1147279
theorem B4577323 : Blo 714321 4577323 := bstep (se 1 (by rfl) ⟨3432992, by rfl⟩ : syracuseStep 4577323 = 6865985) B6865985
theorem B1071527 : Blo 714321 1071527 := bstep (se 1 (by rfl) ⟨803645, by rfl⟩ : syracuseStep 1071527 = 1607291) B1607291
theorem B1071611 : Blo 714321 1071611 := bstep (se 1 (by rfl) ⟨803708, by rfl⟩ : syracuseStep 1071611 = 1607417) B1607417
theorem B1071737 : Blo 714321 1071737 := bstep (se 2 (by rfl) ⟨401901, by rfl⟩ : syracuseStep 1071737 = 803803) B803803
theorem B1071791 : Blo 714321 1071791 := bstep (se 1 (by rfl) ⟨803843, by rfl⟩ : syracuseStep 1071791 = 1607687) B1607687
theorem B1530551 : Blo 714321 1530551 := bstep (se 1 (by rfl) ⟨1147913, by rfl⟩ : syracuseStep 1530551 = 2295827) B2295827
theorem B20601539 : Blo 714321 20601539 := bstep (se 1 (by rfl) ⟨15451154, by rfl⟩ : syracuseStep 20601539 = 30902309) B30902309
theorem B1071839 : Blo 714321 1071839 := bstep (se 1 (by rfl) ⟨803879, by rfl⟩ : syracuseStep 1071839 = 1607759) B1607759
theorem B908111 : Blo 714321 908111 := bstep (se 1 (by rfl) ⟨681083, by rfl⟩ : syracuseStep 908111 = 1362167) B1362167
theorem B4086683 : Blo 714321 4086683 := bstep (se 1 (by rfl) ⟨3065012, by rfl⟩ : syracuseStep 4086683 = 6130025) B6130025
theorem B777115 : Blo 714321 777115 := bstep (se 1 (by rfl) ⟨582836, by rfl⟩ : syracuseStep 777115 = 1165673) B1165673
theorem B1072103 : Blo 714321 1072103 := bstep (se 1 (by rfl) ⟨804077, by rfl⟩ : syracuseStep 1072103 = 1608155) B1608155
theorem B908263 : Blo 714321 908263 := bstep (se 1 (by rfl) ⟨681197, by rfl⟩ : syracuseStep 908263 = 1362395) B1362395
theorem B1531003 : Blo 714321 1531003 := bstep (se 1 (by rfl) ⟨1148252, by rfl⟩ : syracuseStep 1531003 = 2296505) B2296505
theorem B1072361 : Blo 714321 1072361 := bstep (se 2 (by rfl) ⟨402135, by rfl⟩ : syracuseStep 1072361 = 804271) B804271
theorem B1072415 : Blo 714321 1072415 := bstep (se 1 (by rfl) ⟨804311, by rfl⟩ : syracuseStep 1072415 = 1608623) B1608623
theorem B3628475 : Blo 714321 3628475 := bstep (se 1 (by rfl) ⟨2721356, by rfl⟩ : syracuseStep 3628475 = 5442713) B5442713
theorem B1072583 : Blo 714321 1072583 := bstep (se 1 (by rfl) ⟨804437, by rfl⟩ : syracuseStep 1072583 = 1608875) B1608875
theorem B2416121 : Blo 714321 2416121 := bstep (se 2 (by rfl) ⟨906045, by rfl⟩ : syracuseStep 2416121 = 1812091) B1812091
theorem B3497681 : Blo 714321 3497681 := bstep (se 2 (by rfl) ⟨1311630, by rfl⟩ : syracuseStep 3497681 = 2623261) B2623261
theorem B2416391 : Blo 714321 2416391 := bstep (se 1 (by rfl) ⟨1812293, by rfl⟩ : syracuseStep 2416391 = 3624587) B3624587
theorem B1072937 : Blo 714321 1072937 := bstep (se 2 (by rfl) ⟨402351, by rfl⟩ : syracuseStep 1072937 = 804703) B804703
theorem B1072943 : Blo 714321 1072943 := bstep (se 1 (by rfl) ⟨804707, by rfl⟩ : syracuseStep 1072943 = 1609415) B1609415
theorem B2416445 : Blo 714321 2416445 := bstep (se 3 (by rfl) ⟨453083, by rfl⟩ : syracuseStep 2416445 = 906167) B906167
theorem B3104669 : Blo 714321 3104669 := bstep (se 3 (by rfl) ⟨582125, by rfl⟩ : syracuseStep 3104669 = 1164251) B1164251
theorem B1073417 : Blo 714321 1073417 := bstep (se 2 (by rfl) ⟨402531, by rfl⟩ : syracuseStep 1073417 = 805063) B805063
theorem B1532233 : Blo 714321 1532233 := bstep (se 2 (by rfl) ⟨574587, by rfl⟩ : syracuseStep 1532233 = 1149175) B1149175
theorem B1073519 : Blo 714321 1073519 := bstep (se 1 (by rfl) ⟨805139, by rfl⟩ : syracuseStep 1073519 = 1610279) B1610279
theorem B6382091 : Blo 714321 6382091 := bstep (se 1 (by rfl) ⟨4786568, by rfl⟩ : syracuseStep 6382091 = 9573137) B9573137
theorem B1073735 : Blo 714321 1073735 := bstep (se 1 (by rfl) ⟨805301, by rfl⟩ : syracuseStep 1073735 = 1610603) B1610603
theorem B1073771 : Blo 714321 1073771 := bstep (se 1 (by rfl) ⟨805328, by rfl⟩ : syracuseStep 1073771 = 1610657) B1610657
theorem B3629771 : Blo 714321 3629771 := bstep (se 1 (by rfl) ⟨2722328, by rfl⟩ : syracuseStep 3629771 = 5444657) B5444657
theorem B1073999 : Blo 714321 1073999 := bstep (se 1 (by rfl) ⟨805499, by rfl⟩ : syracuseStep 1073999 = 1610999) B1610999
theorem B3629933 : Blo 714321 3629933 := bstep (se 3 (by rfl) ⟨680612, by rfl⟩ : syracuseStep 3629933 = 1361225) B1361225
theorem B1631195 : Blo 714321 1631195 := bstep (se 1 (by rfl) ⟨1223396, by rfl⟩ : syracuseStep 1631195 = 2446793) B2446793
theorem B2712791 : Blo 714321 2712791 := bstep (se 1 (by rfl) ⟨2034593, by rfl⟩ : syracuseStep 2712791 = 4069187) B4069187
theorem B1074395 : Blo 714321 1074395 := bstep (se 1 (by rfl) ⟨805796, by rfl⟩ : syracuseStep 1074395 = 1611593) B1611593
theorem B1205543 : Blo 714321 1205543 := bstep (se 1 (by rfl) ⟨904157, by rfl⟩ : syracuseStep 1205543 = 1808315) B1808315
theorem B1074569 : Blo 714321 1074569 := bstep (se 2 (by rfl) ⟨402963, by rfl⟩ : syracuseStep 1074569 = 805927) B805927
theorem B1533497 : Blo 714321 1533497 := bstep (se 2 (by rfl) ⟨575061, by rfl⟩ : syracuseStep 1533497 = 1150123) B1150123
theorem B714463 : Blo 714321 714463 := bstep (se 1 (by rfl) ⟨535847, by rfl⟩ : syracuseStep 714463 = 1071695) B1071695
theorem B1205995 : Blo 714321 1205995 := bstep (se 1 (by rfl) ⟨904496, by rfl⟩ : syracuseStep 1205995 = 1808993) B1808993
theorem B1074923 : Blo 714321 1074923 := bstep (se 1 (by rfl) ⟨806192, by rfl⟩ : syracuseStep 1074923 = 1612385) B1612385
theorem B1533737 : Blo 714321 1533737 := bstep (se 2 (by rfl) ⟨575151, by rfl⟩ : syracuseStep 1533737 = 1150303) B1150303
theorem B714543 : Blo 714321 714543 := bstep (se 1 (by rfl) ⟨535907, by rfl⟩ : syracuseStep 714543 = 1071815) B1071815
theorem B714651 : Blo 714321 714651 := bstep (se 1 (by rfl) ⟨535988, by rfl⟩ : syracuseStep 714651 = 1071977) B1071977
theorem B714703 : Blo 714321 714703 := bstep (se 1 (by rfl) ⟨536027, by rfl⟩ : syracuseStep 714703 = 1072055) B1072055
theorem B1075151 : Blo 714321 1075151 := bstep (se 1 (by rfl) ⟨806363, by rfl⟩ : syracuseStep 1075151 = 1612727) B1612727
theorem B714727 : Blo 714321 714727 := bstep (se 1 (by rfl) ⟨536045, by rfl⟩ : syracuseStep 714727 = 1072091) B1072091
theorem B2910343 : Blo 714321 2910343 := bstep (se 1 (by rfl) ⟨2182757, by rfl⟩ : syracuseStep 2910343 = 4365515) B4365515
theorem B4581629 : Blo 714321 4581629 := bstep (se 3 (by rfl) ⟨859055, by rfl⟩ : syracuseStep 4581629 = 1718111) B1718111
theorem B715039 : Blo 714321 715039 := bstep (se 1 (by rfl) ⟨536279, by rfl⟩ : syracuseStep 715039 = 1072559) B1072559
theorem B715099 : Blo 714321 715099 := bstep (se 1 (by rfl) ⟨536324, by rfl⟩ : syracuseStep 715099 = 1072649) B1072649
theorem B1075547 : Blo 714321 1075547 := bstep (se 1 (by rfl) ⟨806660, by rfl⟩ : syracuseStep 1075547 = 1613321) B1613321
theorem B715119 : Blo 714321 715119 := bstep (se 1 (by rfl) ⟨536339, by rfl⟩ : syracuseStep 715119 = 1072679) B1072679
theorem B715175 : Blo 714321 715175 := bstep (se 1 (by rfl) ⟨536381, by rfl⟩ : syracuseStep 715175 = 1072763) B1072763
theorem B715259 : Blo 714321 715259 := bstep (se 1 (by rfl) ⟨536444, by rfl⟩ : syracuseStep 715259 = 1072889) B1072889
theorem B715327 : Blo 714321 715327 := bstep (se 1 (by rfl) ⟨536495, by rfl⟩ : syracuseStep 715327 = 1072991) B1072991
theorem B1075775 : Blo 714321 1075775 := bstep (se 1 (by rfl) ⟨806831, by rfl⟩ : syracuseStep 1075775 = 1613663) B1613663
theorem B715335 : Blo 714321 715335 := bstep (se 1 (by rfl) ⟨536501, by rfl⟩ : syracuseStep 715335 = 1073003) B1073003
theorem B2714219 : Blo 714321 2714219 := bstep (se 1 (by rfl) ⟨2035664, by rfl⟩ : syracuseStep 2714219 = 4071329) B4071329
theorem B2419307 : Blo 714321 2419307 := bstep (se 1 (by rfl) ⟨1814480, by rfl⟩ : syracuseStep 2419307 = 3628961) B3628961
theorem B1206967 : Blo 714321 1206967 := bstep (se 1 (by rfl) ⟨905225, by rfl⟩ : syracuseStep 1206967 = 1810451) B1810451
theorem B1075895 : Blo 714321 1075895 := bstep (se 1 (by rfl) ⟨806921, by rfl⟩ : syracuseStep 1075895 = 1613843) B1613843
theorem B715487 : Blo 714321 715487 := bstep (se 1 (by rfl) ⟨536615, by rfl⟩ : syracuseStep 715487 = 1073231) B1073231
theorem B715567 : Blo 714321 715567 := bstep (se 1 (by rfl) ⟨536675, by rfl⟩ : syracuseStep 715567 = 1073351) B1073351
theorem B715675 : Blo 714321 715675 := bstep (se 1 (by rfl) ⟨536756, by rfl⟩ : syracuseStep 715675 = 1073513) B1073513
theorem B1076123 : Blo 714321 1076123 := bstep (se 1 (by rfl) ⟨807092, by rfl⟩ : syracuseStep 1076123 = 1614185) B1614185
theorem B715727 : Blo 714321 715727 := bstep (se 1 (by rfl) ⟨536795, by rfl⟩ : syracuseStep 715727 = 1073591) B1073591
theorem B1207271 : Blo 714321 1207271 := bstep (se 1 (by rfl) ⟨905453, by rfl⟩ : syracuseStep 1207271 = 1810907) B1810907
theorem B715751 : Blo 714321 715751 := bstep (se 1 (by rfl) ⟨536813, by rfl⟩ : syracuseStep 715751 = 1073627) B1073627
theorem B2419901 : Blo 714321 2419901 := bstep (se 3 (by rfl) ⟨453731, by rfl⟩ : syracuseStep 2419901 = 907463) B907463
theorem B716063 : Blo 714321 716063 := bstep (se 1 (by rfl) ⟨537047, by rfl⟩ : syracuseStep 716063 = 1074095) B1074095
theorem B1076519 : Blo 714321 1076519 := bstep (se 1 (by rfl) ⟨807389, by rfl⟩ : syracuseStep 1076519 = 1614779) B1614779
theorem B716123 : Blo 714321 716123 := bstep (se 1 (by rfl) ⟨537092, by rfl⟩ : syracuseStep 716123 = 1074185) B1074185
theorem B716143 : Blo 714321 716143 := bstep (se 1 (by rfl) ⟨537107, by rfl⟩ : syracuseStep 716143 = 1074215) B1074215
theorem B1076603 : Blo 714321 1076603 := bstep (se 1 (by rfl) ⟨807452, by rfl⟩ : syracuseStep 1076603 = 1614905) B1614905
theorem B716199 : Blo 714321 716199 := bstep (se 1 (by rfl) ⟨537149, by rfl⟩ : syracuseStep 716199 = 1074299) B1074299
theorem B1076729 : Blo 714321 1076729 := bstep (se 2 (by rfl) ⟨403773, by rfl⟩ : syracuseStep 1076729 = 807547) B807547
theorem B716283 : Blo 714321 716283 := bstep (se 1 (by rfl) ⟨537212, by rfl⟩ : syracuseStep 716283 = 1074425) B1074425
theorem B716351 : Blo 714321 716351 := bstep (se 1 (by rfl) ⟨537263, by rfl⟩ : syracuseStep 716351 = 1074527) B1074527
theorem B716359 : Blo 714321 716359 := bstep (se 1 (by rfl) ⟨537269, by rfl⟩ : syracuseStep 716359 = 1074539) B1074539
theorem B1076831 : Blo 714321 1076831 := bstep (se 1 (by rfl) ⟨807623, by rfl⟩ : syracuseStep 1076831 = 1615247) B1615247
theorem B3632849 : Blo 714321 3632849 := bstep (se 2 (by rfl) ⟨1362318, by rfl⟩ : syracuseStep 3632849 = 2724637) B2724637
theorem B716511 : Blo 714321 716511 := bstep (se 1 (by rfl) ⟨537383, by rfl⟩ : syracuseStep 716511 = 1074767) B1074767
theorem B2715403 : Blo 714321 2715403 := bstep (se 1 (by rfl) ⟨2036552, by rfl⟩ : syracuseStep 2715403 = 4073105) B4073105
theorem B716591 : Blo 714321 716591 := bstep (se 1 (by rfl) ⟨537443, by rfl⟩ : syracuseStep 716591 = 1074887) B1074887
theorem B1077047 : Blo 714321 1077047 := bstep (se 1 (by rfl) ⟨807785, by rfl⟩ : syracuseStep 1077047 = 1615571) B1615571
theorem B3862379 : Blo 714321 3862379 := bstep (se 1 (by rfl) ⟨2896784, by rfl⟩ : syracuseStep 3862379 = 5793569) B5793569
theorem B716699 : Blo 714321 716699 := bstep (se 1 (by rfl) ⟨537524, by rfl⟩ : syracuseStep 716699 = 1075049) B1075049
theorem B716751 : Blo 714321 716751 := bstep (se 1 (by rfl) ⟨537563, by rfl⟩ : syracuseStep 716751 = 1075127) B1075127
theorem B716775 : Blo 714321 716775 := bstep (se 1 (by rfl) ⟨537581, by rfl⟩ : syracuseStep 716775 = 1075163) B1075163
theorem B2715707 : Blo 714321 2715707 := bstep (se 1 (by rfl) ⟨2036780, by rfl⟩ : syracuseStep 2715707 = 4073561) B4073561
theorem B1208425 : Blo 714321 1208425 := bstep (se 2 (by rfl) ⟨453159, by rfl⟩ : syracuseStep 1208425 = 906319) B906319
theorem B1077353 : Blo 714321 1077353 := bstep (se 2 (by rfl) ⟨404007, by rfl⟩ : syracuseStep 1077353 = 808015) B808015
theorem B717087 : Blo 714321 717087 := bstep (se 1 (by rfl) ⟨537815, by rfl⟩ : syracuseStep 717087 = 1075631) B1075631
theorem B717147 : Blo 714321 717147 := bstep (se 1 (by rfl) ⟨537860, by rfl⟩ : syracuseStep 717147 = 1075721) B1075721
theorem B717167 : Blo 714321 717167 := bstep (se 1 (by rfl) ⟨537875, by rfl⟩ : syracuseStep 717167 = 1075751) B1075751
theorem B717223 : Blo 714321 717223 := bstep (se 1 (by rfl) ⟨537917, by rfl⟩ : syracuseStep 717223 = 1075835) B1075835
theorem B14119343 : Blo 714321 14119343 := bstep (se 1 (by rfl) ⟨10589507, by rfl⟩ : syracuseStep 14119343 = 21179015) B21179015
theorem B717307 : Blo 714321 717307 := bstep (se 1 (by rfl) ⟨537980, by rfl⟩ : syracuseStep 717307 = 1075961) B1075961
theorem B717375 : Blo 714321 717375 := bstep (se 1 (by rfl) ⟨538031, by rfl⟩ : syracuseStep 717375 = 1076063) B1076063
theorem B717383 : Blo 714321 717383 := bstep (se 1 (by rfl) ⟨538037, by rfl⟩ : syracuseStep 717383 = 1076075) B1076075
theorem B1471097 : Blo 714321 1471097 := bstep (se 2 (by rfl) ⟨551661, by rfl⟩ : syracuseStep 1471097 = 1103323) B1103323
theorem B4584089 : Blo 714321 4584089 := bstep (se 2 (by rfl) ⟨1719033, by rfl⟩ : syracuseStep 4584089 = 3438067) B3438067
theorem B717535 : Blo 714321 717535 := bstep (se 1 (by rfl) ⟨538151, by rfl⟩ : syracuseStep 717535 = 1076303) B1076303
theorem B717615 : Blo 714321 717615 := bstep (se 1 (by rfl) ⟨538211, by rfl⟩ : syracuseStep 717615 = 1076423) B1076423
theorem B717723 : Blo 714321 717723 := bstep (se 1 (by rfl) ⟨538292, by rfl⟩ : syracuseStep 717723 = 1076585) B1076585
theorem B717775 : Blo 714321 717775 := bstep (se 1 (by rfl) ⟨538331, by rfl⟩ : syracuseStep 717775 = 1076663) B1076663
theorem B717799 : Blo 714321 717799 := bstep (se 1 (by rfl) ⟨538349, by rfl⟩ : syracuseStep 717799 = 1076699) B1076699
theorem B718111 : Blo 714321 718111 := bstep (se 1 (by rfl) ⟨538583, by rfl⟩ : syracuseStep 718111 = 1077167) B1077167
theorem B718171 : Blo 714321 718171 := bstep (se 1 (by rfl) ⟨538628, by rfl⟩ : syracuseStep 718171 = 1077257) B1077257
theorem B718191 : Blo 714321 718191 := bstep (se 1 (by rfl) ⟨538643, by rfl⟩ : syracuseStep 718191 = 1077287) B1077287
theorem B718247 : Blo 714321 718247 := bstep (se 1 (by rfl) ⟨538685, by rfl⟩ : syracuseStep 718247 = 1077371) B1077371
theorem B816583 : Blo 714321 816583 := bstep (se 1 (by rfl) ⟨612437, by rfl⟩ : syracuseStep 816583 = 1224875) B1224875
theorem B7730635 : Blo 714321 7730635 := bstep (se 1 (by rfl) ⟨5797976, by rfl⟩ : syracuseStep 7730635 = 11595953) B11595953
theorem B3274427 : Blo 714321 3274427 := bstep (se 1 (by rfl) ⟨2455820, by rfl⟩ : syracuseStep 3274427 = 4911641) B4911641
theorem B1210153 : Blo 714321 1210153 := bstep (se 2 (by rfl) ⟨453807, by rfl⟩ : syracuseStep 1210153 = 907615) B907615
theorem B1144633 : Blo 714321 1144633 := bstep (se 2 (by rfl) ⟨429237, by rfl⟩ : syracuseStep 1144633 = 858475) B858475
theorem B2422817 : Blo 714321 2422817 := bstep (se 2 (by rfl) ⟨908556, by rfl⟩ : syracuseStep 2422817 = 1817113) B1817113
theorem B3635279 : Blo 714321 3635279 := bstep (se 1 (by rfl) ⟨2726459, by rfl⟩ : syracuseStep 3635279 = 5452919) B5452919
theorem B7076119 : Blo 714321 7076119 := bstep (se 1 (by rfl) ⟨5307089, by rfl⟩ : syracuseStep 7076119 = 10614179) B10614179
theorem B1210943 : Blo 714321 1210943 := bstep (se 1 (by rfl) ⟨908207, by rfl⟩ : syracuseStep 1210943 = 1816415) B1816415
theorem B10320659 : Blo 714321 10320659 := bstep (se 1 (by rfl) ⟨7740494, by rfl⟩ : syracuseStep 10320659 = 15480989) B15480989
theorem B5176219 : Blo 714321 5176219 := bstep (se 1 (by rfl) ⟨3882164, by rfl⟩ : syracuseStep 5176219 = 7764329) B7764329
theorem B7371899 : Blo 714321 7371899 := bstep (se 1 (by rfl) ⟨5528924, by rfl⟩ : syracuseStep 7371899 = 11057849) B11057849
theorem B3636413 : Blo 714321 3636413 := bstep (se 3 (by rfl) ⟨681827, by rfl⟩ : syracuseStep 3636413 = 1363655) B1363655
theorem B1211611 : Blo 714321 1211611 := bstep (se 1 (by rfl) ⟨908708, by rfl⟩ : syracuseStep 1211611 = 1817417) B1817417
theorem B104627447 : Blo 714321 104627447 := bstep (se 1 (by rfl) ⟨78470585, by rfl⟩ : syracuseStep 104627447 = 156941171) B156941171
theorem B1768735 : Blo 714321 1768735 := bstep (se 1 (by rfl) ⟨1326551, by rfl⟩ : syracuseStep 1768735 = 2653103) B2653103
theorem B1637671 : Blo 714321 1637671 := bstep (se 1 (by rfl) ⟨1228253, by rfl⟩ : syracuseStep 1637671 = 2456507) B2456507
theorem B2588269 : Blo 714321 2588269 := bstep (se 3 (by rfl) ⟨485300, by rfl⟩ : syracuseStep 2588269 = 970601) B970601
theorem B7732883 : Blo 714321 7732883 := bstep (se 1 (by rfl) ⟨5799662, by rfl⟩ : syracuseStep 7732883 = 11599325) B11599325
theorem B7765753 : Blo 714321 7765753 := bstep (se 2 (by rfl) ⟨2912157, by rfl⟩ : syracuseStep 7765753 = 5824315) B5824315
theorem B2719777 : Blo 714321 2719777 := bstep (se 2 (by rfl) ⟨1019916, by rfl⟩ : syracuseStep 2719777 = 2039833) B2039833
theorem B4129231 : Blo 714321 4129231 := bstep (se 1 (by rfl) ⟨3096923, by rfl⟩ : syracuseStep 4129231 = 6193847) B6193847
theorem B18318311 : Blo 714321 18318311 := bstep (se 1 (by rfl) ⟨13738733, by rfl⟩ : syracuseStep 18318311 = 27477467) B27477467
theorem B16548887 : Blo 714321 16548887 := bstep (se 1 (by rfl) ⟨12411665, by rfl⟩ : syracuseStep 16548887 = 24823331) B24823331
theorem B1311851 : Blo 714321 1311851 := bstep (se 1 (by rfl) ⟨983888, by rfl⟩ : syracuseStep 1311851 = 1967777) B1967777
theorem B1934543 : Blo 714321 1934543 := bstep (se 1 (by rfl) ⟨1450907, by rfl⟩ : syracuseStep 1934543 = 2901815) B2901815
theorem B5440769 : Blo 714321 5440769 := bstep (se 2 (by rfl) ⟨2040288, by rfl⟩ : syracuseStep 5440769 = 4080577) B4080577
theorem B2295211 : Blo 714321 2295211 := bstep (se 1 (by rfl) ⟨1721408, by rfl⟩ : syracuseStep 2295211 = 3442817) B3442817
theorem B6129067 : Blo 714321 6129067 := bstep (se 1 (by rfl) ⟨4596800, by rfl⟩ : syracuseStep 6129067 = 9193601) B9193601
theorem B1017679 : Blo 714321 1017679 := bstep (se 1 (by rfl) ⟨763259, by rfl⟩ : syracuseStep 1017679 = 1526519) B1526519
theorem B2296043 : Blo 714321 2296043 := bstep (se 1 (by rfl) ⟨1722032, by rfl⟩ : syracuseStep 2296043 = 3444065) B3444065
theorem B1607975 : Blo 714321 1607975 := bstep (se 1 (by rfl) ⟨1205981, by rfl⟩ : syracuseStep 1607975 = 2411963) B2411963
theorem B1607993 : Blo 714321 1607993 := bstep (se 2 (by rfl) ⟨602997, by rfl⟩ : syracuseStep 1607993 = 1205995) B1205995
theorem B7736309 : Blo 714321 7736309 := bstep (se 5 (by rfl) ⟨362639, by rfl⟩ : syracuseStep 7736309 = 725279) B725279
theorem B1150175 : Blo 714321 1150175 := bstep (se 1 (by rfl) ⟨862631, by rfl⟩ : syracuseStep 1150175 = 1725263) B1725263
theorem B1609289 : Blo 714321 1609289 := bstep (se 2 (by rfl) ⟨603483, by rfl⟩ : syracuseStep 1609289 = 1206967) B1206967
theorem B2723665 : Blo 714321 2723665 := bstep (se 2 (by rfl) ⟨1021374, by rfl⟩ : syracuseStep 2723665 = 2042749) B2042749
theorem B1019803 : Blo 714321 1019803 := bstep (se 1 (by rfl) ⟨764852, by rfl⟩ : syracuseStep 1019803 = 1529705) B1529705
theorem B7737727 : Blo 714321 7737727 := bstep (se 1 (by rfl) ⟨5803295, by rfl⟩ : syracuseStep 7737727 = 11606591) B11606591
theorem B1020367 : Blo 714321 1020367 := bstep (se 1 (by rfl) ⟨765275, by rfl⟩ : syracuseStep 1020367 = 1530551) B1530551
theorem B13734359 : Blo 714321 13734359 := bstep (se 1 (by rfl) ⟨10300769, by rfl⟩ : syracuseStep 13734359 = 20601539) B20601539
theorem B2036303 : Blo 714321 2036303 := bstep (se 1 (by rfl) ⟨1527227, by rfl⟩ : syracuseStep 2036303 = 3054455) B3054455
theorem B2757199 : Blo 714321 2757199 := bstep (se 1 (by rfl) ⟨2067899, by rfl⟩ : syracuseStep 2757199 = 4135799) B4135799
theorem B2724455 : Blo 714321 2724455 := bstep (se 1 (by rfl) ⟨2043341, by rfl⟩ : syracuseStep 2724455 = 4086683) B4086683
theorem B1610747 : Blo 714321 1610747 := bstep (se 1 (by rfl) ⟨1208060, by rfl⟩ : syracuseStep 1610747 = 2416121) B2416121
theorem B2069513 : Blo 714321 2069513 := bstep (se 2 (by rfl) ⟨776067, by rfl⟩ : syracuseStep 2069513 = 1552135) B1552135
theorem B1021033 : Blo 714321 1021033 := bstep (se 2 (by rfl) ⟨382887, by rfl⟩ : syracuseStep 1021033 = 765775) B765775
theorem B2331787 : Blo 714321 2331787 := bstep (se 1 (by rfl) ⟨1748840, by rfl⟩ : syracuseStep 2331787 = 3497681) B3497681
theorem B1610927 : Blo 714321 1610927 := bstep (se 1 (by rfl) ⟨1208195, by rfl⟩ : syracuseStep 1610927 = 2416391) B2416391
theorem B1610963 : Blo 714321 1610963 := bstep (se 1 (by rfl) ⟨1208222, by rfl⟩ : syracuseStep 1610963 = 2416445) B2416445
theorem B2037089 : Blo 714321 2037089 := bstep (se 2 (by rfl) ⟨763908, by rfl⟩ : syracuseStep 2037089 = 1527817) B1527817
theorem B1611233 : Blo 714321 1611233 := bstep (se 2 (by rfl) ⟨604212, by rfl⟩ : syracuseStep 1611233 = 1208425) B1208425
theorem B2037419 : Blo 714321 2037419 := bstep (se 1 (by rfl) ⟨1528064, by rfl⟩ : syracuseStep 2037419 = 3056129) B3056129
theorem B4593419 : Blo 714321 4593419 := bstep (se 1 (by rfl) ⟨3445064, by rfl⟩ : syracuseStep 4593419 = 6890129) B6890129
theorem B1087463 : Blo 714321 1087463 := bstep (se 1 (by rfl) ⟨815597, by rfl⟩ : syracuseStep 1087463 = 1631195) B1631195
theorem B2725913 : Blo 714321 2725913 := bstep (se 2 (by rfl) ⟨1022217, by rfl⟩ : syracuseStep 2725913 = 2044435) B2044435
theorem B7739459 : Blo 714321 7739459 := bstep (se 1 (by rfl) ⟨5804594, by rfl⟩ : syracuseStep 7739459 = 11609189) B11609189
theorem B1808527 : Blo 714321 1808527 := bstep (se 1 (by rfl) ⟨1356395, by rfl⟩ : syracuseStep 1808527 = 2712791) B2712791
theorem B10459601 : Blo 714321 10459601 := bstep (se 2 (by rfl) ⟨3922350, by rfl⟩ : syracuseStep 10459601 = 7844701) B7844701
theorem B1022491 : Blo 714321 1022491 := bstep (se 1 (by rfl) ⟨766868, by rfl⟩ : syracuseStep 1022491 = 1533737) B1533737
theorem B5315371 : Blo 714321 5315371 := bstep (se 1 (by rfl) ⟨3986528, by rfl⟩ : syracuseStep 5315371 = 7973057) B7973057
theorem B3054419 : Blo 714321 3054419 := bstep (se 1 (by rfl) ⟨2290814, by rfl⟩ : syracuseStep 3054419 = 4581629) B4581629
theorem B5446601 : Blo 714321 5446601 := bstep (se 2 (by rfl) ⟨2042475, by rfl⟩ : syracuseStep 5446601 = 4084951) B4084951
theorem B1809449 : Blo 714321 1809449 := bstep (se 2 (by rfl) ⟨678543, by rfl⟩ : syracuseStep 1809449 = 1357087) B1357087
theorem B1809479 : Blo 714321 1809479 := bstep (se 1 (by rfl) ⟨1357109, by rfl⟩ : syracuseStep 1809479 = 2714219) B2714219
theorem B1612871 : Blo 714321 1612871 := bstep (se 1 (by rfl) ⟨1209653, by rfl⟩ : syracuseStep 1612871 = 2419307) B2419307
theorem B1088777 : Blo 714321 1088777 := bstep (se 2 (by rfl) ⟨408291, by rfl⟩ : syracuseStep 1088777 = 816583) B816583
theorem B18357677 : Blo 714321 18357677 := bstep (se 3 (by rfl) ⟨3442064, by rfl⟩ : syracuseStep 18357677 = 6884129) B6884129
theorem B1613267 : Blo 714321 1613267 := bstep (se 1 (by rfl) ⟨1209950, by rfl⟩ : syracuseStep 1613267 = 2419901) B2419901
theorem B1613537 : Blo 714321 1613537 := bstep (se 2 (by rfl) ⟨605076, by rfl⟩ : syracuseStep 1613537 = 1210153) B1210153
theorem B2203517 : Blo 714321 2203517 := bstep (se 3 (by rfl) ⟨413159, by rfl⟩ : syracuseStep 2203517 = 826319) B826319
theorem B1810471 : Blo 714321 1810471 := bstep (se 1 (by rfl) ⟨1357853, by rfl⟩ : syracuseStep 1810471 = 2715707) B2715707
theorem B6103097 : Blo 714321 6103097 := bstep (se 2 (by rfl) ⟨2288661, by rfl⟩ : syracuseStep 6103097 = 4577323) B4577323
theorem B9412895 : Blo 714321 9412895 := bstep (se 1 (by rfl) ⟨7059671, by rfl⟩ : syracuseStep 9412895 = 14119343) B14119343
theorem B3056059 : Blo 714321 3056059 := bstep (se 1 (by rfl) ⟨2292044, by rfl⟩ : syracuseStep 3056059 = 4584089) B4584089
theorem B21504727 : Blo 714321 21504727 := bstep (se 1 (by rfl) ⟨16128545, by rfl⟩ : syracuseStep 21504727 = 32257091) B32257091
theorem B12264695 : Blo 714321 12264695 := bstep (se 1 (by rfl) ⟨9198521, by rfl⟩ : syracuseStep 12264695 = 18397043) B18397043
theorem B1615211 : Blo 714321 1615211 := bstep (se 1 (by rfl) ⟨1211408, by rfl⟩ : syracuseStep 1615211 = 2422817) B2422817
theorem B2041337 : Blo 714321 2041337 := bstep (se 2 (by rfl) ⟨765501, by rfl⟩ : syracuseStep 2041337 = 1531003) B1531003
theorem B1615481 : Blo 714321 1615481 := bstep (se 2 (by rfl) ⟨605805, by rfl⟩ : syracuseStep 1615481 = 1211611) B1211611
theorem B2041679 : Blo 714321 2041679 := bstep (se 1 (by rfl) ⟨1531259, by rfl⟩ : syracuseStep 2041679 = 3062519) B3062519
theorem B3451025 : Blo 714321 3451025 := bstep (se 2 (by rfl) ⟨1294134, by rfl⟩ : syracuseStep 3451025 = 2588269) B2588269
theorem B5155255 : Blo 714321 5155255 := bstep (se 1 (by rfl) ⟨3866441, by rfl⟩ : syracuseStep 5155255 = 7732883) B7732883
theorem B13806395 : Blo 714321 13806395 := bstep (se 1 (by rfl) ⟨10354796, by rfl⟩ : syracuseStep 13806395 = 20709593) B20709593
theorem B46476179 : Blo 714321 46476179 := bstep (se 1 (by rfl) ⟨34857134, by rfl⟩ : syracuseStep 46476179 = 69714269) B69714269
theorem B2206817 : Blo 714321 2206817 := bstep (se 2 (by rfl) ⟨827556, by rfl⟩ : syracuseStep 2206817 = 1655113) B1655113
theorem B2042977 : Blo 714321 2042977 := bstep (se 2 (by rfl) ⟨766116, by rfl⟩ : syracuseStep 2042977 = 1532233) B1532233
theorem B8170631 : Blo 714321 8170631 := bstep (se 1 (by rfl) ⟨6127973, by rfl⟩ : syracuseStep 8170631 = 12255947) B12255947
theorem B2043103 : Blo 714321 2043103 := bstep (se 1 (by rfl) ⟨1532327, by rfl⟩ : syracuseStep 2043103 = 3064655) B3064655
theorem B2239721 : Blo 714321 2239721 := bstep (se 2 (by rfl) ⟨839895, by rfl⟩ : syracuseStep 2239721 = 1679791) B1679791
theorem B2043319 : Blo 714321 2043319 := bstep (se 1 (by rfl) ⟨1532489, by rfl⟩ : syracuseStep 2043319 = 3064979) B3064979
theorem B1289903 : Blo 714321 1289903 := bstep (se 1 (by rfl) ⟨967427, by rfl⟩ : syracuseStep 1289903 = 1934855) B1934855
theorem B26095283 : Blo 714321 26095283 := bstep (se 1 (by rfl) ⟨19571462, by rfl⟩ : syracuseStep 26095283 = 39142925) B39142925
theorem B6205177 : Blo 714321 6205177 := bstep (se 2 (by rfl) ⟨2326941, by rfl⟩ : syracuseStep 6205177 = 4653883) B4653883
theorem B17018909 : Blo 714321 17018909 := bstep (se 3 (by rfl) ⟨3191045, by rfl⟩ : syracuseStep 17018909 = 6382091) B6382091
theorem B5157391 : Blo 714321 5157391 := bstep (se 1 (by rfl) ⟨3868043, by rfl⟩ : syracuseStep 5157391 = 7736087) B7736087
theorem B4076203 : Blo 714321 4076203 := bstep (se 1 (by rfl) ⟨3057152, by rfl⟩ : syracuseStep 4076203 = 6114305) B6114305
theorem B16495433 : Blo 714321 16495433 := bstep (se 2 (by rfl) ⟨6185787, by rfl⟩ : syracuseStep 16495433 = 12371575) B12371575
theorem B3060605 : Blo 714321 3060605 := bstep (se 3 (by rfl) ⟨573863, by rfl⟩ : syracuseStep 3060605 = 1147727) B1147727
theorem B1225639 : Blo 714321 1225639 := bstep (se 1 (by rfl) ⟨919229, by rfl⟩ : syracuseStep 1225639 = 1838459) B1838459
theorem B1291439 : Blo 714321 1291439 := bstep (se 1 (by rfl) ⟨968579, by rfl⟩ : syracuseStep 1291439 = 1937159) B1937159
theorem B3880457 : Blo 714321 3880457 := bstep (se 2 (by rfl) ⟨1455171, by rfl⟩ : syracuseStep 3880457 = 2910343) B2910343
theorem B7353991 : Blo 714321 7353991 := bstep (se 1 (by rfl) ⟨5515493, by rfl⟩ : syracuseStep 7353991 = 11030987) B11030987
theorem B16562015 : Blo 714321 16562015 := bstep (se 1 (by rfl) ⟨12421511, by rfl⟩ : syracuseStep 16562015 = 24843023) B24843023
theorem B3618755 : Blo 714321 3618755 := bstep (se 1 (by rfl) ⟨2714066, by rfl⟩ : syracuseStep 3618755 = 5428133) B5428133
theorem B3619079 : Blo 714321 3619079 := bstep (se 1 (by rfl) ⟨2714309, by rfl⟩ : syracuseStep 3619079 = 5428619) B5428619
theorem B4077935 : Blo 714321 4077935 := bstep (se 1 (by rfl) ⟨3058451, by rfl⟩ : syracuseStep 4077935 = 6116903) B6116903
theorem B9812339 : Blo 714321 9812339 := bstep (se 1 (by rfl) ⟨7359254, by rfl⟩ : syracuseStep 9812339 = 14718509) B14718509
theorem B1358203 : Blo 714321 1358203 := bstep (se 1 (by rfl) ⟨1018652, by rfl⟩ : syracuseStep 1358203 = 2037305) B2037305
theorem B10598951 : Blo 714321 10598951 := bstep (se 1 (by rfl) ⟨7949213, by rfl⟩ : syracuseStep 10598951 = 15898427) B15898427
theorem B5519929 : Blo 714321 5519929 := bstep (se 2 (by rfl) ⟨2069973, by rfl⟩ : syracuseStep 5519929 = 4139947) B4139947
theorem B1817225 : Blo 714321 1817225 := bstep (se 2 (by rfl) ⟨681459, by rfl⟩ : syracuseStep 1817225 = 1362919) B1362919
theorem B1719265 : Blo 714321 1719265 := bstep (se 2 (by rfl) ⟨644724, by rfl⟩ : syracuseStep 1719265 = 1289449) B1289449
theorem B1359031 : Blo 714321 1359031 := bstep (se 1 (by rfl) ⟨1019273, by rfl⟩ : syracuseStep 1359031 = 2038547) B2038547
theorem B4144613 : Blo 714321 4144613 := bstep (se 4 (by rfl) ⟨388557, by rfl⟩ : syracuseStep 4144613 = 777115) B777115
theorem B1359335 : Blo 714321 1359335 := bstep (se 1 (by rfl) ⟨1019501, by rfl⟩ : syracuseStep 1359335 = 2039003) B2039003
theorem B3620537 : Blo 714321 3620537 := bstep (se 2 (by rfl) ⟨1357701, by rfl⟩ : syracuseStep 3620537 = 2715403) B2715403
theorem B1294235 : Blo 714321 1294235 := bstep (se 1 (by rfl) ⟨970676, by rfl⟩ : syracuseStep 1294235 = 1941353) B1941353
theorem B80724599 : Blo 714321 80724599 := bstep (se 1 (by rfl) ⟨60543449, by rfl⟩ : syracuseStep 80724599 = 121086899) B121086899
theorem B803695 : Blo 714321 803695 := bstep (se 1 (by rfl) ⟨602771, by rfl⟩ : syracuseStep 803695 = 1205543) B1205543
theorem B967735 : Blo 714321 967735 := bstep (se 1 (by rfl) ⟨725801, by rfl⟩ : syracuseStep 967735 = 1451603) B1451603
theorem B10307513 : Blo 714321 10307513 := bstep (se 2 (by rfl) ⟨3865317, by rfl⟩ : syracuseStep 10307513 = 7730635) B7730635
theorem B1361863 : Blo 714321 1361863 := bstep (se 1 (by rfl) ⟨1021397, by rfl⟩ : syracuseStep 1361863 = 2042795) B2042795
theorem B804847 : Blo 714321 804847 := bstep (se 1 (by rfl) ⟨603635, by rfl⟩ : syracuseStep 804847 = 1207271) B1207271
theorem B1526177 : Blo 714321 1526177 := bstep (se 2 (by rfl) ⟨572316, by rfl⟩ : syracuseStep 1526177 = 1144633) B1144633
theorem B2574919 : Blo 714321 2574919 := bstep (se 1 (by rfl) ⟨1931189, by rfl⟩ : syracuseStep 2574919 = 3862379) B3862379
theorem B15452795 : Blo 714321 15452795 := bstep (se 1 (by rfl) ⟨11589596, by rfl⟩ : syracuseStep 15452795 = 23179193) B23179193
theorem B904375 : Blo 714321 904375 := bstep (se 1 (by rfl) ⟨678281, by rfl⟩ : syracuseStep 904375 = 1356563) B1356563
theorem B2411801 : Blo 714321 2411801 := bstep (se 2 (by rfl) ⟨904425, by rfl⟩ : syracuseStep 2411801 = 1808851) B1808851
theorem B2411855 : Blo 714321 2411855 := bstep (se 1 (by rfl) ⟨1808891, by rfl⟩ : syracuseStep 2411855 = 3617783) B3617783
theorem B2903465 : Blo 714321 2903465 := bstep (se 2 (by rfl) ⟨1088799, by rfl⟩ : syracuseStep 2903465 = 2177599) B2177599
theorem B2182951 : Blo 714321 2182951 := bstep (se 1 (by rfl) ⟨1637213, by rfl⟩ : syracuseStep 2182951 = 3274427) B3274427
theorem B6901625 : Blo 714321 6901625 := bstep (se 2 (by rfl) ⟨2588109, by rfl⟩ : syracuseStep 6901625 = 5176219) B5176219
theorem B807295 : Blo 714321 807295 := bstep (se 1 (by rfl) ⟨605471, by rfl⟩ : syracuseStep 807295 = 1210943) B1210943
theorem B2183561 : Blo 714321 2183561 := bstep (se 2 (by rfl) ⟨818835, by rfl⟩ : syracuseStep 2183561 = 1637671) B1637671
theorem B2609759 : Blo 714321 2609759 := bstep (se 1 (by rfl) ⟨1957319, by rfl⟩ : syracuseStep 2609759 = 3914639) B3914639
theorem B2413151 : Blo 714321 2413151 := bstep (se 1 (by rfl) ⟨1809863, by rfl⟩ : syracuseStep 2413151 = 3619727) B3619727
theorem B39703159 : Blo 714321 39703159 := bstep (se 1 (by rfl) ⟨29777369, by rfl⟩ : syracuseStep 39703159 = 59554739) B59554739
theorem B2904893 : Blo 714321 2904893 := bstep (se 3 (by rfl) ⟨544667, by rfl⟩ : syracuseStep 2904893 = 1089335) B1089335
theorem B69751631 : Blo 714321 69751631 := bstep (se 1 (by rfl) ⟨52313723, by rfl⟩ : syracuseStep 69751631 = 104627447) B104627447
theorem B3527675 : Blo 714321 3527675 := bstep (se 1 (by rfl) ⟨2645756, by rfl⟩ : syracuseStep 3527675 = 5291513) B5291513
theorem B8279117 : Blo 714321 8279117 := bstep (se 3 (by rfl) ⟨1552334, by rfl⟩ : syracuseStep 8279117 = 3104669) B3104669
theorem B19650059 : Blo 714321 19650059 := bstep (se 1 (by rfl) ⟨14737544, by rfl⟩ : syracuseStep 19650059 = 29475089) B29475089
theorem B26105489 : Blo 714321 26105489 := bstep (se 2 (by rfl) ⟨9789558, by rfl⟩ : syracuseStep 26105489 = 19579117) B19579117
theorem B2414393 : Blo 714321 2414393 := bstep (se 2 (by rfl) ⟨905397, by rfl⟩ : syracuseStep 2414393 = 1810795) B1810795
theorem B2414555 : Blo 714321 2414555 := bstep (se 1 (by rfl) ⟨1810916, by rfl⟩ : syracuseStep 2414555 = 3621833) B3621833
theorem B10344647 : Blo 714321 10344647 := bstep (se 1 (by rfl) ⟨7758485, by rfl⟩ : syracuseStep 10344647 = 15516971) B15516971
theorem B2414825 : Blo 714321 2414825 := bstep (se 2 (by rfl) ⟨905559, by rfl⟩ : syracuseStep 2414825 = 1811119) B1811119
theorem B4086227 : Blo 714321 4086227 := bstep (se 1 (by rfl) ⟨3064670, by rfl⟩ : syracuseStep 4086227 = 6129341) B6129341
theorem B1071647 : Blo 714321 1071647 := bstep (se 1 (by rfl) ⟨803735, by rfl⟩ : syracuseStep 1071647 = 1607471) B1607471
theorem B4086409 : Blo 714321 4086409 := bstep (se 2 (by rfl) ⟨1532403, by rfl⟩ : syracuseStep 4086409 = 3064807) B3064807
theorem B2415257 : Blo 714321 2415257 := bstep (se 2 (by rfl) ⟨905721, by rfl⟩ : syracuseStep 2415257 = 1811443) B1811443
theorem B4479709 : Blo 714321 4479709 := bstep (se 3 (by rfl) ⟨839945, by rfl⟩ : syracuseStep 4479709 = 1679891) B1679891
theorem B1072031 : Blo 714321 1072031 := bstep (se 1 (by rfl) ⟨804023, by rfl⟩ : syracuseStep 1072031 = 1608047) B1608047
theorem B1072079 : Blo 714321 1072079 := bstep (se 1 (by rfl) ⟨804059, by rfl⟩ : syracuseStep 1072079 = 1608119) B1608119
theorem B1072169 : Blo 714321 1072169 := bstep (se 2 (by rfl) ⟨402063, by rfl⟩ : syracuseStep 1072169 = 804127) B804127
theorem B1072175 : Blo 714321 1072175 := bstep (se 1 (by rfl) ⟨804131, by rfl⟩ : syracuseStep 1072175 = 1608263) B1608263
theorem B1072199 : Blo 714321 1072199 := bstep (se 1 (by rfl) ⟨804149, by rfl⟩ : syracuseStep 1072199 = 1608299) B1608299
theorem B8150219 : Blo 714321 8150219 := bstep (se 1 (by rfl) ⟨6112664, by rfl⟩ : syracuseStep 8150219 = 12225329) B12225329
theorem B1072463 : Blo 714321 1072463 := bstep (se 1 (by rfl) ⟨804347, by rfl⟩ : syracuseStep 1072463 = 1608695) B1608695
theorem B1629551 : Blo 714321 1629551 := bstep (se 1 (by rfl) ⟨1222163, by rfl⟩ : syracuseStep 1629551 = 2444327) B2444327
theorem B1072553 : Blo 714321 1072553 := bstep (se 2 (by rfl) ⟨402207, by rfl⟩ : syracuseStep 1072553 = 804415) B804415
theorem B1072703 : Blo 714321 1072703 := bstep (se 1 (by rfl) ⟨804527, by rfl⟩ : syracuseStep 1072703 = 1609055) B1609055
theorem B1072967 : Blo 714321 1072967 := bstep (se 1 (by rfl) ⟨804725, by rfl⟩ : syracuseStep 1072967 = 1609451) B1609451
theorem B2580311 : Blo 714321 2580311 := bstep (se 1 (by rfl) ⟨1935233, by rfl⟩ : syracuseStep 2580311 = 3870467) B3870467
theorem B1073051 : Blo 714321 1073051 := bstep (se 1 (by rfl) ⟨804788, by rfl⟩ : syracuseStep 1073051 = 1609577) B1609577
theorem B1531943 : Blo 714321 1531943 := bstep (se 1 (by rfl) ⟨1148957, by rfl⟩ : syracuseStep 1531943 = 2297915) B2297915
theorem B4087867 : Blo 714321 4087867 := bstep (se 1 (by rfl) ⟨3065900, by rfl⟩ : syracuseStep 4087867 = 6131801) B6131801
theorem B1532191 : Blo 714321 1532191 := bstep (se 1 (by rfl) ⟨1149143, by rfl⟩ : syracuseStep 1532191 = 2298287) B2298287
theorem B1073615 : Blo 714321 1073615 := bstep (se 1 (by rfl) ⟨805211, by rfl⟩ : syracuseStep 1073615 = 1610423) B1610423
theorem B1073657 : Blo 714321 1073657 := bstep (se 2 (by rfl) ⟨402621, by rfl⟩ : syracuseStep 1073657 = 805243) B805243
theorem B2417147 : Blo 714321 2417147 := bstep (se 1 (by rfl) ⟨1812860, by rfl⟩ : syracuseStep 2417147 = 3625721) B3625721
theorem B4088393 : Blo 714321 4088393 := bstep (se 2 (by rfl) ⟨1533147, by rfl⟩ : syracuseStep 4088393 = 3066295) B3066295
theorem B1073759 : Blo 714321 1073759 := bstep (se 1 (by rfl) ⟨805319, by rfl⟩ : syracuseStep 1073759 = 1610639) B1610639
theorem B2417417 : Blo 714321 2417417 := bstep (se 2 (by rfl) ⟨906531, by rfl⟩ : syracuseStep 2417417 = 1813063) B1813063
theorem B18834221 : Blo 714321 18834221 := bstep (se 3 (by rfl) ⟨3531416, by rfl⟩ : syracuseStep 18834221 = 7062833) B7062833
theorem B1074239 : Blo 714321 1074239 := bstep (se 1 (by rfl) ⟨805679, by rfl⟩ : syracuseStep 1074239 = 1611359) B1611359
theorem B1074281 : Blo 714321 1074281 := bstep (se 2 (by rfl) ⟨402855, by rfl⟩ : syracuseStep 1074281 = 805711) B805711
theorem B2450621 : Blo 714321 2450621 := bstep (se 3 (by rfl) ⟨459491, by rfl⟩ : syracuseStep 2450621 = 918983) B918983
theorem B1205455 : Blo 714321 1205455 := bstep (se 1 (by rfl) ⟨904091, by rfl⟩ : syracuseStep 1205455 = 1808183) B1808183
theorem B1074383 : Blo 714321 1074383 := bstep (se 1 (by rfl) ⟨805787, by rfl⟩ : syracuseStep 1074383 = 1611575) B1611575
theorem B1074587 : Blo 714321 1074587 := bstep (se 1 (by rfl) ⟨805940, by rfl⟩ : syracuseStep 1074587 = 1611881) B1611881
theorem B4089325 : Blo 714321 4089325 := bstep (se 3 (by rfl) ⟨766748, by rfl⟩ : syracuseStep 4089325 = 1533497) B1533497
theorem B2418173 : Blo 714321 2418173 := bstep (se 3 (by rfl) ⟨453407, by rfl⟩ : syracuseStep 2418173 = 906815) B906815
theorem B714351 : Blo 714321 714351 := bstep (se 1 (by rfl) ⟨535763, by rfl⟩ : syracuseStep 714351 = 1071527) B1071527
theorem B1074809 : Blo 714321 1074809 := bstep (se 2 (by rfl) ⟨403053, by rfl⟩ : syracuseStep 1074809 = 806107) B806107
theorem B714407 : Blo 714321 714407 := bstep (se 1 (by rfl) ⟨535805, by rfl⟩ : syracuseStep 714407 = 1071611) B1071611
theorem B1074911 : Blo 714321 1074911 := bstep (se 1 (by rfl) ⟨806183, by rfl⟩ : syracuseStep 1074911 = 1612367) B1612367
theorem B714491 : Blo 714321 714491 := bstep (se 1 (by rfl) ⟨535868, by rfl⟩ : syracuseStep 714491 = 1071737) B1071737
theorem B714527 : Blo 714321 714527 := bstep (se 1 (by rfl) ⟨535895, by rfl⟩ : syracuseStep 714527 = 1071791) B1071791
theorem B714559 : Blo 714321 714559 := bstep (se 1 (by rfl) ⟨535919, by rfl⟩ : syracuseStep 714559 = 1071839) B1071839
theorem B1075007 : Blo 714321 1075007 := bstep (se 1 (by rfl) ⟨806255, by rfl⟩ : syracuseStep 1075007 = 1612511) B1612511
theorem B1075175 : Blo 714321 1075175 := bstep (se 1 (by rfl) ⟨806381, by rfl⟩ : syracuseStep 1075175 = 1612763) B1612763
theorem B714735 : Blo 714321 714735 := bstep (se 1 (by rfl) ⟨536051, by rfl⟩ : syracuseStep 714735 = 1072103) B1072103
theorem B1206265 : Blo 714321 1206265 := bstep (se 2 (by rfl) ⟨452349, by rfl⟩ : syracuseStep 1206265 = 904699) B904699
theorem B1075193 : Blo 714321 1075193 := bstep (se 2 (by rfl) ⟨403197, by rfl⟩ : syracuseStep 1075193 = 806395) B806395
theorem B19589201 : Blo 714321 19589201 := bstep (se 2 (by rfl) ⟨7345950, by rfl⟩ : syracuseStep 19589201 = 14691901) B14691901
theorem B1075295 : Blo 714321 1075295 := bstep (se 1 (by rfl) ⟨806471, by rfl⟩ : syracuseStep 1075295 = 1612943) B1612943
theorem B3631229 : Blo 714321 3631229 := bstep (se 3 (by rfl) ⟨680855, by rfl⟩ : syracuseStep 3631229 = 1361711) B1361711
theorem B714907 : Blo 714321 714907 := bstep (se 1 (by rfl) ⟨536180, by rfl⟩ : syracuseStep 714907 = 1072361) B1072361
theorem B1206427 : Blo 714321 1206427 := bstep (se 1 (by rfl) ⟨904820, by rfl⟩ : syracuseStep 1206427 = 1809641) B1809641
theorem B1075355 : Blo 714321 1075355 := bstep (se 1 (by rfl) ⟨806516, by rfl⟩ : syracuseStep 1075355 = 1613033) B1613033
theorem B714943 : Blo 714321 714943 := bstep (se 1 (by rfl) ⟨536207, by rfl⟩ : syracuseStep 714943 = 1072415) B1072415
theorem B1075391 : Blo 714321 1075391 := bstep (se 1 (by rfl) ⟨806543, by rfl⟩ : syracuseStep 1075391 = 1613087) B1613087
theorem B1075433 : Blo 714321 1075433 := bstep (se 2 (by rfl) ⟨403287, by rfl⟩ : syracuseStep 1075433 = 806575) B806575
theorem B1206535 : Blo 714321 1206535 := bstep (se 1 (by rfl) ⟨904901, by rfl⟩ : syracuseStep 1206535 = 1809803) B1809803
theorem B2418983 : Blo 714321 2418983 := bstep (se 1 (by rfl) ⟨1814237, by rfl⟩ : syracuseStep 2418983 = 3628475) B3628475
theorem B1206569 : Blo 714321 1206569 := bstep (se 2 (by rfl) ⟨452463, by rfl⟩ : syracuseStep 1206569 = 904927) B904927
theorem B715055 : Blo 714321 715055 := bstep (se 1 (by rfl) ⟨536291, by rfl⟩ : syracuseStep 715055 = 1072583) B1072583
theorem B715291 : Blo 714321 715291 := bstep (se 1 (by rfl) ⟨536468, by rfl⟩ : syracuseStep 715291 = 1072937) B1072937
theorem B1075739 : Blo 714321 1075739 := bstep (se 1 (by rfl) ⟨806804, by rfl⟩ : syracuseStep 1075739 = 1613609) B1613609
theorem B715295 : Blo 714321 715295 := bstep (se 1 (by rfl) ⟨536471, by rfl⟩ : syracuseStep 715295 = 1072943) B1072943
theorem B1075817 : Blo 714321 1075817 := bstep (se 2 (by rfl) ⟨403431, by rfl⟩ : syracuseStep 1075817 = 806863) B806863
theorem B715611 : Blo 714321 715611 := bstep (se 1 (by rfl) ⟨536708, by rfl⟩ : syracuseStep 715611 = 1073417) B1073417
theorem B715679 : Blo 714321 715679 := bstep (se 1 (by rfl) ⟨536759, by rfl⟩ : syracuseStep 715679 = 1073519) B1073519
theorem B715823 : Blo 714321 715823 := bstep (se 1 (by rfl) ⟨536867, by rfl⟩ : syracuseStep 715823 = 1073735) B1073735
theorem B715847 : Blo 714321 715847 := bstep (se 1 (by rfl) ⟨536885, by rfl⟩ : syracuseStep 715847 = 1073771) B1073771
theorem B1076345 : Blo 714321 1076345 := bstep (se 2 (by rfl) ⟨403629, by rfl⟩ : syracuseStep 1076345 = 807259) B807259
theorem B2419847 : Blo 714321 2419847 := bstep (se 1 (by rfl) ⟨1814885, by rfl⟩ : syracuseStep 2419847 = 3629771) B3629771
theorem B715999 : Blo 714321 715999 := bstep (se 1 (by rfl) ⟨536999, by rfl⟩ : syracuseStep 715999 = 1073999) B1073999
theorem B1076447 : Blo 714321 1076447 := bstep (se 1 (by rfl) ⟨807335, by rfl⟩ : syracuseStep 1076447 = 1614671) B1614671
theorem B2419955 : Blo 714321 2419955 := bstep (se 1 (by rfl) ⟨1814966, by rfl⟩ : syracuseStep 2419955 = 3629933) B3629933
theorem B1207561 : Blo 714321 1207561 := bstep (se 2 (by rfl) ⟨452835, by rfl⟩ : syracuseStep 1207561 = 905671) B905671
theorem B1076489 : Blo 714321 1076489 := bstep (se 2 (by rfl) ⟨403683, by rfl⟩ : syracuseStep 1076489 = 807367) B807367
theorem B1076591 : Blo 714321 1076591 := bstep (se 1 (by rfl) ⟨807443, by rfl⟩ : syracuseStep 1076591 = 1614887) B1614887
theorem B716263 : Blo 714321 716263 := bstep (se 1 (by rfl) ⟨537197, by rfl⟩ : syracuseStep 716263 = 1074395) B1074395
theorem B1076711 : Blo 714321 1076711 := bstep (se 1 (by rfl) ⟨807533, by rfl⟩ : syracuseStep 1076711 = 1615067) B1615067
theorem B716379 : Blo 714321 716379 := bstep (se 1 (by rfl) ⟨537284, by rfl⟩ : syracuseStep 716379 = 1074569) B1074569
theorem B1076843 : Blo 714321 1076843 := bstep (se 1 (by rfl) ⟨807632, by rfl⟩ : syracuseStep 1076843 = 1615265) B1615265
theorem B1076969 : Blo 714321 1076969 := bstep (se 2 (by rfl) ⟨403863, by rfl⟩ : syracuseStep 1076969 = 807727) B807727
theorem B1208135 : Blo 714321 1208135 := bstep (se 1 (by rfl) ⟨906101, by rfl⟩ : syracuseStep 1208135 = 1812203) B1812203
theorem B716615 : Blo 714321 716615 := bstep (se 1 (by rfl) ⟨537461, by rfl⟩ : syracuseStep 716615 = 1074923) B1074923
theorem B1077113 : Blo 714321 1077113 := bstep (se 2 (by rfl) ⟨403917, by rfl⟩ : syracuseStep 1077113 = 807835) B807835
theorem B716767 : Blo 714321 716767 := bstep (se 1 (by rfl) ⟨537575, by rfl⟩ : syracuseStep 716767 = 1075151) B1075151
theorem B1077215 : Blo 714321 1077215 := bstep (se 1 (by rfl) ⟨807911, by rfl⟩ : syracuseStep 1077215 = 1615823) B1615823
theorem B3436667 : Blo 714321 3436667 := bstep (se 1 (by rfl) ⟨2577500, by rfl⟩ : syracuseStep 3436667 = 5155001) B5155001
theorem B9433253 : Blo 714321 9433253 := bstep (se 4 (by rfl) ⟨884367, by rfl⟩ : syracuseStep 9433253 = 1768735) B1768735
theorem B1077467 : Blo 714321 1077467 := bstep (se 1 (by rfl) ⟨808100, by rfl⟩ : syracuseStep 1077467 = 1616201) B1616201
theorem B717031 : Blo 714321 717031 := bstep (se 1 (by rfl) ⟨537773, by rfl⟩ : syracuseStep 717031 = 1075547) B1075547
theorem B1077479 : Blo 714321 1077479 := bstep (se 1 (by rfl) ⟨808109, by rfl⟩ : syracuseStep 1077479 = 1616219) B1616219
theorem B717183 : Blo 714321 717183 := bstep (se 1 (by rfl) ⟨537887, by rfl⟩ : syracuseStep 717183 = 1075775) B1075775
theorem B1208783 : Blo 714321 1208783 := bstep (se 1 (by rfl) ⟨906587, by rfl⟩ : syracuseStep 1208783 = 1813175) B1813175
theorem B717263 : Blo 714321 717263 := bstep (se 1 (by rfl) ⟨537947, by rfl⟩ : syracuseStep 717263 = 1075895) B1075895
theorem B717415 : Blo 714321 717415 := bstep (se 1 (by rfl) ⟨538061, by rfl⟩ : syracuseStep 717415 = 1076123) B1076123
theorem B2290457 : Blo 714321 2290457 := bstep (se 2 (by rfl) ⟨858921, by rfl⟩ : syracuseStep 2290457 = 1717843) B1717843
theorem B717679 : Blo 714321 717679 := bstep (se 1 (by rfl) ⟨538259, by rfl⟩ : syracuseStep 717679 = 1076519) B1076519
theorem B2421629 : Blo 714321 2421629 := bstep (se 3 (by rfl) ⟨454055, by rfl⟩ : syracuseStep 2421629 = 908111) B908111
theorem B717735 : Blo 714321 717735 := bstep (se 1 (by rfl) ⟨538301, by rfl⟩ : syracuseStep 717735 = 1076603) B1076603
theorem B717819 : Blo 714321 717819 := bstep (se 1 (by rfl) ⟨538364, by rfl⟩ : syracuseStep 717819 = 1076729) B1076729
theorem B717887 : Blo 714321 717887 := bstep (se 1 (by rfl) ⟨538415, by rfl⟩ : syracuseStep 717887 = 1076831) B1076831
theorem B1209451 : Blo 714321 1209451 := bstep (se 1 (by rfl) ⟨907088, by rfl⟩ : syracuseStep 1209451 = 1814177) B1814177
theorem B2421899 : Blo 714321 2421899 := bstep (se 1 (by rfl) ⟨1816424, by rfl⟩ : syracuseStep 2421899 = 3632849) B3632849
theorem B718031 : Blo 714321 718031 := bstep (se 1 (by rfl) ⟨538523, by rfl⟩ : syracuseStep 718031 = 1077047) B1077047
theorem B1209755 : Blo 714321 1209755 := bstep (se 1 (by rfl) ⟨907316, by rfl⟩ : syracuseStep 1209755 = 1814633) B1814633
theorem B718235 : Blo 714321 718235 := bstep (se 1 (by rfl) ⟨538676, by rfl⟩ : syracuseStep 718235 = 1077353) B1077353
theorem B3634631 : Blo 714321 3634631 := bstep (se 1 (by rfl) ⟨2725973, by rfl⟩ : syracuseStep 3634631 = 5451947) B5451947
theorem B9926345 : Blo 714321 9926345 := bstep (se 2 (by rfl) ⟨3722379, by rfl⟩ : syracuseStep 9926345 = 7444759) B7444759
theorem B9434825 : Blo 714321 9434825 := bstep (se 2 (by rfl) ⟨3538059, by rfl⟩ : syracuseStep 9434825 = 7076119) B7076119
theorem B1210079 : Blo 714321 1210079 := bstep (se 1 (by rfl) ⟨907559, by rfl⟩ : syracuseStep 1210079 = 1815119) B1815119
theorem B980731 : Blo 714321 980731 := bstep (se 1 (by rfl) ⟨735548, by rfl⟩ : syracuseStep 980731 = 1471097) B1471097
theorem B6125651 : Blo 714321 6125651 := bstep (se 1 (by rfl) ⟨4594238, by rfl⟩ : syracuseStep 6125651 = 9188477) B9188477
theorem B1210511 : Blo 714321 1210511 := bstep (se 1 (by rfl) ⟨907883, by rfl⟩ : syracuseStep 1210511 = 1815767) B1815767
theorem B1210747 : Blo 714321 1210747 := bstep (se 1 (by rfl) ⟨908060, by rfl⟩ : syracuseStep 1210747 = 1816121) B1816121
theorem B2325113 : Blo 714321 2325113 := bstep (se 2 (by rfl) ⟨871917, by rfl⟩ : syracuseStep 2325113 = 1743835) B1743835
theorem B1211017 : Blo 714321 1211017 := bstep (se 2 (by rfl) ⟨454131, by rfl⟩ : syracuseStep 1211017 = 908263) B908263
theorem B2423519 : Blo 714321 2423519 := bstep (se 1 (by rfl) ⟨1817639, by rfl⟩ : syracuseStep 2423519 = 3635279) B3635279
theorem B2718791 : Blo 714321 2718791 := bstep (se 1 (by rfl) ⟨2039093, by rfl⟩ : syracuseStep 2718791 = 4078187) B4078187
theorem B6880439 : Blo 714321 6880439 := bstep (se 1 (by rfl) ⟨5160329, by rfl⟩ : syracuseStep 6880439 = 10320659) B10320659
theorem B5438825 : Blo 714321 5438825 := bstep (se 2 (by rfl) ⟨2039559, by rfl⟩ : syracuseStep 5438825 = 4079119) B4079119
theorem B4914599 : Blo 714321 4914599 := bstep (se 1 (by rfl) ⟨3685949, by rfl⟩ : syracuseStep 4914599 = 7371899) B7371899
theorem B2424275 : Blo 714321 2424275 := bstep (se 1 (by rfl) ⟨1818206, by rfl⟩ : syracuseStep 2424275 = 3636413) B3636413
theorem B10354337 : Blo 714321 10354337 := bstep (se 2 (by rfl) ⟨3882876, by rfl⟩ : syracuseStep 10354337 = 7765753) B7765753
theorem B5505641 : Blo 714321 5505641 := bstep (se 2 (by rfl) ⟨2064615, by rfl⟩ : syracuseStep 5505641 = 4129231) B4129231
theorem B25101053 : Blo 714321 25101053 := bstep (se 3 (by rfl) ⟨4706447, by rfl⟩ : syracuseStep 25101053 = 9412895) B9412895
theorem B28672969 : Blo 714321 28672969 := bstep (se 2 (by rfl) ⟨10752363, by rfl⟩ : syracuseStep 28672969 = 21504727) B21504727
theorem B1607273 : Blo 714321 1607273 := bstep (se 2 (by rfl) ⟨602727, by rfl⟩ : syracuseStep 1607273 = 1205455) B1205455
theorem B1017451 : Blo 714321 1017451 := bstep (se 1 (by rfl) ⟨763088, by rfl⟩ : syracuseStep 1017451 = 1526177) B1526177
theorem B1607867 : Blo 714321 1607867 := bstep (se 1 (by rfl) ⟨1205900, by rfl⟩ : syracuseStep 1607867 = 2411801) B2411801
theorem B1607903 : Blo 714321 1607903 := bstep (se 1 (by rfl) ⟨1205927, by rfl⟩ : syracuseStep 1607903 = 2411855) B2411855
theorem B1608353 : Blo 714321 1608353 := bstep (se 2 (by rfl) ⟨603132, by rfl⟩ : syracuseStep 1608353 = 1206265) B1206265
theorem B1608569 : Blo 714321 1608569 := bstep (se 2 (by rfl) ⟨603213, by rfl⟩ : syracuseStep 1608569 = 1206427) B1206427
theorem B1608713 : Blo 714321 1608713 := bstep (se 2 (by rfl) ⟨603267, by rfl⟩ : syracuseStep 1608713 = 1206535) B1206535
theorem B1739839 : Blo 714321 1739839 := bstep (se 1 (by rfl) ⟨1304879, by rfl⟩ : syracuseStep 1739839 = 2609759) B2609759
theorem B1608767 : Blo 714321 1608767 := bstep (se 1 (by rfl) ⟨1206575, by rfl⟩ : syracuseStep 1608767 = 2413151) B2413151
theorem B1936595 : Blo 714321 1936595 := bstep (se 1 (by rfl) ⟨1452446, by rfl⟩ : syracuseStep 1936595 = 2904893) B2904893
theorem B46501087 : Blo 714321 46501087 := bstep (se 1 (by rfl) ⟨34875815, by rfl⟩ : syracuseStep 46501087 = 69751631) B69751631
theorem B1379675 : Blo 714321 1379675 := bstep (se 1 (by rfl) ⟨1034756, by rfl⟩ : syracuseStep 1379675 = 2069513) B2069513
theorem B17403659 : Blo 714321 17403659 := bstep (se 1 (by rfl) ⟨13052744, by rfl⟩ : syracuseStep 17403659 = 26105489) B26105489
theorem B1609595 : Blo 714321 1609595 := bstep (se 1 (by rfl) ⟨1207196, by rfl⟩ : syracuseStep 1609595 = 2414393) B2414393
theorem B1609703 : Blo 714321 1609703 := bstep (se 1 (by rfl) ⟨1207277, by rfl⟩ : syracuseStep 1609703 = 2414555) B2414555
theorem B2723969 : Blo 714321 2723969 := bstep (se 2 (by rfl) ⟨1021488, by rfl⟩ : syracuseStep 2723969 = 2042977) B2042977
theorem B1609883 : Blo 714321 1609883 := bstep (se 1 (by rfl) ⟨1207412, by rfl⟩ : syracuseStep 1609883 = 2414825) B2414825
theorem B28348645 : Blo 714321 28348645 := bstep (se 4 (by rfl) ⟨2657685, by rfl⟩ : syracuseStep 28348645 = 5315371) B5315371
theorem B2724137 : Blo 714321 2724137 := bstep (se 2 (by rfl) ⟨1021551, by rfl⟩ : syracuseStep 2724137 = 2043103) B2043103
theorem B2724151 : Blo 714321 2724151 := bstep (se 1 (by rfl) ⟨2043113, by rfl⟩ : syracuseStep 2724151 = 4086227) B4086227
theorem B1610081 : Blo 714321 1610081 := bstep (se 2 (by rfl) ⟨603780, by rfl⟩ : syracuseStep 1610081 = 1207561) B1207561
theorem B1610171 : Blo 714321 1610171 := bstep (se 1 (by rfl) ⟨1207628, by rfl⟩ : syracuseStep 1610171 = 2415257) B2415257
theorem B2036279 : Blo 714321 2036279 := bstep (se 1 (by rfl) ⟨1527209, by rfl⟩ : syracuseStep 2036279 = 3054419) B3054419
theorem B2724425 : Blo 714321 2724425 := bstep (se 2 (by rfl) ⟨1021659, by rfl⟩ : syracuseStep 2724425 = 2043319) B2043319
theorem B725851 : Blo 714321 725851 := bstep (se 1 (by rfl) ⟨544388, by rfl⟩ : syracuseStep 725851 = 1088777) B1088777
theorem B1086367 : Blo 714321 1086367 := bstep (se 1 (by rfl) ⟨814775, by rfl⟩ : syracuseStep 1086367 = 1629551) B1629551
theorem B1021295 : Blo 714321 1021295 := bstep (se 1 (by rfl) ⟨765971, by rfl⟩ : syracuseStep 1021295 = 1531943) B1531943
theorem B4068731 : Blo 714321 4068731 := bstep (se 1 (by rfl) ⟨3051548, by rfl⟩ : syracuseStep 4068731 = 6103097) B6103097
theorem B1611431 : Blo 714321 1611431 := bstep (se 1 (by rfl) ⟨1208573, by rfl⟩ : syracuseStep 1611431 = 2417147) B2417147
theorem B2725595 : Blo 714321 2725595 := bstep (se 1 (by rfl) ⟨2044196, by rfl⟩ : syracuseStep 2725595 = 4088393) B4088393
theorem B1611611 : Blo 714321 1611611 := bstep (se 1 (by rfl) ⟨1208708, by rfl⟩ : syracuseStep 1611611 = 2417417) B2417417
theorem B12556147 : Blo 714321 12556147 := bstep (se 1 (by rfl) ⟨9417110, by rfl⟩ : syracuseStep 12556147 = 18834221) B18834221
theorem B3676265 : Blo 714321 3676265 := bstep (se 2 (by rfl) ⟨1378599, by rfl⟩ : syracuseStep 3676265 = 2757199) B2757199
theorem B1612115 : Blo 714321 1612115 := bstep (se 1 (by rfl) ⟨1209086, by rfl⟩ : syracuseStep 1612115 = 2418173) B2418173
theorem B2300683 : Blo 714321 2300683 := bstep (se 1 (by rfl) ⟨1725512, by rfl⟩ : syracuseStep 2300683 = 3451025) B3451025
theorem B1612601 : Blo 714321 1612601 := bstep (se 2 (by rfl) ⟨604725, by rfl⟩ : syracuseStep 1612601 = 1209451) B1209451
theorem B1612655 : Blo 714321 1612655 := bstep (se 1 (by rfl) ⟨1209491, by rfl⟩ : syracuseStep 1612655 = 2418983) B2418983
theorem B1613231 : Blo 714321 1613231 := bstep (se 1 (by rfl) ⟨1209923, by rfl⟩ : syracuseStep 1613231 = 2419847) B2419847
theorem B5447087 : Blo 714321 5447087 := bstep (se 1 (by rfl) ⟨4085315, by rfl⟩ : syracuseStep 5447087 = 8170631) B8170631
theorem B1613303 : Blo 714321 1613303 := bstep (se 1 (by rfl) ⟨1209977, by rfl⟩ : syracuseStep 1613303 = 2419955) B2419955
theorem B9805321 : Blo 714321 9805321 := bstep (se 2 (by rfl) ⟨3676995, by rfl⟩ : syracuseStep 9805321 = 7353991) B7353991
theorem B11345939 : Blo 714321 11345939 := bstep (se 1 (by rfl) ⟨8509454, by rfl⟩ : syracuseStep 11345939 = 17018909) B17018909
theorem B1810937 : Blo 714321 1810937 := bstep (se 2 (by rfl) ⟨679101, by rfl⟩ : syracuseStep 1810937 = 1358203) B1358203
theorem B1614329 : Blo 714321 1614329 := bstep (se 2 (by rfl) ⟨605373, by rfl⟩ : syracuseStep 1614329 = 1210747) B1210747
theorem B2040403 : Blo 714321 2040403 := bstep (se 1 (by rfl) ⟨1530302, by rfl⟩ : syracuseStep 2040403 = 3060605) B3060605
theorem B1614419 : Blo 714321 1614419 := bstep (se 1 (by rfl) ⟨1210814, by rfl⟩ : syracuseStep 1614419 = 2421629) B2421629
theorem B1614599 : Blo 714321 1614599 := bstep (se 1 (by rfl) ⟨1210949, by rfl⟩ : syracuseStep 1614599 = 2421899) B2421899
theorem B860959 : Blo 714321 860959 := bstep (se 1 (by rfl) ⟨645719, by rfl⟩ : syracuseStep 860959 = 1291439) B1291439
theorem B5448545 : Blo 714321 5448545 := bstep (se 2 (by rfl) ⟨2043204, by rfl⟩ : syracuseStep 5448545 = 4086409) B4086409
theorem B1614689 : Blo 714321 1614689 := bstep (se 2 (by rfl) ⟨605508, by rfl⟩ : syracuseStep 1614689 = 1211017) B1211017
theorem B5972945 : Blo 714321 5972945 := bstep (se 2 (by rfl) ⟨2239854, by rfl⟩ : syracuseStep 5972945 = 4479709) B4479709
theorem B7742573 : Blo 714321 7742573 := bstep (se 3 (by rfl) ⟨1451732, by rfl⟩ : syracuseStep 7742573 = 2903465) B2903465
theorem B11052301 : Blo 714321 11052301 := bstep (se 3 (by rfl) ⟨2072306, by rfl⟩ : syracuseStep 11052301 = 4144613) B4144613
theorem B1812041 : Blo 714321 1812041 := bstep (se 2 (by rfl) ⟨679515, by rfl⟩ : syracuseStep 1812041 = 1359031) B1359031
theorem B1550075 : Blo 714321 1550075 := bstep (se 1 (by rfl) ⟨1162556, by rfl⟩ : syracuseStep 1550075 = 2325113) B2325113
theorem B1615679 : Blo 714321 1615679 := bstep (se 1 (by rfl) ⟨1211759, by rfl⟩ : syracuseStep 1615679 = 2423519) B2423519
theorem B1812527 : Blo 714321 1812527 := bstep (se 1 (by rfl) ⟨1359395, by rfl⟩ : syracuseStep 1812527 = 2718791) B2718791
theorem B1616183 : Blo 714321 1616183 := bstep (se 1 (by rfl) ⟨1212137, by rfl⟩ : syracuseStep 1616183 = 2424275) B2424275
theorem B862823 : Blo 714321 862823 := bstep (se 1 (by rfl) ⟨647117, by rfl⟩ : syracuseStep 862823 = 1294235) B1294235
theorem B5450489 : Blo 714321 5450489 := bstep (se 2 (by rfl) ⟨2043933, by rfl⟩ : syracuseStep 5450489 = 4087867) B4087867
theorem B2042921 : Blo 714321 2042921 := bstep (se 2 (by rfl) ⟨766095, by rfl⟩ : syracuseStep 2042921 = 1532191) B1532191
theorem B53816399 : Blo 714321 53816399 := bstep (se 1 (by rfl) ⟨40362299, by rfl⟩ : syracuseStep 53816399 = 80724599) B80724599
theorem B4074745 : Blo 714321 4074745 := bstep (se 2 (by rfl) ⟨1528029, by rfl⟩ : syracuseStep 4074745 = 3056059) B3056059
theorem B1289695 : Blo 714321 1289695 := bstep (se 1 (by rfl) ⟨967271, by rfl⟩ : syracuseStep 1289695 = 1934543) B1934543
theorem B1290313 : Blo 714321 1290313 := bstep (se 2 (by rfl) ⟨483867, by rfl⟩ : syracuseStep 1290313 = 967735) B967735
theorem B10301863 : Blo 714321 10301863 := bstep (se 1 (by rfl) ⟨7726397, by rfl⟩ : syracuseStep 10301863 = 15452795) B15452795
theorem B3060281 : Blo 714321 3060281 := bstep (se 2 (by rfl) ⟨1147605, by rfl⟩ : syracuseStep 3060281 = 2295211) B2295211
theorem B8172089 : Blo 714321 8172089 := bstep (se 2 (by rfl) ⟨3064533, by rfl⟩ : syracuseStep 8172089 = 6129067) B6129067
theorem B5452433 : Blo 714321 5452433 := bstep (se 2 (by rfl) ⟨2044662, by rfl⟩ : syracuseStep 5452433 = 4089325) B4089325
theorem B5157539 : Blo 714321 5157539 := bstep (se 1 (by rfl) ⟨3868154, by rfl⟩ : syracuseStep 5157539 = 7736309) B7736309
theorem B766783 : Blo 714321 766783 := bstep (se 1 (by rfl) ⟨575087, by rfl⟩ : syracuseStep 766783 = 1150175) B1150175
theorem B1356905 : Blo 714321 1356905 := bstep (se 2 (by rfl) ⟨508839, by rfl⟩ : syracuseStep 1356905 = 1017679) B1017679
theorem B4601083 : Blo 714321 4601083 := bstep (se 1 (by rfl) ⟨3450812, by rfl⟩ : syracuseStep 4601083 = 6901625) B6901625
theorem B1815817 : Blo 714321 1815817 := bstep (se 2 (by rfl) ⟨680931, by rfl⟩ : syracuseStep 1815817 = 1361863) B1361863
theorem B1455707 : Blo 714321 1455707 := bstep (se 1 (by rfl) ⟨1091780, by rfl⟩ : syracuseStep 1455707 = 2183561) B2183561
theorem B9156239 : Blo 714321 9156239 := bstep (se 1 (by rfl) ⟨6867179, by rfl⟩ : syracuseStep 9156239 = 13734359) B13734359
theorem B1357535 : Blo 714321 1357535 := bstep (se 1 (by rfl) ⟨1018151, by rfl⟩ : syracuseStep 1357535 = 2036303) B2036303
theorem B1816303 : Blo 714321 1816303 := bstep (se 1 (by rfl) ⟨1362227, by rfl⟩ : syracuseStep 1816303 = 2724455) B2724455
theorem B6534989 : Blo 714321 6534989 := bstep (se 3 (by rfl) ⟨1225310, by rfl⟩ : syracuseStep 6534989 = 2450621) B2450621
theorem B5519411 : Blo 714321 5519411 := bstep (se 1 (by rfl) ⟨4139558, by rfl⟩ : syracuseStep 5519411 = 8279117) B8279117
theorem B1358059 : Blo 714321 1358059 := bstep (se 1 (by rfl) ⟨1018544, by rfl⟩ : syracuseStep 1358059 = 2037089) B2037089
theorem B1358279 : Blo 714321 1358279 := bstep (se 1 (by rfl) ⟨1018709, by rfl⟩ : syracuseStep 1358279 = 2037419) B2037419
theorem B3062279 : Blo 714321 3062279 := bstep (se 1 (by rfl) ⟨2296709, by rfl⟩ : syracuseStep 3062279 = 4593419) B4593419
theorem B1817275 : Blo 714321 1817275 := bstep (se 1 (by rfl) ⟨1362956, by rfl⟩ : syracuseStep 1817275 = 2725913) B2725913
theorem B5159639 : Blo 714321 5159639 := bstep (se 1 (by rfl) ⟨3869729, by rfl⟩ : syracuseStep 5159639 = 7739459) B7739459
theorem B6896431 : Blo 714321 6896431 := bstep (se 1 (by rfl) ⟨5172323, by rfl⟩ : syracuseStep 6896431 = 10344647) B10344647
theorem B12238451 : Blo 714321 12238451 := bstep (se 1 (by rfl) ⟨9178838, by rfl⟩ : syracuseStep 12238451 = 18357677) B18357677
theorem B1359737 : Blo 714321 1359737 := bstep (se 2 (by rfl) ⟨509901, by rfl⟩ : syracuseStep 1359737 = 1019803) B1019803
theorem B1720207 : Blo 714321 1720207 := bstep (se 1 (by rfl) ⟨1290155, by rfl⟩ : syracuseStep 1720207 = 2580311) B2580311
theorem B2899901 : Blo 714321 2899901 := bstep (se 3 (by rfl) ⟨543731, by rfl⟩ : syracuseStep 2899901 = 1087463) B1087463
theorem B1360489 : Blo 714321 1360489 := bstep (se 2 (by rfl) ⟨510183, by rfl⟩ : syracuseStep 1360489 = 1020367) B1020367
theorem B52937545 : Blo 714321 52937545 := bstep (se 2 (by rfl) ⟨19851579, by rfl⟩ : syracuseStep 52937545 = 39703159) B39703159
theorem B8176463 : Blo 714321 8176463 := bstep (se 1 (by rfl) ⟨6132347, by rfl⟩ : syracuseStep 8176463 = 12264695) B12264695
theorem B1360891 : Blo 714321 1360891 := bstep (se 1 (by rfl) ⟨1020668, by rfl⟩ : syracuseStep 1360891 = 2041337) B2041337
theorem B1361119 : Blo 714321 1361119 := bstep (se 1 (by rfl) ⟨1020839, by rfl⟩ : syracuseStep 1361119 = 2041679) B2041679
theorem B13059467 : Blo 714321 13059467 := bstep (se 1 (by rfl) ⟨9794600, by rfl⟩ : syracuseStep 13059467 = 19589201) B19589201
theorem B1361377 : Blo 714321 1361377 := bstep (se 2 (by rfl) ⟨510516, by rfl⟩ : syracuseStep 1361377 = 1021033) B1021033
theorem B804379 : Blo 714321 804379 := bstep (se 1 (by rfl) ⟨603284, by rfl⟩ : syracuseStep 804379 = 1206569) B1206569
theorem B30984119 : Blo 714321 30984119 := bstep (se 1 (by rfl) ⟨23238089, by rfl⟩ : syracuseStep 30984119 = 46476179) B46476179
theorem B1493147 : Blo 714321 1493147 := bstep (se 1 (by rfl) ⟨1119860, by rfl⟩ : syracuseStep 1493147 = 2239721) B2239721
theorem B805423 : Blo 714321 805423 := bstep (se 1 (by rfl) ⟨604067, by rfl⟩ : syracuseStep 805423 = 1208135) B1208135
theorem B2411369 : Blo 714321 2411369 := bstep (se 2 (by rfl) ⟨904263, by rfl⟩ : syracuseStep 2411369 = 1808527) B1808527
theorem B805855 : Blo 714321 805855 := bstep (se 1 (by rfl) ⟨604391, by rfl⟩ : syracuseStep 805855 = 1208783) B1208783
theorem B1526971 : Blo 714321 1526971 := bstep (se 1 (by rfl) ⟨1145228, by rfl⟩ : syracuseStep 1526971 = 2290457) B2290457
theorem B10996955 : Blo 714321 10996955 := bstep (se 1 (by rfl) ⟨8247716, by rfl⟩ : syracuseStep 10996955 = 16495433) B16495433
theorem B1363321 : Blo 714321 1363321 := bstep (se 2 (by rfl) ⟨511245, by rfl⟩ : syracuseStep 1363321 = 1022491) B1022491
theorem B7359905 : Blo 714321 7359905 := bstep (se 2 (by rfl) ⟨2759964, by rfl⟩ : syracuseStep 7359905 = 5519929) B5519929
theorem B806503 : Blo 714321 806503 := bstep (se 1 (by rfl) ⟨604877, by rfl⟩ : syracuseStep 806503 = 1209755) B1209755
theorem B806719 : Blo 714321 806719 := bstep (se 1 (by rfl) ⟨605039, by rfl⟩ : syracuseStep 806719 = 1210079) B1210079
theorem B2412503 : Blo 714321 2412503 := bstep (se 1 (by rfl) ⟨1809377, by rfl⟩ : syracuseStep 2412503 = 3618755) B3618755
theorem B5230565 : Blo 714321 5230565 := bstep (se 4 (by rfl) ⟨490365, by rfl⟩ : syracuseStep 5230565 = 980731) B980731
theorem B4083767 : Blo 714321 4083767 := bstep (se 1 (by rfl) ⟨3062825, by rfl⟩ : syracuseStep 4083767 = 6125651) B6125651
theorem B807007 : Blo 714321 807007 := bstep (se 1 (by rfl) ⟨605255, by rfl⟩ : syracuseStep 807007 = 1210511) B1210511
theorem B2412719 : Blo 714321 2412719 := bstep (se 1 (by rfl) ⟨1809539, by rfl⟩ : syracuseStep 2412719 = 3619079) B3619079
theorem B6541559 : Blo 714321 6541559 := bstep (se 1 (by rfl) ⟨4906169, by rfl⟩ : syracuseStep 6541559 = 9812339) B9812339
theorem B7065967 : Blo 714321 7065967 := bstep (se 1 (by rfl) ⟨5299475, by rfl⟩ : syracuseStep 7065967 = 10598951) B10598951
theorem B3625883 : Blo 714321 3625883 := bstep (se 1 (by rfl) ⟨2719412, by rfl⟩ : syracuseStep 3625883 = 5438825) B5438825
theorem B906223 : Blo 714321 906223 := bstep (se 1 (by rfl) ⟨679667, by rfl⟩ : syracuseStep 906223 = 1359335) B1359335
theorem B6902891 : Blo 714321 6902891 := bstep (se 1 (by rfl) ⟨5177168, by rfl⟩ : syracuseStep 6902891 = 10354337) B10354337
theorem B2413691 : Blo 714321 2413691 := bstep (se 1 (by rfl) ⟨1810268, by rfl⟩ : syracuseStep 2413691 = 3620537) B3620537
theorem B3626369 : Blo 714321 3626369 := bstep (se 2 (by rfl) ⟨1359888, by rfl⟩ : syracuseStep 3626369 = 2719777) B2719777
theorem B2413961 : Blo 714321 2413961 := bstep (se 2 (by rfl) ⟨905235, by rfl⟩ : syracuseStep 2413961 = 1810471) B1810471
theorem B12212207 : Blo 714321 12212207 := bstep (se 1 (by rfl) ⟨9159155, by rfl⟩ : syracuseStep 12212207 = 18318311) B18318311
theorem B874567 : Blo 714321 874567 := bstep (se 1 (by rfl) ⟨655925, by rfl⟩ : syracuseStep 874567 = 1311851) B1311851
theorem B3627179 : Blo 714321 3627179 := bstep (se 1 (by rfl) ⟨2720384, by rfl⟩ : syracuseStep 3627179 = 5440769) B5440769
theorem B1071593 : Blo 714321 1071593 := bstep (se 2 (by rfl) ⟨401847, by rfl⟩ : syracuseStep 1071593 = 803695) B803695
theorem B6871675 : Blo 714321 6871675 := bstep (se 1 (by rfl) ⟨5153756, by rfl⟩ : syracuseStep 6871675 = 10307513) B10307513
theorem B1530695 : Blo 714321 1530695 := bstep (se 1 (by rfl) ⟨1148021, by rfl⟩ : syracuseStep 1530695 = 2296043) B2296043
theorem B1071983 : Blo 714321 1071983 := bstep (se 1 (by rfl) ⟨803987, by rfl⟩ : syracuseStep 1071983 = 1607975) B1607975
theorem B1071995 : Blo 714321 1071995 := bstep (se 1 (by rfl) ⟨803996, by rfl⟩ : syracuseStep 1071995 = 1607993) B1607993
theorem B1072859 : Blo 714321 1072859 := bstep (se 1 (by rfl) ⟨804644, by rfl⟩ : syracuseStep 1072859 = 1609289) B1609289
theorem B1073129 : Blo 714321 1073129 := bstep (se 2 (by rfl) ⟨402423, by rfl⟩ : syracuseStep 1073129 = 804847) B804847
theorem B44130365 : Blo 714321 44130365 := bstep (se 3 (by rfl) ⟨8274443, by rfl⟩ : syracuseStep 44130365 = 16548887) B16548887
theorem B6873673 : Blo 714321 6873673 := bstep (se 2 (by rfl) ⟨2577627, by rfl⟩ : syracuseStep 6873673 = 5155255) B5155255
theorem B2351783 : Blo 714321 2351783 := bstep (se 1 (by rfl) ⟨1763837, by rfl⟩ : syracuseStep 2351783 = 3527675) B3527675
theorem B1073831 : Blo 714321 1073831 := bstep (se 1 (by rfl) ⟨805373, by rfl⟩ : syracuseStep 1073831 = 1610747) B1610747
theorem B3433225 : Blo 714321 3433225 := bstep (se 2 (by rfl) ⟨1287459, by rfl⟩ : syracuseStep 3433225 = 2574919) B2574919
theorem B1073951 : Blo 714321 1073951 := bstep (se 1 (by rfl) ⟨805463, by rfl⟩ : syracuseStep 1073951 = 1610927) B1610927
theorem B1073975 : Blo 714321 1073975 := bstep (se 1 (by rfl) ⟨805481, by rfl⟩ : syracuseStep 1073975 = 1610963) B1610963
theorem B1074155 : Blo 714321 1074155 := bstep (se 1 (by rfl) ⟨805616, by rfl⟩ : syracuseStep 1074155 = 1611233) B1611233
theorem B13100039 : Blo 714321 13100039 := bstep (se 1 (by rfl) ⟨9825029, by rfl⟩ : syracuseStep 13100039 = 19650059) B19650059
theorem B1205833 : Blo 714321 1205833 := bstep (se 2 (by rfl) ⟨452187, by rfl⟩ : syracuseStep 1205833 = 904375) B904375
theorem B6973067 : Blo 714321 6973067 := bstep (se 1 (by rfl) ⟨5229800, by rfl⟩ : syracuseStep 6973067 = 10459601) B10459601
theorem B714431 : Blo 714321 714431 := bstep (se 1 (by rfl) ⟨535823, by rfl⟩ : syracuseStep 714431 = 1071647) B1071647
theorem B26470253 : Blo 714321 26470253 := bstep (se 3 (by rfl) ⟨4963172, by rfl⟩ : syracuseStep 26470253 = 9926345) B9926345
theorem B714687 : Blo 714321 714687 := bstep (se 1 (by rfl) ⟨536015, by rfl⟩ : syracuseStep 714687 = 1072031) B1072031
theorem B3631067 : Blo 714321 3631067 := bstep (se 1 (by rfl) ⟨2723300, by rfl⟩ : syracuseStep 3631067 = 5446601) B5446601
theorem B714719 : Blo 714321 714719 := bstep (se 1 (by rfl) ⟨536039, by rfl⟩ : syracuseStep 714719 = 1072079) B1072079
theorem B714779 : Blo 714321 714779 := bstep (se 1 (by rfl) ⟨536084, by rfl⟩ : syracuseStep 714779 = 1072169) B1072169
theorem B1206299 : Blo 714321 1206299 := bstep (se 1 (by rfl) ⟨904724, by rfl⟩ : syracuseStep 1206299 = 1809449) B1809449
theorem B714783 : Blo 714321 714783 := bstep (se 1 (by rfl) ⟨536087, by rfl⟩ : syracuseStep 714783 = 1072175) B1072175
theorem B714799 : Blo 714321 714799 := bstep (se 1 (by rfl) ⟨536099, by rfl⟩ : syracuseStep 714799 = 1072199) B1072199
theorem B1206319 : Blo 714321 1206319 := bstep (se 1 (by rfl) ⟨904739, by rfl⟩ : syracuseStep 1206319 = 1809479) B1809479
theorem B1075247 : Blo 714321 1075247 := bstep (se 1 (by rfl) ⟨806435, by rfl⟩ : syracuseStep 1075247 = 1612871) B1612871
theorem B5433479 : Blo 714321 5433479 := bstep (se 1 (by rfl) ⟨4075109, by rfl⟩ : syracuseStep 5433479 = 8150219) B8150219
theorem B714975 : Blo 714321 714975 := bstep (se 1 (by rfl) ⟨536231, by rfl⟩ : syracuseStep 714975 = 1072463) B1072463
theorem B715035 : Blo 714321 715035 := bstep (se 1 (by rfl) ⟨536276, by rfl⟩ : syracuseStep 715035 = 1072553) B1072553
theorem B1075511 : Blo 714321 1075511 := bstep (se 1 (by rfl) ⟨806633, by rfl⟩ : syracuseStep 1075511 = 1613267) B1613267
theorem B715135 : Blo 714321 715135 := bstep (se 1 (by rfl) ⟨536351, by rfl⟩ : syracuseStep 715135 = 1072703) B1072703
theorem B2910601 : Blo 714321 2910601 := bstep (se 2 (by rfl) ⟨1091475, by rfl⟩ : syracuseStep 2910601 = 2182951) B2182951
theorem B3631553 : Blo 714321 3631553 := bstep (se 2 (by rfl) ⟨1361832, by rfl⟩ : syracuseStep 3631553 = 2723665) B2723665
theorem B1075691 : Blo 714321 1075691 := bstep (se 1 (by rfl) ⟨806768, by rfl⟩ : syracuseStep 1075691 = 1613537) B1613537
theorem B715311 : Blo 714321 715311 := bstep (se 1 (by rfl) ⟨536483, by rfl⟩ : syracuseStep 715311 = 1072967) B1072967
theorem B1469011 : Blo 714321 1469011 := bstep (se 1 (by rfl) ⟨1101758, by rfl⟩ : syracuseStep 1469011 = 2203517) B2203517
theorem B715367 : Blo 714321 715367 := bstep (se 1 (by rfl) ⟨536525, by rfl⟩ : syracuseStep 715367 = 1073051) B1073051
theorem B715743 : Blo 714321 715743 := bstep (se 1 (by rfl) ⟨536807, by rfl⟩ : syracuseStep 715743 = 1073615) B1073615
theorem B715771 : Blo 714321 715771 := bstep (se 1 (by rfl) ⟨536828, by rfl⟩ : syracuseStep 715771 = 1073657) B1073657
theorem B715839 : Blo 714321 715839 := bstep (se 1 (by rfl) ⟨536879, by rfl⟩ : syracuseStep 715839 = 1073759) B1073759
theorem B10316969 : Blo 714321 10316969 := bstep (se 2 (by rfl) ⟨3868863, by rfl⟩ : syracuseStep 10316969 = 7737727) B7737727
theorem B1076393 : Blo 714321 1076393 := bstep (se 2 (by rfl) ⟨403647, by rfl⟩ : syracuseStep 1076393 = 807295) B807295
theorem B6876521 : Blo 714321 6876521 := bstep (se 2 (by rfl) ⟨2578695, by rfl⟩ : syracuseStep 6876521 = 5157391) B5157391
theorem B716159 : Blo 714321 716159 := bstep (se 1 (by rfl) ⟨537119, by rfl⟩ : syracuseStep 716159 = 1074239) B1074239
theorem B716187 : Blo 714321 716187 := bstep (se 1 (by rfl) ⟨537140, by rfl⟩ : syracuseStep 716187 = 1074281) B1074281
theorem B716255 : Blo 714321 716255 := bstep (se 1 (by rfl) ⟨537191, by rfl⟩ : syracuseStep 716255 = 1074383) B1074383
theorem B5434937 : Blo 714321 5434937 := bstep (se 2 (by rfl) ⟨2038101, by rfl⟩ : syracuseStep 5434937 = 4076203) B4076203
theorem B1076807 : Blo 714321 1076807 := bstep (se 1 (by rfl) ⟨807605, by rfl⟩ : syracuseStep 1076807 = 1615211) B1615211
theorem B716391 : Blo 714321 716391 := bstep (se 1 (by rfl) ⟨537293, by rfl⟩ : syracuseStep 716391 = 1074587) B1074587
theorem B716539 : Blo 714321 716539 := bstep (se 1 (by rfl) ⟨537404, by rfl⟩ : syracuseStep 716539 = 1074809) B1074809
theorem B1076987 : Blo 714321 1076987 := bstep (se 1 (by rfl) ⟨807740, by rfl⟩ : syracuseStep 1076987 = 1615481) B1615481
theorem B716607 : Blo 714321 716607 := bstep (se 1 (by rfl) ⟨537455, by rfl⟩ : syracuseStep 716607 = 1074911) B1074911
theorem B716671 : Blo 714321 716671 := bstep (se 1 (by rfl) ⟨537503, by rfl⟩ : syracuseStep 716671 = 1075007) B1075007
theorem B1634185 : Blo 714321 1634185 := bstep (se 2 (by rfl) ⟨612819, by rfl⟩ : syracuseStep 1634185 = 1225639) B1225639
theorem B716783 : Blo 714321 716783 := bstep (se 1 (by rfl) ⟨537587, by rfl⟩ : syracuseStep 716783 = 1075175) B1075175
theorem B716795 : Blo 714321 716795 := bstep (se 1 (by rfl) ⟨537596, by rfl⟩ : syracuseStep 716795 = 1075193) B1075193
theorem B716863 : Blo 714321 716863 := bstep (se 1 (by rfl) ⟨537647, by rfl⟩ : syracuseStep 716863 = 1075295) B1075295
theorem B2420819 : Blo 714321 2420819 := bstep (se 1 (by rfl) ⟨1815614, by rfl⟩ : syracuseStep 2420819 = 3631229) B3631229
theorem B716903 : Blo 714321 716903 := bstep (se 1 (by rfl) ⟨537677, by rfl⟩ : syracuseStep 716903 = 1075355) B1075355
theorem B716927 : Blo 714321 716927 := bstep (se 1 (by rfl) ⟨537695, by rfl⟩ : syracuseStep 716927 = 1075391) B1075391
theorem B716955 : Blo 714321 716955 := bstep (se 1 (by rfl) ⟨537716, by rfl⟩ : syracuseStep 716955 = 1075433) B1075433
theorem B3109049 : Blo 714321 3109049 := bstep (se 2 (by rfl) ⟨1165893, by rfl⟩ : syracuseStep 3109049 = 2331787) B2331787
theorem B717159 : Blo 714321 717159 := bstep (se 1 (by rfl) ⟨537869, by rfl⟩ : syracuseStep 717159 = 1075739) B1075739
theorem B717211 : Blo 714321 717211 := bstep (se 1 (by rfl) ⟨537908, by rfl⟩ : syracuseStep 717211 = 1075817) B1075817
theorem B9204263 : Blo 714321 9204263 := bstep (se 1 (by rfl) ⟨6903197, by rfl⟩ : syracuseStep 9204263 = 13806395) B13806395
theorem B1471211 : Blo 714321 1471211 := bstep (se 1 (by rfl) ⟨1103408, by rfl⟩ : syracuseStep 1471211 = 2206817) B2206817
theorem B717563 : Blo 714321 717563 := bstep (se 1 (by rfl) ⟨538172, by rfl⟩ : syracuseStep 717563 = 1076345) B1076345
theorem B717631 : Blo 714321 717631 := bstep (se 1 (by rfl) ⟨538223, by rfl⟩ : syracuseStep 717631 = 1076447) B1076447
theorem B717659 : Blo 714321 717659 := bstep (se 1 (by rfl) ⟨538244, by rfl⟩ : syracuseStep 717659 = 1076489) B1076489
theorem B717727 : Blo 714321 717727 := bstep (se 1 (by rfl) ⟨538295, by rfl⟩ : syracuseStep 717727 = 1076591) B1076591
theorem B717807 : Blo 714321 717807 := bstep (se 1 (by rfl) ⟨538355, by rfl⟩ : syracuseStep 717807 = 1076711) B1076711
theorem B717895 : Blo 714321 717895 := bstep (se 1 (by rfl) ⟨538421, by rfl⟩ : syracuseStep 717895 = 1076843) B1076843
theorem B17396855 : Blo 714321 17396855 := bstep (se 1 (by rfl) ⟨13047641, by rfl⟩ : syracuseStep 17396855 = 26095283) B26095283
theorem B717979 : Blo 714321 717979 := bstep (se 1 (by rfl) ⟨538484, by rfl⟩ : syracuseStep 717979 = 1076969) B1076969
theorem B718075 : Blo 714321 718075 := bstep (se 1 (by rfl) ⟨538556, by rfl⟩ : syracuseStep 718075 = 1077113) B1077113
theorem B718143 : Blo 714321 718143 := bstep (se 1 (by rfl) ⟨538607, by rfl⟩ : syracuseStep 718143 = 1077215) B1077215
theorem B2291111 : Blo 714321 2291111 := bstep (se 1 (by rfl) ⟨1718333, by rfl⟩ : syracuseStep 2291111 = 3436667) B3436667
theorem B6288835 : Blo 714321 6288835 := bstep (se 1 (by rfl) ⟨4716626, by rfl⟩ : syracuseStep 6288835 = 9433253) B9433253
theorem B718311 : Blo 714321 718311 := bstep (se 1 (by rfl) ⟨538733, by rfl⟩ : syracuseStep 718311 = 1077467) B1077467
theorem B718319 : Blo 714321 718319 := bstep (se 1 (by rfl) ⟨538739, by rfl⟩ : syracuseStep 718319 = 1077479) B1077479
theorem B2423087 : Blo 714321 2423087 := bstep (se 1 (by rfl) ⟨1817315, by rfl⟩ : syracuseStep 2423087 = 3634631) B3634631
theorem B2586971 : Blo 714321 2586971 := bstep (se 1 (by rfl) ⟨1940228, by rfl⟩ : syracuseStep 2586971 = 3880457) B3880457
theorem B13105597 : Blo 714321 13105597 := bstep (se 3 (by rfl) ⟨2457299, by rfl⟩ : syracuseStep 13105597 = 4914599) B4914599
theorem B6289883 : Blo 714321 6289883 := bstep (se 1 (by rfl) ⟨4717412, by rfl⟩ : syracuseStep 6289883 = 9434825) B9434825
theorem B11041343 : Blo 714321 11041343 := bstep (se 1 (by rfl) ⟨8281007, by rfl⟩ : syracuseStep 11041343 = 16562015) B16562015
theorem B2292353 : Blo 714321 2292353 := bstep (se 2 (by rfl) ⟨859632, by rfl⟩ : syracuseStep 2292353 = 1719265) B1719265
theorem B33094277 : Blo 714321 33094277 := bstep (se 4 (by rfl) ⟨3102588, by rfl⟩ : syracuseStep 33094277 = 6205177) B6205177
theorem B2718623 : Blo 714321 2718623 := bstep (se 1 (by rfl) ⟨2038967, by rfl⟩ : syracuseStep 2718623 = 4077935) B4077935
theorem B1211483 : Blo 714321 1211483 := bstep (se 1 (by rfl) ⟨908612, by rfl⟩ : syracuseStep 1211483 = 1817225) B1817225
theorem B3439741 : Blo 714321 3439741 := bstep (se 3 (by rfl) ⟨644951, by rfl⟩ : syracuseStep 3439741 = 1289903) B1289903
theorem B4586959 : Blo 714321 4586959 := bstep (se 1 (by rfl) ⟨3440219, by rfl⟩ : syracuseStep 4586959 = 6880439) B6880439
theorem B6881669 : Blo 714321 6881669 := bstep (se 4 (by rfl) ⟨645156, by rfl⟩ : syracuseStep 6881669 = 1290313) B1290313
theorem B3670427 : Blo 714321 3670427 := bstep (se 1 (by rfl) ⟨2752820, by rfl⟩ : syracuseStep 3670427 = 5505641) B5505641
theorem B2720537 : Blo 714321 2720537 := bstep (se 2 (by rfl) ⟨1020201, by rfl⟩ : syracuseStep 2720537 = 2040403) B2040403
theorem B1147945 : Blo 714321 1147945 := bstep (se 2 (by rfl) ⟨430479, by rfl⟩ : syracuseStep 1147945 = 860959) B860959
theorem B70583393 : Blo 714321 70583393 := bstep (se 2 (by rfl) ⟨26468772, by rfl⟩ : syracuseStep 70583393 = 52937545) B52937545
theorem B1607579 : Blo 714321 1607579 := bstep (se 1 (by rfl) ⟨1205684, by rfl⟩ : syracuseStep 1607579 = 2411369) B2411369
theorem B1607777 : Blo 714321 1607777 := bstep (se 2 (by rfl) ⟨602916, by rfl⟩ : syracuseStep 1607777 = 1205833) B1205833
theorem B919783 : Blo 714321 919783 := bstep (se 1 (by rfl) ⟨689837, by rfl⟩ : syracuseStep 919783 = 1379675) B1379675
theorem B11602439 : Blo 714321 11602439 := bstep (se 1 (by rfl) ⟨8701829, by rfl⟩ : syracuseStep 11602439 = 17403659) B17403659
theorem B15927853 : Blo 714321 15927853 := bstep (se 3 (by rfl) ⟨2986472, by rfl⟩ : syracuseStep 15927853 = 5972945) B5972945
theorem B1608335 : Blo 714321 1608335 := bstep (se 1 (by rfl) ⟨1206251, by rfl⟩ : syracuseStep 1608335 = 2412503) B2412503
theorem B2722511 : Blo 714321 2722511 := bstep (se 1 (by rfl) ⟨2041883, by rfl⟩ : syracuseStep 2722511 = 4083767) B4083767
theorem B1608425 : Blo 714321 1608425 := bstep (se 2 (by rfl) ⟨603159, by rfl⟩ : syracuseStep 1608425 = 1206319) B1206319
theorem B1608479 : Blo 714321 1608479 := bstep (se 1 (by rfl) ⟨1206359, by rfl⟩ : syracuseStep 1608479 = 2412719) B2412719
theorem B4361039 : Blo 714321 4361039 := bstep (se 1 (by rfl) ⟨3270779, by rfl⟩ : syracuseStep 4361039 = 6541559) B6541559
theorem B1609127 : Blo 714321 1609127 := bstep (se 1 (by rfl) ⟨1206845, by rfl⟩ : syracuseStep 1609127 = 2413691) B2413691
theorem B1609307 : Blo 714321 1609307 := bstep (se 1 (by rfl) ⟨1206980, by rfl⟩ : syracuseStep 1609307 = 2413961) B2413961
theorem B2723453 : Blo 714321 2723453 := bstep (se 3 (by rfl) ⟨510647, by rfl⟩ : syracuseStep 2723453 = 1021295) B1021295
theorem B2035961 : Blo 714321 2035961 := bstep (se 2 (by rfl) ⟨763485, by rfl⟩ : syracuseStep 2035961 = 1526971) B1526971
theorem B62001449 : Blo 714321 62001449 := bstep (se 2 (by rfl) ⟨23250543, by rfl⟩ : syracuseStep 62001449 = 46501087) B46501087
theorem B4133533 : Blo 714321 4133533 := bstep (se 3 (by rfl) ⟨775037, by rfl⟩ : syracuseStep 4133533 = 1550075) B1550075
theorem B604771093 : Blo 714321 604771093 := bstep (se 6 (by rfl) ⟨14174322, by rfl⟩ : syracuseStep 604771093 = 28348645) B28348645
theorem B13735817 : Blo 714321 13735817 := bstep (se 2 (by rfl) ⟨5150931, by rfl⟩ : syracuseStep 13735817 = 10301863) B10301863
theorem B1022377 : Blo 714321 1022377 := bstep (se 2 (by rfl) ⟨383391, by rfl⟩ : syracuseStep 1022377 = 766783) B766783
theorem B1448489 : Blo 714321 1448489 := bstep (se 2 (by rfl) ⟨543183, by rfl⟩ : syracuseStep 1448489 = 1086367) B1086367
theorem B2300861 : Blo 714321 2300861 := bstep (se 3 (by rfl) ⟨431411, by rfl⟩ : syracuseStep 2300861 = 862823) B862823
theorem B6134777 : Blo 714321 6134777 := bstep (se 2 (by rfl) ⟨2300541, by rfl⟩ : syracuseStep 6134777 = 4601083) B4601083
theorem B1613879 : Blo 714321 1613879 := bstep (se 1 (by rfl) ⟨1210409, by rfl⟩ : syracuseStep 1613879 = 2420819) B2420819
theorem B2072699 : Blo 714321 2072699 := bstep (se 1 (by rfl) ⟨1554524, by rfl⟩ : syracuseStep 2072699 = 3109049) B3109049
theorem B1810745 : Blo 714321 1810745 := bstep (se 2 (by rfl) ⟨679029, by rfl⟩ : syracuseStep 1810745 = 1358059) B1358059
theorem B6136175 : Blo 714321 6136175 := bstep (se 1 (by rfl) ⟨4602131, by rfl⟩ : syracuseStep 6136175 = 9204263) B9204263
theorem B2040187 : Blo 714321 2040187 := bstep (se 1 (by rfl) ⟨1530140, by rfl⟩ : syracuseStep 2040187 = 3060281) B3060281
theorem B5448059 : Blo 714321 5448059 := bstep (se 1 (by rfl) ⟨4086044, by rfl⟩ : syracuseStep 5448059 = 8172089) B8172089
theorem B17474129 : Blo 714321 17474129 := bstep (se 2 (by rfl) ⟨6552798, by rfl⟩ : syracuseStep 17474129 = 13105597) B13105597
theorem B6104159 : Blo 714321 6104159 := bstep (se 1 (by rfl) ⟨4578119, by rfl⟩ : syracuseStep 6104159 = 9156239) B9156239
theorem B3679607 : Blo 714321 3679607 := bstep (se 1 (by rfl) ⟨2759705, by rfl⟩ : syracuseStep 3679607 = 5519411) B5519411
theorem B1615391 : Blo 714321 1615391 := bstep (se 1 (by rfl) ⟨1211543, by rfl⟩ : syracuseStep 1615391 = 2423087) B2423087
theorem B2041519 : Blo 714321 2041519 := bstep (se 1 (by rfl) ⟨1531139, by rfl⟩ : syracuseStep 2041519 = 3062279) B3062279
theorem B22062851 : Blo 714321 22062851 := bstep (se 1 (by rfl) ⟨16547138, by rfl⟩ : syracuseStep 22062851 = 33094277) B33094277
theorem B1812415 : Blo 714321 1812415 := bstep (se 1 (by rfl) ⟨1359311, by rfl⟩ : syracuseStep 1812415 = 2718623) B2718623
theorem B5450975 : Blo 714321 5450975 := bstep (se 1 (by rfl) ⟨4088231, by rfl⟩ : syracuseStep 5450975 = 8176463) B8176463
theorem B1813985 : Blo 714321 1813985 := bstep (se 2 (by rfl) ⟨680244, by rfl⟩ : syracuseStep 1813985 = 1360489) B1360489
theorem B20656079 : Blo 714321 20656079 := bstep (se 1 (by rfl) ⟨15492059, by rfl⟩ : syracuseStep 20656079 = 30984119) B30984119
theorem B1814521 : Blo 714321 1814521 := bstep (se 2 (by rfl) ⟨680445, by rfl⟩ : syracuseStep 1814521 = 1360891) B1360891
theorem B995431 : Blo 714321 995431 := bstep (se 1 (by rfl) ⟨746573, by rfl⟩ : syracuseStep 995431 = 1493147) B1493147
theorem B1814825 : Blo 714321 1814825 := bstep (se 2 (by rfl) ⟨680559, by rfl⟩ : syracuseStep 1814825 = 1361119) B1361119
theorem B1815169 : Blo 714321 1815169 := bstep (se 2 (by rfl) ⟨680688, by rfl⟩ : syracuseStep 1815169 = 1361377) B1361377
theorem B1291063 : Blo 714321 1291063 := bstep (se 1 (by rfl) ⟨968297, by rfl⟩ : syracuseStep 1291063 = 1936595) B1936595
theorem B1356601 : Blo 714321 1356601 := bstep (se 2 (by rfl) ⟨508725, by rfl⟩ : syracuseStep 1356601 = 1017451) B1017451
theorem B3487043 : Blo 714321 3487043 := bstep (se 1 (by rfl) ⟨2615282, by rfl⟩ : syracuseStep 3487043 = 5230565) B5230565
theorem B1815979 : Blo 714321 1815979 := bstep (se 1 (by rfl) ⟨1361984, by rfl⟩ : syracuseStep 1815979 = 2723969) B2723969
theorem B1816091 : Blo 714321 1816091 := bstep (se 1 (by rfl) ⟨1362068, by rfl⟩ : syracuseStep 1816091 = 2724137) B2724137
theorem B1816283 : Blo 714321 1816283 := bstep (se 1 (by rfl) ⟨1362212, by rfl⟩ : syracuseStep 1816283 = 2724425) B2724425
theorem B3880801 : Blo 714321 3880801 := bstep (se 2 (by rfl) ⟨1455300, by rfl⟩ : syracuseStep 3880801 = 2910601) B2910601
theorem B4601927 : Blo 714321 4601927 := bstep (se 1 (by rfl) ⟨3451445, by rfl⟩ : syracuseStep 4601927 = 6902891) B6902891
theorem B1817063 : Blo 714321 1817063 := bstep (se 1 (by rfl) ⟨1362797, by rfl⟩ : syracuseStep 1817063 = 2725595) B2725595
theorem B8141471 : Blo 714321 8141471 := bstep (se 1 (by rfl) ⟨6106103, by rfl⟩ : syracuseStep 8141471 = 12212207) B12212207
theorem B18594845 : Blo 714321 18594845 := bstep (se 3 (by rfl) ⟨3486533, by rfl⟩ : syracuseStep 18594845 = 6973067) B6973067
theorem B1817761 : Blo 714321 1817761 := bstep (se 2 (by rfl) ⟨681660, by rfl⟩ : syracuseStep 1817761 = 1363321) B1363321
theorem B1719593 : Blo 714321 1719593 := bstep (se 2 (by rfl) ⟨644847, by rfl⟩ : syracuseStep 1719593 = 1289695) B1289695
theorem B2178913 : Blo 714321 2178913 := bstep (se 2 (by rfl) ⟨817092, by rfl⟩ : syracuseStep 2178913 = 1634185) B1634185
theorem B9421289 : Blo 714321 9421289 := bstep (se 2 (by rfl) ⟨3532983, by rfl⟩ : syracuseStep 9421289 = 7065967) B7065967
theorem B8733359 : Blo 714321 8733359 := bstep (se 1 (by rfl) ⟨6550019, by rfl⟩ : syracuseStep 8733359 = 13100039) B13100039
theorem B5161715 : Blo 714321 5161715 := bstep (se 1 (by rfl) ⟨3871286, by rfl⟩ : syracuseStep 5161715 = 7742573) B7742573
theorem B967801 : Blo 714321 967801 := bstep (se 2 (by rfl) ⟨362925, by rfl⟩ : syracuseStep 967801 = 725851) B725851
theorem B17646835 : Blo 714321 17646835 := bstep (se 1 (by rfl) ⟨13235126, by rfl⟩ : syracuseStep 17646835 = 26470253) B26470253
theorem B804199 : Blo 714321 804199 := bstep (se 1 (by rfl) ⟨603149, by rfl⟩ : syracuseStep 804199 = 1206299) B1206299
theorem B3622319 : Blo 714321 3622319 := bstep (se 1 (by rfl) ⟨2716739, by rfl⟩ : syracuseStep 3622319 = 5433479) B5433479
theorem B1361947 : Blo 714321 1361947 := bstep (se 1 (by rfl) ⟨1021460, by rfl⟩ : syracuseStep 1361947 = 2042921) B2042921
theorem B4081853 : Blo 714321 4081853 := bstep (se 3 (by rfl) ⟨765347, by rfl⟩ : syracuseStep 4081853 = 1530695) B1530695
theorem B3623291 : Blo 714321 3623291 := bstep (se 1 (by rfl) ⟨2717468, by rfl⟩ : syracuseStep 3623291 = 5434937) B5434937
theorem B1166089 : Blo 714321 1166089 := bstep (se 2 (by rfl) ⟨437283, by rfl⟩ : syracuseStep 1166089 = 874567) B874567
theorem B904603 : Blo 714321 904603 := bstep (se 1 (by rfl) ⟨678452, by rfl⟩ : syracuseStep 904603 = 1356905) B1356905
theorem B9162233 : Blo 714321 9162233 := bstep (se 2 (by rfl) ⟨3435837, by rfl⟩ : syracuseStep 9162233 = 6871675) B6871675
theorem B1527407 : Blo 714321 1527407 := bstep (se 1 (by rfl) ⟨1145555, by rfl⟩ : syracuseStep 1527407 = 2291111) B2291111
theorem B3067577 : Blo 714321 3067577 := bstep (se 2 (by rfl) ⟨1150341, by rfl⟩ : syracuseStep 3067577 = 2300683) B2300683
theorem B970471 : Blo 714321 970471 := bstep (se 1 (by rfl) ⟨727853, by rfl⟩ : syracuseStep 970471 = 1455707) B1455707
theorem B9195241 : Blo 714321 9195241 := bstep (se 2 (by rfl) ⟨3448215, by rfl⟩ : syracuseStep 9195241 = 6896431) B6896431
theorem B905023 : Blo 714321 905023 := bstep (se 1 (by rfl) ⟨678767, by rfl⟩ : syracuseStep 905023 = 1357535) B1357535
theorem B1724647 : Blo 714321 1724647 := bstep (se 1 (by rfl) ⟨1293485, by rfl⟩ : syracuseStep 1724647 = 2586971) B2586971
theorem B905519 : Blo 714321 905519 := bstep (se 1 (by rfl) ⟨679139, by rfl⟩ : syracuseStep 905519 = 1358279) B1358279
theorem B7360895 : Blo 714321 7360895 := bstep (se 1 (by rfl) ⟨5520671, by rfl⟩ : syracuseStep 7360895 = 11041343) B11041343
theorem B1528235 : Blo 714321 1528235 := bstep (se 1 (by rfl) ⟨1146176, by rfl⟩ : syracuseStep 1528235 = 2292353) B2292353
theorem B6115945 : Blo 714321 6115945 := bstep (se 2 (by rfl) ⟨2293479, by rfl⟩ : syracuseStep 6115945 = 4586959) B4586959
theorem B807655 : Blo 714321 807655 := bstep (se 1 (by rfl) ⟨605741, by rfl⟩ : syracuseStep 807655 = 1211483) B1211483
theorem B906491 : Blo 714321 906491 := bstep (se 1 (by rfl) ⟨679868, by rfl⟩ : syracuseStep 906491 = 1359737) B1359737
theorem B16734035 : Blo 714321 16734035 := bstep (se 1 (by rfl) ⟨12550526, by rfl⟩ : syracuseStep 16734035 = 25101053) B25101053
theorem B9164897 : Blo 714321 9164897 := bstep (se 2 (by rfl) ⟨3436836, by rfl⟩ : syracuseStep 9164897 = 6873673) B6873673
theorem B8706311 : Blo 714321 8706311 := bstep (se 1 (by rfl) ⟨6529733, by rfl⟩ : syracuseStep 8706311 = 13059467) B13059467
theorem B4577633 : Blo 714321 4577633 := bstep (se 2 (by rfl) ⟨1716612, by rfl⟩ : syracuseStep 4577633 = 3433225) B3433225
theorem B1071515 : Blo 714321 1071515 := bstep (se 1 (by rfl) ⟨803636, by rfl⟩ : syracuseStep 1071515 = 1607273) B1607273
theorem B38230625 : Blo 714321 38230625 := bstep (se 2 (by rfl) ⟨14336484, by rfl⟩ : syracuseStep 38230625 = 28672969) B28672969
theorem B1071911 : Blo 714321 1071911 := bstep (se 1 (by rfl) ⟨803933, by rfl⟩ : syracuseStep 1071911 = 1607867) B1607867
theorem B5430077 : Blo 714321 5430077 := bstep (se 3 (by rfl) ⟨1018139, by rfl⟩ : syracuseStep 5430077 = 2036279) B2036279
theorem B1071935 : Blo 714321 1071935 := bstep (se 1 (by rfl) ⟨803951, by rfl⟩ : syracuseStep 1071935 = 1607903) B1607903
theorem B14736401 : Blo 714321 14736401 := bstep (se 2 (by rfl) ⟨5526150, by rfl⟩ : syracuseStep 14736401 = 11052301) B11052301
theorem B1072235 : Blo 714321 1072235 := bstep (se 1 (by rfl) ⟨804176, by rfl⟩ : syracuseStep 1072235 = 1608353) B1608353
theorem B1072379 : Blo 714321 1072379 := bstep (se 1 (by rfl) ⟨804284, by rfl⟩ : syracuseStep 1072379 = 1608569) B1608569
theorem B1072475 : Blo 714321 1072475 := bstep (se 1 (by rfl) ⟨804356, by rfl⟩ : syracuseStep 1072475 = 1608713) B1608713
theorem B1072505 : Blo 714321 1072505 := bstep (se 2 (by rfl) ⟨402189, by rfl⟩ : syracuseStep 1072505 = 804379) B804379
theorem B1072511 : Blo 714321 1072511 := bstep (se 1 (by rfl) ⟨804383, by rfl⟩ : syracuseStep 1072511 = 1608767) B1608767
theorem B7331303 : Blo 714321 7331303 := bstep (se 1 (by rfl) ⟨5498477, by rfl⟩ : syracuseStep 7331303 = 10996955) B10996955
theorem B4906603 : Blo 714321 4906603 := bstep (se 1 (by rfl) ⟨3679952, by rfl⟩ : syracuseStep 4906603 = 7359905) B7359905
theorem B1073063 : Blo 714321 1073063 := bstep (se 1 (by rfl) ⟨804797, by rfl⟩ : syracuseStep 1073063 = 1609595) B1609595
theorem B1073135 : Blo 714321 1073135 := bstep (se 1 (by rfl) ⟨804851, by rfl⟩ : syracuseStep 1073135 = 1609703) B1609703
theorem B1073255 : Blo 714321 1073255 := bstep (se 1 (by rfl) ⟨804941, by rfl⟩ : syracuseStep 1073255 = 1609883) B1609883
theorem B1073387 : Blo 714321 1073387 := bstep (se 1 (by rfl) ⟨805040, by rfl⟩ : syracuseStep 1073387 = 1610081) B1610081
theorem B1073447 : Blo 714321 1073447 := bstep (se 1 (by rfl) ⟨805085, by rfl⟩ : syracuseStep 1073447 = 1610171) B1610171
theorem B2417255 : Blo 714321 2417255 := bstep (se 1 (by rfl) ⟨1812941, by rfl⟩ : syracuseStep 2417255 = 3625883) B3625883
theorem B1073897 : Blo 714321 1073897 := bstep (se 2 (by rfl) ⟨402711, by rfl⟩ : syracuseStep 1073897 = 805423) B805423
theorem B1958681 : Blo 714321 1958681 := bstep (se 2 (by rfl) ⟨734505, by rfl⟩ : syracuseStep 1958681 = 1469011) B1469011
theorem B2712487 : Blo 714321 2712487 := bstep (se 1 (by rfl) ⟨2034365, by rfl⟩ : syracuseStep 2712487 = 4068731) B4068731
theorem B2417579 : Blo 714321 2417579 := bstep (se 1 (by rfl) ⟨1813184, by rfl⟩ : syracuseStep 2417579 = 3626369) B3626369
theorem B1074287 : Blo 714321 1074287 := bstep (se 1 (by rfl) ⟨805715, by rfl⟩ : syracuseStep 1074287 = 1611431) B1611431
theorem B1074407 : Blo 714321 1074407 := bstep (se 1 (by rfl) ⟨805805, by rfl⟩ : syracuseStep 1074407 = 1611611) B1611611
theorem B1074473 : Blo 714321 1074473 := bstep (se 2 (by rfl) ⟨402927, by rfl⟩ : syracuseStep 1074473 = 805855) B805855
theorem B2450843 : Blo 714321 2450843 := bstep (se 1 (by rfl) ⟨1838132, by rfl⟩ : syracuseStep 2450843 = 3676265) B3676265
theorem B2319785 : Blo 714321 2319785 := bstep (se 2 (by rfl) ⟨869919, by rfl⟩ : syracuseStep 2319785 = 1739839) B1739839
theorem B2418119 : Blo 714321 2418119 := bstep (se 1 (by rfl) ⟨1813589, by rfl⟩ : syracuseStep 2418119 = 3627179) B3627179
theorem B1074743 : Blo 714321 1074743 := bstep (se 1 (by rfl) ⟨806057, by rfl⟩ : syracuseStep 1074743 = 1612115) B1612115
theorem B714395 : Blo 714321 714395 := bstep (se 1 (by rfl) ⟨535796, by rfl⟩ : syracuseStep 714395 = 1071593) B1071593
theorem B5432993 : Blo 714321 5432993 := bstep (se 2 (by rfl) ⟨2037372, by rfl⟩ : syracuseStep 5432993 = 4074745) B4074745
theorem B1075067 : Blo 714321 1075067 := bstep (se 1 (by rfl) ⟨806300, by rfl⟩ : syracuseStep 1075067 = 1612601) B1612601
theorem B714655 : Blo 714321 714655 := bstep (se 1 (by rfl) ⟨535991, by rfl⟩ : syracuseStep 714655 = 1071983) B1071983
theorem B1075103 : Blo 714321 1075103 := bstep (se 1 (by rfl) ⟨806327, by rfl⟩ : syracuseStep 1075103 = 1612655) B1612655
theorem B714663 : Blo 714321 714663 := bstep (se 1 (by rfl) ⟨535997, by rfl⟩ : syracuseStep 714663 = 1071995) B1071995
theorem B1075337 : Blo 714321 1075337 := bstep (se 2 (by rfl) ⟨403251, by rfl⟩ : syracuseStep 1075337 = 806503) B806503
theorem B1075487 : Blo 714321 1075487 := bstep (se 1 (by rfl) ⟨806615, by rfl⟩ : syracuseStep 1075487 = 1613231) B1613231
theorem B3631391 : Blo 714321 3631391 := bstep (se 1 (by rfl) ⟨2723543, by rfl⟩ : syracuseStep 3631391 = 5447087) B5447087
theorem B1075535 : Blo 714321 1075535 := bstep (se 1 (by rfl) ⟨806651, by rfl⟩ : syracuseStep 1075535 = 1613303) B1613303
theorem B1075625 : Blo 714321 1075625 := bstep (se 2 (by rfl) ⟨403359, by rfl⟩ : syracuseStep 1075625 = 806719) B806719
theorem B715239 : Blo 714321 715239 := bstep (se 1 (by rfl) ⟨536429, by rfl⟩ : syracuseStep 715239 = 1072859) B1072859
theorem B715419 : Blo 714321 715419 := bstep (se 1 (by rfl) ⟨536564, by rfl⟩ : syracuseStep 715419 = 1073129) B1073129
theorem B7563959 : Blo 714321 7563959 := bstep (se 1 (by rfl) ⟨5672969, by rfl⟩ : syracuseStep 7563959 = 11345939) B11345939
theorem B29420243 : Blo 714321 29420243 := bstep (se 1 (by rfl) ⟨22065182, by rfl⟩ : syracuseStep 29420243 = 44130365) B44130365
theorem B1076009 : Blo 714321 1076009 := bstep (se 2 (by rfl) ⟨403503, by rfl⟩ : syracuseStep 1076009 = 807007) B807007
theorem B1207291 : Blo 714321 1207291 := bstep (se 1 (by rfl) ⟨905468, by rfl⟩ : syracuseStep 1207291 = 1810937) B1810937
theorem B1076219 : Blo 714321 1076219 := bstep (se 1 (by rfl) ⟨807164, by rfl⟩ : syracuseStep 1076219 = 1614329) B1614329
theorem B1076279 : Blo 714321 1076279 := bstep (se 1 (by rfl) ⟨807209, by rfl⟩ : syracuseStep 1076279 = 1614419) B1614419
theorem B3632201 : Blo 714321 3632201 := bstep (se 2 (by rfl) ⟨1362075, by rfl⟩ : syracuseStep 3632201 = 2724151) B2724151
theorem B1567855 : Blo 714321 1567855 := bstep (se 1 (by rfl) ⟨1175891, by rfl⟩ : syracuseStep 1567855 = 2351783) B2351783
theorem B715887 : Blo 714321 715887 := bstep (se 1 (by rfl) ⟨536915, by rfl⟩ : syracuseStep 715887 = 1073831) B1073831
theorem B1076399 : Blo 714321 1076399 := bstep (se 1 (by rfl) ⟨807299, by rfl⟩ : syracuseStep 1076399 = 1614599) B1614599
theorem B715967 : Blo 714321 715967 := bstep (se 1 (by rfl) ⟨536975, by rfl⟩ : syracuseStep 715967 = 1073951) B1073951
theorem B715983 : Blo 714321 715983 := bstep (se 1 (by rfl) ⟨536987, by rfl⟩ : syracuseStep 715983 = 1073975) B1073975
theorem B3632363 : Blo 714321 3632363 := bstep (se 1 (by rfl) ⟨2724272, by rfl⟩ : syracuseStep 3632363 = 5448545) B5448545
theorem B1076459 : Blo 714321 1076459 := bstep (se 1 (by rfl) ⟨807344, by rfl⟩ : syracuseStep 1076459 = 1614689) B1614689
theorem B716103 : Blo 714321 716103 := bstep (se 1 (by rfl) ⟨537077, by rfl⟩ : syracuseStep 716103 = 1074155) B1074155
theorem B1208027 : Blo 714321 1208027 := bstep (se 1 (by rfl) ⟨906020, by rfl⟩ : syracuseStep 1208027 = 1812041) B1812041
theorem B1077119 : Blo 714321 1077119 := bstep (se 1 (by rfl) ⟨807839, by rfl⟩ : syracuseStep 1077119 = 1615679) B1615679
theorem B2420711 : Blo 714321 2420711 := bstep (se 1 (by rfl) ⟨1815533, by rfl⟩ : syracuseStep 2420711 = 3631067) B3631067
theorem B1208297 : Blo 714321 1208297 := bstep (se 2 (by rfl) ⟨453111, by rfl⟩ : syracuseStep 1208297 = 906223) B906223
theorem B1208351 : Blo 714321 1208351 := bstep (se 1 (by rfl) ⟨906263, by rfl⟩ : syracuseStep 1208351 = 1812527) B1812527
theorem B716831 : Blo 714321 716831 := bstep (se 1 (by rfl) ⟨537623, by rfl⟩ : syracuseStep 716831 = 1075247) B1075247
theorem B717007 : Blo 714321 717007 := bstep (se 1 (by rfl) ⟨537755, by rfl⟩ : syracuseStep 717007 = 1075511) B1075511
theorem B1077455 : Blo 714321 1077455 := bstep (se 1 (by rfl) ⟨808091, by rfl⟩ : syracuseStep 1077455 = 1616183) B1616183
theorem B2421035 : Blo 714321 2421035 := bstep (se 1 (by rfl) ⟨1815776, by rfl⟩ : syracuseStep 2421035 = 3631553) B3631553
theorem B717127 : Blo 714321 717127 := bstep (se 1 (by rfl) ⟨537845, by rfl⟩ : syracuseStep 717127 = 1075691) B1075691
theorem B2421089 : Blo 714321 2421089 := bstep (se 2 (by rfl) ⟨907908, by rfl⟩ : syracuseStep 2421089 = 1815817) B1815817
theorem B3633659 : Blo 714321 3633659 := bstep (se 1 (by rfl) ⟨2725244, by rfl⟩ : syracuseStep 3633659 = 5450489) B5450489
theorem B8385113 : Blo 714321 8385113 := bstep (se 2 (by rfl) ⟨3144417, by rfl⟩ : syracuseStep 8385113 = 6288835) B6288835
theorem B35877599 : Blo 714321 35877599 := bstep (se 1 (by rfl) ⟨26908199, by rfl⟩ : syracuseStep 35877599 = 53816399) B53816399
theorem B6877979 : Blo 714321 6877979 := bstep (se 1 (by rfl) ⟨5158484, by rfl⟩ : syracuseStep 6877979 = 10316969) B10316969
theorem B717595 : Blo 714321 717595 := bstep (se 1 (by rfl) ⟨538196, by rfl⟩ : syracuseStep 717595 = 1076393) B1076393
theorem B4584347 : Blo 714321 4584347 := bstep (se 1 (by rfl) ⟨3438260, by rfl⟩ : syracuseStep 4584347 = 6876521) B6876521
theorem B2421737 : Blo 714321 2421737 := bstep (se 2 (by rfl) ⟨908151, by rfl⟩ : syracuseStep 2421737 = 1816303) B1816303
theorem B717871 : Blo 714321 717871 := bstep (se 1 (by rfl) ⟨538403, by rfl⟩ : syracuseStep 717871 = 1076807) B1076807
theorem B16741529 : Blo 714321 16741529 := bstep (se 2 (by rfl) ⟨6278073, by rfl⟩ : syracuseStep 16741529 = 12556147) B12556147
theorem B717991 : Blo 714321 717991 := bstep (se 1 (by rfl) ⟨538493, by rfl⟩ : syracuseStep 717991 = 1076987) B1076987
theorem B3634955 : Blo 714321 3634955 := bstep (se 1 (by rfl) ⟨2726216, by rfl⟩ : syracuseStep 3634955 = 5452433) B5452433
theorem B3438359 : Blo 714321 3438359 := bstep (se 1 (by rfl) ⟨2578769, by rfl⟩ : syracuseStep 3438359 = 5157539) B5157539
theorem B980807 : Blo 714321 980807 := bstep (se 1 (by rfl) ⟨735605, by rfl⟩ : syracuseStep 980807 = 1471211) B1471211
theorem B11597903 : Blo 714321 11597903 := bstep (se 1 (by rfl) ⟨8698427, by rfl⟩ : syracuseStep 11597903 = 17396855) B17396855
theorem B2423033 : Blo 714321 2423033 := bstep (se 2 (by rfl) ⟨908637, by rfl⟩ : syracuseStep 2423033 = 1817275) B1817275
theorem B4356659 : Blo 714321 4356659 := bstep (se 1 (by rfl) ⟨3267494, by rfl⟩ : syracuseStep 4356659 = 6534989) B6534989
theorem B4586321 : Blo 714321 4586321 := bstep (se 2 (by rfl) ⟨1719870, by rfl⟩ : syracuseStep 4586321 = 3439741) B3439741
theorem B4193255 : Blo 714321 4193255 := bstep (se 1 (by rfl) ⟨3144941, by rfl⟩ : syracuseStep 4193255 = 6289883) B6289883
theorem B3439759 : Blo 714321 3439759 := bstep (se 1 (by rfl) ⟨2579819, by rfl⟩ : syracuseStep 3439759 = 5159639) B5159639
theorem B13073761 : Blo 714321 13073761 := bstep (se 2 (by rfl) ⟨4902660, by rfl⟩ : syracuseStep 13073761 = 9805321) B9805321
theorem B8158967 : Blo 714321 8158967 := bstep (se 1 (by rfl) ⟨6119225, by rfl⟩ : syracuseStep 8158967 = 12238451) B12238451
theorem B2293609 : Blo 714321 2293609 := bstep (se 2 (by rfl) ⟨860103, by rfl⟩ : syracuseStep 2293609 = 1720207) B1720207
theorem B1933267 : Blo 714321 1933267 := bstep (se 1 (by rfl) ⟨1449950, by rfl⟩ : syracuseStep 1933267 = 2899901) B2899901
theorem B4587779 : Blo 714321 4587779 := bstep (se 1 (by rfl) ⟨3440834, by rfl⟩ : syracuseStep 4587779 = 6881669) B6881669
theorem B3441143 : Blo 714321 3441143 := bstep (se 1 (by rfl) ⟨2580857, by rfl⟩ : syracuseStep 3441143 = 5161715) B5161715
theorem B2720249 : Blo 714321 2720249 := bstep (se 2 (by rfl) ⟨1020093, by rfl⟩ : syracuseStep 2720249 = 2040187) B2040187
theorem B47055595 : Blo 714321 47055595 := bstep (se 1 (by rfl) ⟨35291696, by rfl⟩ : syracuseStep 47055595 = 70583393) B70583393
theorem B2721235 : Blo 714321 2721235 := bstep (se 1 (by rfl) ⟨2040926, by rfl⟩ : syracuseStep 2721235 = 4081853) B4081853
theorem B23529113 : Blo 714321 23529113 := bstep (se 2 (by rfl) ⟨8823417, by rfl⟩ : syracuseStep 23529113 = 17646835) B17646835
theorem B7734959 : Blo 714321 7734959 := bstep (se 1 (by rfl) ⟨5801219, by rfl⟩ : syracuseStep 7734959 = 11602439) B11602439
theorem B2722025 : Blo 714321 2722025 := bstep (se 2 (by rfl) ⟨1020759, by rfl⟩ : syracuseStep 2722025 = 2041519) B2041519
theorem B1018271 : Blo 714321 1018271 := bstep (se 1 (by rfl) ⟨763703, by rfl⟩ : syracuseStep 1018271 = 1527407) B1527407
theorem B1018823 : Blo 714321 1018823 := bstep (se 1 (by rfl) ⟨764117, by rfl⟩ : syracuseStep 1018823 = 1528235) B1528235
theorem B21237137 : Blo 714321 21237137 := bstep (se 2 (by rfl) ⟨7963926, by rfl⟩ : syracuseStep 21237137 = 15927853) B15927853
theorem B1609721 : Blo 714321 1609721 := bstep (se 2 (by rfl) ⟨603645, by rfl⟩ : syracuseStep 1609721 = 1207291) B1207291
theorem B5804207 : Blo 714321 5804207 := bstep (se 1 (by rfl) ⟨4353155, by rfl⟩ : syracuseStep 5804207 = 8706311) B8706311
theorem B3051755 : Blo 714321 3051755 := bstep (se 1 (by rfl) ⟨2288816, by rfl⟩ : syracuseStep 3051755 = 4577633) B4577633
theorem B12260321 : Blo 714321 12260321 := bstep (se 2 (by rfl) ⟨4597620, by rfl⟩ : syracuseStep 12260321 = 9195241) B9195241
theorem B4887535 : Blo 714321 4887535 := bstep (se 1 (by rfl) ⟨3665651, by rfl⟩ : syracuseStep 4887535 = 7331303) B7331303
theorem B1381799 : Blo 714321 1381799 := bstep (se 1 (by rfl) ⟨1036349, by rfl⟩ : syracuseStep 1381799 = 2072699) B2072699
theorem B2299529 : Blo 714321 2299529 := bstep (se 2 (by rfl) ⟨862323, by rfl⟩ : syracuseStep 2299529 = 1724647) B1724647
theorem B1611503 : Blo 714321 1611503 := bstep (se 1 (by rfl) ⟨1208627, by rfl⟩ : syracuseStep 1611503 = 2417255) B2417255
theorem B1611719 : Blo 714321 1611719 := bstep (se 1 (by rfl) ⟨1208789, by rfl⟩ : syracuseStep 1611719 = 2417579) B2417579
theorem B4069439 : Blo 714321 4069439 := bstep (se 1 (by rfl) ⟨3052079, by rfl⟩ : syracuseStep 4069439 = 6104159) B6104159
theorem B5511377 : Blo 714321 5511377 := bstep (se 2 (by rfl) ⟨2066766, by rfl⟩ : syracuseStep 5511377 = 4133533) B4133533
theorem B1546523 : Blo 714321 1546523 := bstep (se 1 (by rfl) ⟨1159892, by rfl⟩ : syracuseStep 1546523 = 2319785) B2319785
theorem B1612079 : Blo 714321 1612079 := bstep (se 1 (by rfl) ⟨1209059, by rfl⟩ : syracuseStep 1612079 = 2418119) B2418119
theorem B1808801 : Blo 714321 1808801 := bstep (se 2 (by rfl) ⟨678300, by rfl⟩ : syracuseStep 1808801 = 1356601) B1356601
theorem B11182013 : Blo 714321 11182013 := bstep (se 3 (by rfl) ⟨2096627, by rfl⟩ : syracuseStep 11182013 = 4193255) B4193255
theorem B13770719 : Blo 714321 13770719 := bstep (se 1 (by rfl) ⟨10328039, by rfl⟩ : syracuseStep 13770719 = 20656079) B20656079
theorem B1613807 : Blo 714321 1613807 := bstep (se 1 (by rfl) ⟨1210355, by rfl⟩ : syracuseStep 1613807 = 2420711) B2420711
theorem B1614023 : Blo 714321 1614023 := bstep (se 1 (by rfl) ⟨1210517, by rfl⟩ : syracuseStep 1614023 = 2421035) B2421035
theorem B1614059 : Blo 714321 1614059 := bstep (se 1 (by rfl) ⟨1210544, by rfl⟩ : syracuseStep 1614059 = 2421089) B2421089
theorem B3056231 : Blo 714321 3056231 := bstep (se 1 (by rfl) ⟨2292173, by rfl⟩ : syracuseStep 3056231 = 4584347) B4584347
theorem B1614491 : Blo 714321 1614491 := bstep (se 1 (by rfl) ⟨1210868, by rfl⟩ : syracuseStep 1614491 = 2421737) B2421737
theorem B1615355 : Blo 714321 1615355 := bstep (se 1 (by rfl) ⟨1211516, by rfl⟩ : syracuseStep 1615355 = 2423033) B2423033
theorem B3057547 : Blo 714321 3057547 := bstep (se 1 (by rfl) ⟨2293160, by rfl⟩ : syracuseStep 3057547 = 4586321) B4586321
theorem B12396563 : Blo 714321 12396563 := bstep (se 1 (by rfl) ⟨9297422, by rfl⟩ : syracuseStep 12396563 = 18594845) B18594845
theorem B3058145 : Blo 714321 3058145 := bstep (se 2 (by rfl) ⟨1146804, by rfl⟩ : syracuseStep 3058145 = 2293609) B2293609
theorem B1813691 : Blo 714321 1813691 := bstep (se 1 (by rfl) ⟨1360268, by rfl⟩ : syracuseStep 1813691 = 2720537) B2720537
theorem B3616649 : Blo 714321 3616649 := bstep (se 2 (by rfl) ⟨1356243, by rfl⟩ : syracuseStep 3616649 = 2712487) B2712487
theorem B1290401 : Blo 714321 1290401 := bstep (se 2 (by rfl) ⟨483900, by rfl⟩ : syracuseStep 1290401 = 967801) B967801
theorem B1815007 : Blo 714321 1815007 := bstep (se 1 (by rfl) ⟨1361255, by rfl⟩ : syracuseStep 1815007 = 2722511) B2722511
theorem B5223149 : Blo 714321 5223149 := bstep (se 3 (by rfl) ⟨979340, by rfl⟩ : syracuseStep 5223149 = 1958681) B1958681
theorem B6108155 : Blo 714321 6108155 := bstep (se 1 (by rfl) ⟨4581116, by rfl⟩ : syracuseStep 6108155 = 9162233) B9162233
theorem B1815635 : Blo 714321 1815635 := bstep (se 1 (by rfl) ⟨1361726, by rfl⟩ : syracuseStep 1815635 = 2723453) B2723453
theorem B2045051 : Blo 714321 2045051 := bstep (se 1 (by rfl) ⟨1533788, by rfl⟩ : syracuseStep 2045051 = 3067577) B3067577
theorem B1815929 : Blo 714321 1815929 := bstep (se 2 (by rfl) ⟨680973, by rfl⟩ : syracuseStep 1815929 = 1361947) B1361947
theorem B1357307 : Blo 714321 1357307 := bstep (se 1 (by rfl) ⟨1017980, by rfl⟩ : syracuseStep 1357307 = 2035961) B2035961
theorem B41334299 : Blo 714321 41334299 := bstep (se 1 (by rfl) ⟨31000724, by rfl⟩ : syracuseStep 41334299 = 62001449) B62001449
theorem B1226377 : Blo 714321 1226377 := bstep (se 2 (by rfl) ⟨459891, by rfl⟩ : syracuseStep 1226377 = 919783) B919783
theorem B9812285 : Blo 714321 9812285 := bstep (se 3 (by rfl) ⟨1839803, by rfl⟩ : syracuseStep 9812285 = 3679607) B3679607
theorem B1554785 : Blo 714321 1554785 := bstep (se 2 (by rfl) ⟨583044, by rfl⟩ : syracuseStep 1554785 = 1166089) B1166089
theorem B11156023 : Blo 714321 11156023 := bstep (se 1 (by rfl) ⟨8367017, by rfl⟩ : syracuseStep 11156023 = 16734035) B16734035
theorem B9157211 : Blo 714321 9157211 := bstep (se 1 (by rfl) ⟨6867908, by rfl⟩ : syracuseStep 9157211 = 13735817) B13735817
theorem B6109931 : Blo 714321 6109931 := bstep (se 1 (by rfl) ⟨4582448, by rfl⟩ : syracuseStep 6109931 = 9164897) B9164897
theorem B965659 : Blo 714321 965659 := bstep (se 1 (by rfl) ⟨724244, by rfl⟩ : syracuseStep 965659 = 1448489) B1448489
theorem B3620051 : Blo 714321 3620051 := bstep (se 1 (by rfl) ⟨2715038, by rfl⟩ : syracuseStep 3620051 = 5430077) B5430077
theorem B1327241 : Blo 714321 1327241 := bstep (se 2 (by rfl) ⟨497715, by rfl⟩ : syracuseStep 1327241 = 995431) B995431
theorem B11649419 : Blo 714321 11649419 := bstep (se 1 (by rfl) ⟨8737064, by rfl⟩ : syracuseStep 11649419 = 17474129) B17474129
theorem B1721417 : Blo 714321 1721417 := bstep (se 2 (by rfl) ⟨645531, by rfl⟩ : syracuseStep 1721417 = 1291063) B1291063
theorem B3621995 : Blo 714321 3621995 := bstep (se 1 (by rfl) ⟨2716496, by rfl⟩ : syracuseStep 3621995 = 5432993) B5432993
theorem B19613495 : Blo 714321 19613495 := bstep (se 1 (by rfl) ⟨14710121, by rfl⟩ : syracuseStep 19613495 = 29420243) B29420243
theorem B805351 : Blo 714321 805351 := bstep (se 1 (by rfl) ⟨604013, by rfl⟩ : syracuseStep 805351 = 1208027) B1208027
theorem B805531 : Blo 714321 805531 := bstep (se 1 (by rfl) ⟨604148, by rfl⟩ : syracuseStep 805531 = 1208297) B1208297
theorem B805567 : Blo 714321 805567 := bstep (se 1 (by rfl) ⟨604175, by rfl⟩ : syracuseStep 805567 = 1208351) B1208351
theorem B5590075 : Blo 714321 5590075 := bstep (se 1 (by rfl) ⟨4192556, by rfl⟩ : syracuseStep 5590075 = 8385113) B8385113
theorem B1363169 : Blo 714321 1363169 := bstep (se 2 (by rfl) ⟨511188, by rfl⟩ : syracuseStep 1363169 = 1022377) B1022377
theorem B11161019 : Blo 714321 11161019 := bstep (se 1 (by rfl) ⟨8370764, by rfl⟩ : syracuseStep 11161019 = 16741529) B16741529
theorem B3067951 : Blo 714321 3067951 := bstep (se 1 (by rfl) ⟨2300963, by rfl⟩ : syracuseStep 3067951 = 4601927) B4601927
theorem B2904439 : Blo 714321 2904439 := bstep (se 1 (by rfl) ⟨2178329, by rfl⟩ : syracuseStep 2904439 = 4356659) B4356659
theorem B5427647 : Blo 714321 5427647 := bstep (se 1 (by rfl) ⟨4070735, by rfl⟩ : syracuseStep 5427647 = 8141471) B8141471
theorem B6542137 : Blo 714321 6542137 := bstep (se 2 (by rfl) ⟨2453301, by rfl⟩ : syracuseStep 6542137 = 4906603) B4906603
theorem B2905217 : Blo 714321 2905217 := bstep (se 2 (by rfl) ⟨1089456, by rfl⟩ : syracuseStep 2905217 = 2178913) B2178913
theorem B2577689 : Blo 714321 2577689 := bstep (se 2 (by rfl) ⟨966633, by rfl⟩ : syracuseStep 2577689 = 1933267) B1933267
theorem B6280859 : Blo 714321 6280859 := bstep (se 1 (by rfl) ⟨4710644, by rfl⟩ : syracuseStep 6280859 = 9421289) B9421289
theorem B5822239 : Blo 714321 5822239 := bstep (se 1 (by rfl) ⟨4366679, by rfl⟩ : syracuseStep 5822239 = 8733359) B8733359
theorem B2414717 : Blo 714321 2414717 := bstep (se 3 (by rfl) ⟨452759, by rfl⟩ : syracuseStep 2414717 = 905519) B905519
theorem B2414879 : Blo 714321 2414879 := bstep (se 1 (by rfl) ⟨1811159, by rfl⟩ : syracuseStep 2414879 = 3622319) B3622319
theorem B9787805 : Blo 714321 9787805 := bstep (se 3 (by rfl) ⟨1835213, by rfl⟩ : syracuseStep 9787805 = 3670427) B3670427
theorem B1071719 : Blo 714321 1071719 := bstep (se 1 (by rfl) ⟨803789, by rfl⟩ : syracuseStep 1071719 = 1607579) B1607579
theorem B1530593 : Blo 714321 1530593 := bstep (se 2 (by rfl) ⟨573972, by rfl⟩ : syracuseStep 1530593 = 1147945) B1147945
theorem B1071851 : Blo 714321 1071851 := bstep (se 1 (by rfl) ⟨803888, by rfl⟩ : syracuseStep 1071851 = 1607777) B1607777
theorem B2415527 : Blo 714321 2415527 := bstep (se 1 (by rfl) ⟨1811645, by rfl⟩ : syracuseStep 2415527 = 3623291) B3623291
theorem B1072223 : Blo 714321 1072223 := bstep (se 1 (by rfl) ⟨804167, by rfl⟩ : syracuseStep 1072223 = 1608335) B1608335
theorem B1072265 : Blo 714321 1072265 := bstep (se 2 (by rfl) ⟨402099, by rfl⟩ : syracuseStep 1072265 = 804199) B804199
theorem B1072283 : Blo 714321 1072283 := bstep (se 1 (by rfl) ⟨804212, by rfl⟩ : syracuseStep 1072283 = 1608425) B1608425
theorem B1072319 : Blo 714321 1072319 := bstep (se 1 (by rfl) ⟨804239, by rfl⟩ : syracuseStep 1072319 = 1608479) B1608479
theorem B2907359 : Blo 714321 2907359 := bstep (se 1 (by rfl) ⟨2180519, by rfl⟩ : syracuseStep 2907359 = 4361039) B4361039
theorem B1072751 : Blo 714321 1072751 := bstep (se 1 (by rfl) ⟨804563, by rfl⟩ : syracuseStep 1072751 = 1609127) B1609127
theorem B1072871 : Blo 714321 1072871 := bstep (se 1 (by rfl) ⟨804653, by rfl⟩ : syracuseStep 1072871 = 1609307) B1609307
theorem B2416553 : Blo 714321 2416553 := bstep (se 2 (by rfl) ⟨906207, by rfl⟩ : syracuseStep 2416553 = 1812415) B1812415
theorem B4907263 : Blo 714321 4907263 := bstep (se 1 (by rfl) ⟨3680447, by rfl⟩ : syracuseStep 4907263 = 7360895) B7360895
theorem B2417309 : Blo 714321 2417309 := bstep (se 3 (by rfl) ⟨453245, by rfl⟩ : syracuseStep 2417309 = 906491) B906491
theorem B3225445829 : Blo 714321 3225445829 := bstep (se 4 (by rfl) ⟨302385546, by rfl⟩ : syracuseStep 3225445829 = 604771093) B604771093
theorem B2090473 : Blo 714321 2090473 := bstep (se 2 (by rfl) ⟨783927, by rfl⟩ : syracuseStep 2090473 = 1567855) B1567855
theorem B714343 : Blo 714321 714343 := bstep (se 1 (by rfl) ⟨535757, by rfl⟩ : syracuseStep 714343 = 1071515) B1071515
theorem B25487083 : Blo 714321 25487083 := bstep (se 1 (by rfl) ⟨19115312, by rfl⟩ : syracuseStep 25487083 = 38230625) B38230625
theorem B714607 : Blo 714321 714607 := bstep (se 1 (by rfl) ⟨535955, by rfl⟩ : syracuseStep 714607 = 1071911) B1071911
theorem B1206137 : Blo 714321 1206137 := bstep (se 2 (by rfl) ⟨452301, by rfl⟩ : syracuseStep 1206137 = 904603) B904603
theorem B714623 : Blo 714321 714623 := bstep (se 1 (by rfl) ⟨535967, by rfl⟩ : syracuseStep 714623 = 1071935) B1071935
theorem B1533907 : Blo 714321 1533907 := bstep (se 1 (by rfl) ⟨1150430, by rfl⟩ : syracuseStep 1533907 = 2300861) B2300861
theorem B4089851 : Blo 714321 4089851 := bstep (se 1 (by rfl) ⟨3067388, by rfl⟩ : syracuseStep 4089851 = 6134777) B6134777
theorem B9824267 : Blo 714321 9824267 := bstep (se 1 (by rfl) ⟨7368200, by rfl⟩ : syracuseStep 9824267 = 14736401) B14736401
theorem B714823 : Blo 714321 714823 := bstep (se 1 (by rfl) ⟨536117, by rfl⟩ : syracuseStep 714823 = 1072235) B1072235
theorem B714919 : Blo 714321 714919 := bstep (se 1 (by rfl) ⟨536189, by rfl⟩ : syracuseStep 714919 = 1072379) B1072379
theorem B2615485 : Blo 714321 2615485 := bstep (se 3 (by rfl) ⟨490403, by rfl⟩ : syracuseStep 2615485 = 980807) B980807
theorem B714983 : Blo 714321 714983 := bstep (se 1 (by rfl) ⟨536237, by rfl⟩ : syracuseStep 714983 = 1072475) B1072475
theorem B715003 : Blo 714321 715003 := bstep (se 1 (by rfl) ⟨536252, by rfl⟩ : syracuseStep 715003 = 1072505) B1072505
theorem B715007 : Blo 714321 715007 := bstep (se 1 (by rfl) ⟨536255, by rfl⟩ : syracuseStep 715007 = 1072511) B1072511
theorem B1206697 : Blo 714321 1206697 := bstep (se 2 (by rfl) ⟨452511, by rfl⟩ : syracuseStep 1206697 = 905023) B905023
theorem B715375 : Blo 714321 715375 := bstep (se 1 (by rfl) ⟨536531, by rfl⟩ : syracuseStep 715375 = 1073063) B1073063
theorem B715423 : Blo 714321 715423 := bstep (se 1 (by rfl) ⟨536567, by rfl⟩ : syracuseStep 715423 = 1073135) B1073135
theorem B2419361 : Blo 714321 2419361 := bstep (se 2 (by rfl) ⟨907260, by rfl⟩ : syracuseStep 2419361 = 1814521) B1814521
theorem B1075919 : Blo 714321 1075919 := bstep (se 1 (by rfl) ⟨806939, by rfl⟩ : syracuseStep 1075919 = 1613879) B1613879
theorem B715503 : Blo 714321 715503 := bstep (se 1 (by rfl) ⟨536627, by rfl⟩ : syracuseStep 715503 = 1073255) B1073255
theorem B715591 : Blo 714321 715591 := bstep (se 1 (by rfl) ⟨536693, by rfl⟩ : syracuseStep 715591 = 1073387) B1073387
theorem B715631 : Blo 714321 715631 := bstep (se 1 (by rfl) ⟨536723, by rfl⟩ : syracuseStep 715631 = 1073447) B1073447
theorem B1207163 : Blo 714321 1207163 := bstep (se 1 (by rfl) ⟨905372, by rfl⟩ : syracuseStep 1207163 = 1810745) B1810745
theorem B4090783 : Blo 714321 4090783 := bstep (se 1 (by rfl) ⟨3068087, by rfl⟩ : syracuseStep 4090783 = 6136175) B6136175
theorem B3632039 : Blo 714321 3632039 := bstep (se 1 (by rfl) ⟨2724029, by rfl⟩ : syracuseStep 3632039 = 5448059) B5448059
theorem B715931 : Blo 714321 715931 := bstep (se 1 (by rfl) ⟨536948, by rfl⟩ : syracuseStep 715931 = 1073897) B1073897
theorem B716191 : Blo 714321 716191 := bstep (se 1 (by rfl) ⟨537143, by rfl⟩ : syracuseStep 716191 = 1074287) B1074287
theorem B8154593 : Blo 714321 8154593 := bstep (se 2 (by rfl) ⟨3057972, by rfl⟩ : syracuseStep 8154593 = 6115945) B6115945
theorem B716271 : Blo 714321 716271 := bstep (se 1 (by rfl) ⟨537203, by rfl⟩ : syracuseStep 716271 = 1074407) B1074407
theorem B2420225 : Blo 714321 2420225 := bstep (se 2 (by rfl) ⟨907584, by rfl⟩ : syracuseStep 2420225 = 1815169) B1815169
theorem B716315 : Blo 714321 716315 := bstep (se 1 (by rfl) ⟨537236, by rfl⟩ : syracuseStep 716315 = 1074473) B1074473
theorem B1633895 : Blo 714321 1633895 := bstep (se 1 (by rfl) ⟨1225421, by rfl⟩ : syracuseStep 1633895 = 2450843) B2450843
theorem B1076873 : Blo 714321 1076873 := bstep (se 2 (by rfl) ⟨403827, by rfl⟩ : syracuseStep 1076873 = 807655) B807655
theorem B1076927 : Blo 714321 1076927 := bstep (se 1 (by rfl) ⟨807695, by rfl⟩ : syracuseStep 1076927 = 1615391) B1615391
theorem B716495 : Blo 714321 716495 := bstep (se 1 (by rfl) ⟨537371, by rfl⟩ : syracuseStep 716495 = 1074743) B1074743
theorem B14708567 : Blo 714321 14708567 := bstep (se 1 (by rfl) ⟨11031425, by rfl⟩ : syracuseStep 14708567 = 22062851) B22062851
theorem B716711 : Blo 714321 716711 := bstep (se 1 (by rfl) ⟨537533, by rfl⟩ : syracuseStep 716711 = 1075067) B1075067
theorem B716735 : Blo 714321 716735 := bstep (se 1 (by rfl) ⟨537551, by rfl⟩ : syracuseStep 716735 = 1075103) B1075103
theorem B716891 : Blo 714321 716891 := bstep (se 1 (by rfl) ⟨537668, by rfl⟩ : syracuseStep 716891 = 1075337) B1075337
theorem B716991 : Blo 714321 716991 := bstep (se 1 (by rfl) ⟨537743, by rfl⟩ : syracuseStep 716991 = 1075487) B1075487
theorem B2420927 : Blo 714321 2420927 := bstep (se 1 (by rfl) ⟨1815695, by rfl⟩ : syracuseStep 2420927 = 3631391) B3631391
theorem B717023 : Blo 714321 717023 := bstep (se 1 (by rfl) ⟨537767, by rfl⟩ : syracuseStep 717023 = 1075535) B1075535
theorem B717083 : Blo 714321 717083 := bstep (se 1 (by rfl) ⟨537812, by rfl⟩ : syracuseStep 717083 = 1075625) B1075625
theorem B5042639 : Blo 714321 5042639 := bstep (se 1 (by rfl) ⟨3781979, by rfl⟩ : syracuseStep 5042639 = 7563959) B7563959
theorem B717339 : Blo 714321 717339 := bstep (se 1 (by rfl) ⟨538004, by rfl⟩ : syracuseStep 717339 = 1076009) B1076009
theorem B2421305 : Blo 714321 2421305 := bstep (se 2 (by rfl) ⟨907989, by rfl⟩ : syracuseStep 2421305 = 1815979) B1815979
theorem B717479 : Blo 714321 717479 := bstep (se 1 (by rfl) ⟨538109, by rfl⟩ : syracuseStep 717479 = 1076219) B1076219
theorem B717519 : Blo 714321 717519 := bstep (se 1 (by rfl) ⟨538139, by rfl⟩ : syracuseStep 717519 = 1076279) B1076279
theorem B2421467 : Blo 714321 2421467 := bstep (se 1 (by rfl) ⟨1816100, by rfl⟩ : syracuseStep 2421467 = 3632201) B3632201
theorem B717599 : Blo 714321 717599 := bstep (se 1 (by rfl) ⟨538199, by rfl⟩ : syracuseStep 717599 = 1076399) B1076399
theorem B3633983 : Blo 714321 3633983 := bstep (se 1 (by rfl) ⟨2725487, by rfl⟩ : syracuseStep 3633983 = 5450975) B5450975
theorem B2421575 : Blo 714321 2421575 := bstep (se 1 (by rfl) ⟨1816181, by rfl⟩ : syracuseStep 2421575 = 3632363) B3632363
theorem B717639 : Blo 714321 717639 := bstep (se 1 (by rfl) ⟨538229, by rfl⟩ : syracuseStep 717639 = 1076459) B1076459
theorem B1209323 : Blo 714321 1209323 := bstep (se 1 (by rfl) ⟨906992, by rfl⟩ : syracuseStep 1209323 = 1813985) B1813985
theorem B5174401 : Blo 714321 5174401 := bstep (se 2 (by rfl) ⟨1940400, by rfl⟩ : syracuseStep 5174401 = 3880801) B3880801
theorem B718079 : Blo 714321 718079 := bstep (se 1 (by rfl) ⟨538559, by rfl⟩ : syracuseStep 718079 = 1077119) B1077119
theorem B718303 : Blo 714321 718303 := bstep (se 1 (by rfl) ⟨538727, by rfl⟩ : syracuseStep 718303 = 1077455) B1077455
theorem B1209883 : Blo 714321 1209883 := bstep (se 1 (by rfl) ⟨907412, by rfl⟩ : syracuseStep 1209883 = 1814825) B1814825
theorem B2422439 : Blo 714321 2422439 := bstep (se 1 (by rfl) ⟨1816829, by rfl⟩ : syracuseStep 2422439 = 3633659) B3633659
theorem B23918399 : Blo 714321 23918399 := bstep (se 1 (by rfl) ⟨17938799, by rfl⟩ : syracuseStep 23918399 = 35877599) B35877599
theorem B4585319 : Blo 714321 4585319 := bstep (se 1 (by rfl) ⟨3438989, by rfl⟩ : syracuseStep 4585319 = 6877979) B6877979
theorem B2324695 : Blo 714321 2324695 := bstep (se 1 (by rfl) ⟨1743521, by rfl⟩ : syracuseStep 2324695 = 3487043) B3487043
theorem B1210727 : Blo 714321 1210727 := bstep (se 1 (by rfl) ⟨908045, by rfl⟩ : syracuseStep 1210727 = 1816091) B1816091
theorem B1210855 : Blo 714321 1210855 := bstep (se 1 (by rfl) ⟨908141, by rfl⟩ : syracuseStep 1210855 = 1816283) B1816283
theorem B2423303 : Blo 714321 2423303 := bstep (se 1 (by rfl) ⟨1817477, by rfl⟩ : syracuseStep 2423303 = 3634955) B3634955
theorem B2292239 : Blo 714321 2292239 := bstep (se 1 (by rfl) ⟨1719179, by rfl⟩ : syracuseStep 2292239 = 3438359) B3438359
theorem B5175845 : Blo 714321 5175845 := bstep (se 4 (by rfl) ⟨485235, by rfl⟩ : syracuseStep 5175845 = 970471) B970471
theorem B7731935 : Blo 714321 7731935 := bstep (se 1 (by rfl) ⟨5798951, by rfl⟩ : syracuseStep 7731935 = 11597903) B11597903
theorem B4586345 : Blo 714321 4586345 := bstep (se 2 (by rfl) ⟨1719879, by rfl⟩ : syracuseStep 4586345 = 3439759) B3439759
theorem B2423681 : Blo 714321 2423681 := bstep (se 2 (by rfl) ⟨908880, by rfl⟩ : syracuseStep 2423681 = 1817761) B1817761
theorem B1211375 : Blo 714321 1211375 := bstep (se 1 (by rfl) ⟨908531, by rfl⟩ : syracuseStep 1211375 = 1817063) B1817063
theorem B17431681 : Blo 714321 17431681 := bstep (se 2 (by rfl) ⟨6536880, by rfl⟩ : syracuseStep 17431681 = 13073761) B13073761
theorem B1146395 : Blo 714321 1146395 := bstep (se 1 (by rfl) ⟨859796, by rfl⟩ : syracuseStep 1146395 = 1719593) B1719593
theorem B5439311 : Blo 714321 5439311 := bstep (se 1 (by rfl) ⟨4079483, by rfl⟩ : syracuseStep 5439311 = 8158967) B8158967
theorem B884827 : Blo 714321 884827 := bstep (se 1 (by rfl) ⟨663620, by rfl⟩ : syracuseStep 884827 = 1327241) B1327241
theorem B7766279 : Blo 714321 7766279 := bstep (se 1 (by rfl) ⟨5824709, by rfl⟩ : syracuseStep 7766279 = 11649419) B11649419
theorem B2294095 : Blo 714321 2294095 := bstep (se 1 (by rfl) ⟨1720571, by rfl⟩ : syracuseStep 2294095 = 3441143) B3441143
theorem B13075663 : Blo 714321 13075663 := bstep (se 1 (by rfl) ⟨9806747, by rfl⟩ : syracuseStep 13075663 = 19613495) B19613495
theorem B14158091 : Blo 714321 14158091 := bstep (se 1 (by rfl) ⟨10618568, by rfl⟩ : syracuseStep 14158091 = 21237137) B21237137
theorem B7440679 : Blo 714321 7440679 := bstep (se 1 (by rfl) ⟨5580509, by rfl⟩ : syracuseStep 7440679 = 11161019) B11161019
theorem B33982777 : Blo 714321 33982777 := bstep (se 2 (by rfl) ⟨12743541, by rfl⟩ : syracuseStep 33982777 = 25487083) B25487083
theorem B3869471 : Blo 714321 3869471 := bstep (se 1 (by rfl) ⟨2902103, by rfl⟩ : syracuseStep 3869471 = 5804207) B5804207
theorem B2034503 : Blo 714321 2034503 := bstep (se 1 (by rfl) ⟨1525877, by rfl⟩ : syracuseStep 2034503 = 3051755) B3051755
theorem B4590445 : Blo 714321 4590445 := bstep (se 3 (by rfl) ⟨860708, by rfl⟩ : syracuseStep 4590445 = 1721417) B1721417
theorem B1608929 : Blo 714321 1608929 := bstep (se 2 (by rfl) ⟨603348, by rfl⟩ : syracuseStep 1608929 = 1206697) B1206697
theorem B1936811 : Blo 714321 1936811 := bstep (se 1 (by rfl) ⟨1452608, by rfl⟩ : syracuseStep 1936811 = 2905217) B2905217
theorem B921199 : Blo 714321 921199 := bstep (se 1 (by rfl) ⟨690899, by rfl⟩ : syracuseStep 921199 = 1381799) B1381799
theorem B1609811 : Blo 714321 1609811 := bstep (se 1 (by rfl) ⟨1207358, by rfl⟩ : syracuseStep 1609811 = 2414717) B2414717
theorem B3674251 : Blo 714321 3674251 := bstep (se 1 (by rfl) ⟨2755688, by rfl⟩ : syracuseStep 3674251 = 5511377) B5511377
theorem B1609919 : Blo 714321 1609919 := bstep (se 1 (by rfl) ⟨1207439, by rfl⟩ : syracuseStep 1609919 = 2414879) B2414879
theorem B6525203 : Blo 714321 6525203 := bstep (se 1 (by rfl) ⟨4893902, by rfl⟩ : syracuseStep 6525203 = 9787805) B9787805
theorem B16748957 : Blo 714321 16748957 := bstep (se 3 (by rfl) ⟨3140429, by rfl⟩ : syracuseStep 16748957 = 6280859) B6280859
theorem B1020395 : Blo 714321 1020395 := bstep (se 1 (by rfl) ⟨765296, by rfl⟩ : syracuseStep 1020395 = 1530593) B1530593
theorem B1610351 : Blo 714321 1610351 := bstep (se 1 (by rfl) ⟨1207763, by rfl⟩ : syracuseStep 1610351 = 2415527) B2415527
theorem B1938239 : Blo 714321 1938239 := bstep (se 1 (by rfl) ⟨1453679, by rfl⟩ : syracuseStep 1938239 = 2907359) B2907359
theorem B1611035 : Blo 714321 1611035 := bstep (se 1 (by rfl) ⟨1208276, by rfl⟩ : syracuseStep 1611035 = 2416553) B2416553
theorem B9180479 : Blo 714321 9180479 := bstep (se 1 (by rfl) ⟨6885359, by rfl⟩ : syracuseStep 9180479 = 13770719) B13770719
theorem B2037487 : Blo 714321 2037487 := bstep (se 1 (by rfl) ⟨1528115, by rfl⟩ : syracuseStep 2037487 = 3056231) B3056231
theorem B1611539 : Blo 714321 1611539 := bstep (se 1 (by rfl) ⟨1208654, by rfl⟩ : syracuseStep 1611539 = 2417309) B2417309
theorem B3872585 : Blo 714321 3872585 := bstep (se 2 (by rfl) ⟨1452219, by rfl⟩ : syracuseStep 3872585 = 2904439) B2904439
theorem B2726567 : Blo 714321 2726567 := bstep (se 1 (by rfl) ⟨2044925, by rfl⟩ : syracuseStep 2726567 = 4089851) B4089851
theorem B8264375 : Blo 714321 8264375 := bstep (se 1 (by rfl) ⟨6198281, by rfl⟩ : syracuseStep 8264375 = 12396563) B12396563
theorem B2038763 : Blo 714321 2038763 := bstep (se 1 (by rfl) ⟨1529072, by rfl⟩ : syracuseStep 2038763 = 3058145) B3058145
theorem B1612907 : Blo 714321 1612907 := bstep (se 1 (by rfl) ⟨1209680, by rfl⟩ : syracuseStep 1612907 = 2419361) B2419361
theorem B1613177 : Blo 714321 1613177 := bstep (se 2 (by rfl) ⟨604941, by rfl⟩ : syracuseStep 1613177 = 1209883) B1209883
theorem B1613483 : Blo 714321 1613483 := bstep (se 1 (by rfl) ⟨1210112, by rfl⟩ : syracuseStep 1613483 = 2420225) B2420225
theorem B1089263 : Blo 714321 1089263 := bstep (se 1 (by rfl) ⟨816947, by rfl⟩ : syracuseStep 1089263 = 1633895) B1633895
theorem B9805711 : Blo 714321 9805711 := bstep (se 1 (by rfl) ⟨7354283, by rfl⟩ : syracuseStep 9805711 = 14708567) B14708567
theorem B860267 : Blo 714321 860267 := bstep (se 1 (by rfl) ⟨645200, by rfl⟩ : syracuseStep 860267 = 1290401) B1290401
theorem B1613951 : Blo 714321 1613951 := bstep (se 1 (by rfl) ⟨1210463, by rfl⟩ : syracuseStep 1613951 = 2420927) B2420927
theorem B1614203 : Blo 714321 1614203 := bstep (se 1 (by rfl) ⟨1210652, by rfl⟩ : syracuseStep 1614203 = 2421305) B2421305
theorem B1614311 : Blo 714321 1614311 := bstep (se 1 (by rfl) ⟨1210733, by rfl⟩ : syracuseStep 1614311 = 2421467) B2421467
theorem B3482099 : Blo 714321 3482099 := bstep (se 1 (by rfl) ⟨2611574, by rfl⟩ : syracuseStep 3482099 = 5223149) B5223149
theorem B1614383 : Blo 714321 1614383 := bstep (se 1 (by rfl) ⟨1210787, by rfl⟩ : syracuseStep 1614383 = 2421575) B2421575
theorem B1614473 : Blo 714321 1614473 := bstep (se 2 (by rfl) ⟨605427, by rfl⟩ : syracuseStep 1614473 = 1210855) B1210855
theorem B4072103 : Blo 714321 4072103 := bstep (se 1 (by rfl) ⟨3054077, by rfl⟩ : syracuseStep 4072103 = 6108155) B6108155
theorem B1614959 : Blo 714321 1614959 := bstep (se 1 (by rfl) ⟨1211219, by rfl⟩ : syracuseStep 1614959 = 2422439) B2422439
theorem B3056879 : Blo 714321 3056879 := bstep (se 1 (by rfl) ⟨2292659, by rfl⟩ : syracuseStep 3056879 = 4585319) B4585319
theorem B1287545 : Blo 714321 1287545 := bstep (se 2 (by rfl) ⟨482829, by rfl⟩ : syracuseStep 1287545 = 965659) B965659
theorem B23242241 : Blo 714321 23242241 := bstep (se 2 (by rfl) ⟨8715840, by rfl⟩ : syracuseStep 23242241 = 17431681) B17431681
theorem B1615535 : Blo 714321 1615535 := bstep (se 1 (by rfl) ⟨1211651, by rfl⟩ : syracuseStep 1615535 = 2423303) B2423303
theorem B3450563 : Blo 714321 3450563 := bstep (se 1 (by rfl) ⟨2587922, by rfl⟩ : syracuseStep 3450563 = 5175845) B5175845
theorem B6104807 : Blo 714321 6104807 := bstep (se 1 (by rfl) ⟨4578605, by rfl⟩ : syracuseStep 6104807 = 9157211) B9157211
theorem B5154623 : Blo 714321 5154623 := bstep (se 1 (by rfl) ⟨3865967, by rfl⟩ : syracuseStep 5154623 = 7731935) B7731935
theorem B4073287 : Blo 714321 4073287 := bstep (se 1 (by rfl) ⟨3054965, by rfl⟩ : syracuseStep 4073287 = 6109931) B6109931
theorem B3057563 : Blo 714321 3057563 := bstep (se 1 (by rfl) ⟨2293172, by rfl⟩ : syracuseStep 3057563 = 4586345) B4586345
theorem B1615787 : Blo 714321 1615787 := bstep (se 1 (by rfl) ⟨1211840, by rfl⟩ : syracuseStep 1615787 = 2423681) B2423681
theorem B764263 : Blo 714321 764263 := bstep (se 1 (by rfl) ⟨573197, by rfl⟩ : syracuseStep 764263 = 1146395) B1146395
theorem B1813499 : Blo 714321 1813499 := bstep (se 1 (by rfl) ⟨1360124, by rfl⟩ : syracuseStep 1813499 = 2720249) B2720249
theorem B12234077 : Blo 714321 12234077 := bstep (se 3 (by rfl) ⟨2293889, by rfl⟩ : syracuseStep 12234077 = 4587779) B4587779
theorem B5156639 : Blo 714321 5156639 := bstep (se 1 (by rfl) ⟨3867479, by rfl⟩ : syracuseStep 5156639 = 7734959) B7734959
theorem B13447037 : Blo 714321 13447037 := bstep (se 3 (by rfl) ⟨2521319, by rfl⟩ : syracuseStep 13447037 = 5042639) B5042639
theorem B1814683 : Blo 714321 1814683 := bstep (se 1 (by rfl) ⟨1361012, by rfl⟩ : syracuseStep 1814683 = 2722025) B2722025
theorem B4076729 : Blo 714321 4076729 := bstep (se 2 (by rfl) ⟨1528773, by rfl⟩ : syracuseStep 4076729 = 3057547) B3057547
theorem B3487313 : Blo 714321 3487313 := bstep (se 2 (by rfl) ⟨1307742, by rfl⟩ : syracuseStep 3487313 = 2615485) B2615485
theorem B3618431 : Blo 714321 3618431 := bstep (se 1 (by rfl) ⟨2713823, by rfl⟩ : syracuseStep 3618431 = 5427647) B5427647
theorem B8173547 : Blo 714321 8173547 := bstep (se 1 (by rfl) ⟨6130160, by rfl⟩ : syracuseStep 8173547 = 12260321) B12260321
theorem B1718459 : Blo 714321 1718459 := bstep (se 1 (by rfl) ⟨1288844, by rfl⟩ : syracuseStep 1718459 = 2577689) B2577689
theorem B5454377 : Blo 714321 5454377 := bstep (se 2 (by rfl) ⟨2045391, by rfl⟩ : syracuseStep 5454377 = 4090783) B4090783
theorem B7453433 : Blo 714321 7453433 := bstep (se 2 (by rfl) ⟨2795037, by rfl⟩ : syracuseStep 7453433 = 5590075) B5590075
theorem B1031015 : Blo 714321 1031015 := bstep (se 1 (by rfl) ⟨773261, by rfl⟩ : syracuseStep 1031015 = 1546523) B1546523
theorem B7454675 : Blo 714321 7454675 := bstep (se 1 (by rfl) ⟨5591006, by rfl⟩ : syracuseStep 7454675 = 11182013) B11182013
theorem B804091 : Blo 714321 804091 := bstep (se 1 (by rfl) ⟨603068, by rfl⟩ : syracuseStep 804091 = 1206137) B1206137
theorem B6899201 : Blo 714321 6899201 := bstep (se 2 (by rfl) ⟨2587200, by rfl⟩ : syracuseStep 6899201 = 5174401) B5174401
theorem B804775 : Blo 714321 804775 := bstep (se 1 (by rfl) ⟨603581, by rfl⟩ : syracuseStep 804775 = 1207163) B1207163
theorem B2411099 : Blo 714321 2411099 := bstep (se 1 (by rfl) ⟨1808324, by rfl⟩ : syracuseStep 2411099 = 3616649) B3616649
theorem B3099593 : Blo 714321 3099593 := bstep (se 2 (by rfl) ⟨1162347, by rfl⟩ : syracuseStep 3099593 = 2324695) B2324695
theorem B806215 : Blo 714321 806215 := bstep (se 1 (by rfl) ⟨604661, by rfl⟩ : syracuseStep 806215 = 1209323) B1209323
theorem B6540677 : Blo 714321 6540677 := bstep (se 4 (by rfl) ⟨613188, by rfl⟩ : syracuseStep 6540677 = 1226377) B1226377
theorem B1363367 : Blo 714321 1363367 := bstep (se 1 (by rfl) ⟨1022525, by rfl⟩ : syracuseStep 1363367 = 2045051) B2045051
theorem B904871 : Blo 714321 904871 := bstep (se 1 (by rfl) ⟨678653, by rfl⟩ : syracuseStep 904871 = 1357307) B1357307
theorem B15945599 : Blo 714321 15945599 := bstep (se 1 (by rfl) ⟨11959199, by rfl⟩ : syracuseStep 15945599 = 23918399) B23918399
theorem B6541523 : Blo 714321 6541523 := bstep (se 1 (by rfl) ⟨4906142, by rfl⟩ : syracuseStep 6541523 = 9812285) B9812285
theorem B1036523 : Blo 714321 1036523 := bstep (se 1 (by rfl) ⟨777392, by rfl⟩ : syracuseStep 1036523 = 1554785) B1554785
theorem B807151 : Blo 714321 807151 := bstep (se 1 (by rfl) ⟨605363, by rfl⟩ : syracuseStep 807151 = 1210727) B1210727
theorem B1528159 : Blo 714321 1528159 := bstep (se 1 (by rfl) ⟨1146119, by rfl⟩ : syracuseStep 1528159 = 2292239) B2292239
theorem B807583 : Blo 714321 807583 := bstep (se 1 (by rfl) ⟨605687, by rfl⟩ : syracuseStep 807583 = 1211375) B1211375
theorem B2413367 : Blo 714321 2413367 := bstep (se 1 (by rfl) ⟨1810025, by rfl⟩ : syracuseStep 2413367 = 3620051) B3620051
theorem B8180837 : Blo 714321 8180837 := bstep (se 4 (by rfl) ⟨766953, by rfl⟩ : syracuseStep 8180837 = 1533907) B1533907
theorem B3626207 : Blo 714321 3626207 := bstep (se 1 (by rfl) ⟨2719655, by rfl⟩ : syracuseStep 3626207 = 5439311) B5439311
theorem B6543017 : Blo 714321 6543017 := bstep (se 2 (by rfl) ⟨2453631, by rfl⟩ : syracuseStep 6543017 = 4907263) B4907263
theorem B2414663 : Blo 714321 2414663 := bstep (se 1 (by rfl) ⟨1810997, by rfl⟩ : syracuseStep 2414663 = 3621995) B3621995
theorem B62740793 : Blo 714321 62740793 := bstep (se 2 (by rfl) ⟨23527797, by rfl⟩ : syracuseStep 62740793 = 47055595) B47055595
theorem B15686075 : Blo 714321 15686075 := bstep (se 1 (by rfl) ⟨11764556, by rfl⟩ : syracuseStep 15686075 = 23529113) B23529113
theorem B3628313 : Blo 714321 3628313 := bstep (se 2 (by rfl) ⟨1360617, by rfl⟩ : syracuseStep 3628313 = 2721235) B2721235
theorem B1073147 : Blo 714321 1073147 := bstep (se 1 (by rfl) ⟨804860, by rfl⟩ : syracuseStep 1073147 = 1609721) B1609721
theorem B1073801 : Blo 714321 1073801 := bstep (se 2 (by rfl) ⟨402675, by rfl⟩ : syracuseStep 1073801 = 805351) B805351
theorem B1074041 : Blo 714321 1074041 := bstep (se 2 (by rfl) ⟨402765, by rfl⟩ : syracuseStep 1074041 = 805531) B805531
theorem B1074089 : Blo 714321 1074089 := bstep (se 2 (by rfl) ⟨402783, by rfl⟩ : syracuseStep 1074089 = 805567) B805567
theorem B1533019 : Blo 714321 1533019 := bstep (se 1 (by rfl) ⟨1149764, by rfl⟩ : syracuseStep 1533019 = 2299529) B2299529
theorem B1074335 : Blo 714321 1074335 := bstep (se 1 (by rfl) ⟨805751, by rfl⟩ : syracuseStep 1074335 = 1611503) B1611503
theorem B1074479 : Blo 714321 1074479 := bstep (se 1 (by rfl) ⟨805859, by rfl⟩ : syracuseStep 1074479 = 1611719) B1611719
theorem B2712959 : Blo 714321 2712959 := bstep (se 1 (by rfl) ⟨2034719, by rfl⟩ : syracuseStep 2712959 = 4069439) B4069439
theorem B1074719 : Blo 714321 1074719 := bstep (se 1 (by rfl) ⟨806039, by rfl⟩ : syracuseStep 1074719 = 1612079) B1612079
theorem B1205867 : Blo 714321 1205867 := bstep (se 1 (by rfl) ⟨904400, by rfl⟩ : syracuseStep 1205867 = 1808801) B1808801
theorem B34891397 : Blo 714321 34891397 := bstep (se 4 (by rfl) ⟨3271068, by rfl⟩ : syracuseStep 34891397 = 6542137) B6542137
theorem B714479 : Blo 714321 714479 := bstep (se 1 (by rfl) ⟨535859, by rfl⟩ : syracuseStep 714479 = 1071719) B1071719
theorem B714567 : Blo 714321 714567 := bstep (se 1 (by rfl) ⟨535925, by rfl⟩ : syracuseStep 714567 = 1071851) B1071851
theorem B714815 : Blo 714321 714815 := bstep (se 1 (by rfl) ⟨536111, by rfl⟩ : syracuseStep 714815 = 1072223) B1072223
theorem B714843 : Blo 714321 714843 := bstep (se 1 (by rfl) ⟨536132, by rfl⟩ : syracuseStep 714843 = 1072265) B1072265
theorem B714855 : Blo 714321 714855 := bstep (se 1 (by rfl) ⟨536141, by rfl⟩ : syracuseStep 714855 = 1072283) B1072283
theorem B714879 : Blo 714321 714879 := bstep (se 1 (by rfl) ⟨536159, by rfl⟩ : syracuseStep 714879 = 1072319) B1072319
theorem B715167 : Blo 714321 715167 := bstep (se 1 (by rfl) ⟨536375, by rfl⟩ : syracuseStep 715167 = 1072751) B1072751
theorem B715247 : Blo 714321 715247 := bstep (se 1 (by rfl) ⟨536435, by rfl⟩ : syracuseStep 715247 = 1072871) B1072871
theorem B1075871 : Blo 714321 1075871 := bstep (se 1 (by rfl) ⟨806903, by rfl⟩ : syracuseStep 1075871 = 1613807) B1613807
theorem B4090601 : Blo 714321 4090601 := bstep (se 2 (by rfl) ⟨1533975, by rfl⟩ : syracuseStep 4090601 = 3067951) B3067951
theorem B1076015 : Blo 714321 1076015 := bstep (se 1 (by rfl) ⟨807011, by rfl⟩ : syracuseStep 1076015 = 1614023) B1614023
theorem B1076039 : Blo 714321 1076039 := bstep (se 1 (by rfl) ⟨807029, by rfl⟩ : syracuseStep 1076039 = 1614059) B1614059
theorem B1076327 : Blo 714321 1076327 := bstep (se 1 (by rfl) ⟨807245, by rfl⟩ : syracuseStep 1076327 = 1614491) B1614491
theorem B2420009 : Blo 714321 2420009 := bstep (se 2 (by rfl) ⟨907503, by rfl⟩ : syracuseStep 2420009 = 1815007) B1815007
theorem B2150297219 : Blo 714321 2150297219 := bstep (se 1 (by rfl) ⟨1612722914, by rfl⟩ : syracuseStep 2150297219 = 3225445829) B3225445829
theorem B1076903 : Blo 714321 1076903 := bstep (se 1 (by rfl) ⟨807677, by rfl⟩ : syracuseStep 1076903 = 1615355) B1615355
theorem B2715389 : Blo 714321 2715389 := bstep (se 3 (by rfl) ⟨509135, by rfl⟩ : syracuseStep 2715389 = 1018271) B1018271
theorem B6516713 : Blo 714321 6516713 := bstep (se 2 (by rfl) ⟨2443767, by rfl⟩ : syracuseStep 6516713 = 4887535) B4887535
theorem B6549511 : Blo 714321 6549511 := bstep (se 1 (by rfl) ⟨4912133, by rfl⟩ : syracuseStep 6549511 = 9824267) B9824267
theorem B717279 : Blo 714321 717279 := bstep (se 1 (by rfl) ⟨537959, by rfl⟩ : syracuseStep 717279 = 1075919) B1075919
theorem B2421359 : Blo 714321 2421359 := bstep (se 1 (by rfl) ⟨1816019, by rfl⟩ : syracuseStep 2421359 = 3632039) B3632039
theorem B1209127 : Blo 714321 1209127 := bstep (se 1 (by rfl) ⟨906845, by rfl⟩ : syracuseStep 1209127 = 1813691) B1813691
theorem B5436395 : Blo 714321 5436395 := bstep (se 1 (by rfl) ⟨4077296, by rfl⟩ : syracuseStep 5436395 = 8154593) B8154593
theorem B7762985 : Blo 714321 7762985 := bstep (se 2 (by rfl) ⟨2911119, by rfl⟩ : syracuseStep 7762985 = 5822239) B5822239
theorem B717915 : Blo 714321 717915 := bstep (se 1 (by rfl) ⟨538436, by rfl⟩ : syracuseStep 717915 = 1076873) B1076873
theorem B717951 : Blo 714321 717951 := bstep (se 1 (by rfl) ⟨538463, by rfl⟩ : syracuseStep 717951 = 1076927) B1076927
theorem B2716861 : Blo 714321 2716861 := bstep (se 3 (by rfl) ⟨509411, by rfl⟩ : syracuseStep 2716861 = 1018823) B1018823
theorem B2422655 : Blo 714321 2422655 := bstep (se 1 (by rfl) ⟨1816991, by rfl⟩ : syracuseStep 2422655 = 3633983) B3633983
theorem B3635117 : Blo 714321 3635117 := bstep (se 3 (by rfl) ⟨681584, by rfl⟩ : syracuseStep 3635117 = 1363169) B1363169
theorem B1210423 : Blo 714321 1210423 := bstep (se 1 (by rfl) ⟨907817, by rfl⟩ : syracuseStep 1210423 = 1815635) B1815635
theorem B14874697 : Blo 714321 14874697 := bstep (se 2 (by rfl) ⟨5578011, by rfl⟩ : syracuseStep 14874697 = 11156023) B11156023
theorem B1210619 : Blo 714321 1210619 := bstep (se 1 (by rfl) ⟨907964, by rfl⟩ : syracuseStep 1210619 = 1815929) B1815929
theorem B27556199 : Blo 714321 27556199 := bstep (se 1 (by rfl) ⟨20667149, by rfl⟩ : syracuseStep 27556199 = 41334299) B41334299
theorem B44596757 : Blo 714321 44596757 := bstep (se 6 (by rfl) ⟨1045236, by rfl⟩ : syracuseStep 44596757 = 2090473) B2090473
theorem B5177519 : Blo 714321 5177519 := bstep (se 1 (by rfl) ⟨3883139, by rfl⟩ : syracuseStep 5177519 = 7766279) B7766279
theorem B2294045 : Blo 714321 2294045 := bstep (se 3 (by rfl) ⟨430133, by rfl⟩ : syracuseStep 2294045 = 860267) B860267
theorem B79331717 : Blo 714321 79331717 := bstep (se 4 (by rfl) ⟨7437348, by rfl⟩ : syracuseStep 79331717 = 14874697) B14874697
theorem B4719077 : Blo 714321 4719077 := bstep (se 4 (by rfl) ⟨442413, by rfl⟩ : syracuseStep 4719077 = 884827) B884827
theorem B44663885 : Blo 714321 44663885 := bstep (se 3 (by rfl) ⟨8374478, by rfl⟩ : syracuseStep 44663885 = 16748957) B16748957
theorem B2721053 : Blo 714321 2721053 := bstep (se 3 (by rfl) ⟨510197, by rfl⟩ : syracuseStep 2721053 = 1020395) B1020395
theorem B9438727 : Blo 714321 9438727 := bstep (se 1 (by rfl) ⟨7079045, by rfl⟩ : syracuseStep 9438727 = 14158091) B14158091
theorem B39683621 : Blo 714321 39683621 := bstep (se 4 (by rfl) ⟨3720339, by rfl⟩ : syracuseStep 39683621 = 7440679) B7440679
theorem B17434217 : Blo 714321 17434217 := bstep (se 2 (by rfl) ⟨6537831, by rfl⟩ : syracuseStep 17434217 = 13075663) B13075663
theorem B1607399 : Blo 714321 1607399 := bstep (se 1 (by rfl) ⟨1205549, by rfl⟩ : syracuseStep 1607399 = 2411099) B2411099
theorem B2066395 : Blo 714321 2066395 := bstep (se 1 (by rfl) ⟨1549796, by rfl⟩ : syracuseStep 2066395 = 3099593) B3099593
theorem B4360451 : Blo 714321 4360451 := bstep (se 1 (by rfl) ⟨3270338, by rfl⟩ : syracuseStep 4360451 = 6540677) B6540677
theorem B4361015 : Blo 714321 4361015 := bstep (se 1 (by rfl) ⟨3270761, by rfl⟩ : syracuseStep 4361015 = 6541523) B6541523
theorem B69602165 : Blo 714321 69602165 := bstep (se 5 (by rfl) ⟨3262601, by rfl⟩ : syracuseStep 69602165 = 6525203) B6525203
theorem B1019017 : Blo 714321 1019017 := bstep (se 2 (by rfl) ⟨382131, by rfl⟩ : syracuseStep 1019017 = 764263) B764263
theorem B1608911 : Blo 714321 1608911 := bstep (se 1 (by rfl) ⟨1206683, by rfl⟩ : syracuseStep 1608911 = 2413367) B2413367
theorem B4362011 : Blo 714321 4362011 := bstep (se 1 (by rfl) ⟨3271508, by rfl⟩ : syracuseStep 4362011 = 6543017) B6543017
theorem B13733813 : Blo 714321 13733813 := bstep (se 5 (by rfl) ⟨643772, by rfl⟩ : syracuseStep 13733813 = 1287545) B1287545
theorem B1609775 : Blo 714321 1609775 := bstep (se 1 (by rfl) ⟨1207331, by rfl⟩ : syracuseStep 1609775 = 2414663) B2414663
theorem B5509583 : Blo 714321 5509583 := bstep (se 1 (by rfl) ⟨4132187, by rfl⟩ : syracuseStep 5509583 = 8264375) B8264375
theorem B726175 : Blo 714321 726175 := bstep (se 1 (by rfl) ⟨544631, by rfl⟩ : syracuseStep 726175 = 1089263) B1089263
theorem B2037545 : Blo 714321 2037545 := bstep (se 2 (by rfl) ⟨764079, by rfl⟩ : syracuseStep 2037545 = 1528159) B1528159
theorem B1808639 : Blo 714321 1808639 := bstep (se 1 (by rfl) ⟨1356479, by rfl⟩ : syracuseStep 1808639 = 2712959) B2712959
theorem B1612169 : Blo 714321 1612169 := bstep (se 2 (by rfl) ⟨604563, by rfl⟩ : syracuseStep 1612169 = 1209127) B1209127
theorem B2300375 : Blo 714321 2300375 := bstep (se 1 (by rfl) ⟨1725281, by rfl⟩ : syracuseStep 2300375 = 3450563) B3450563
theorem B4069871 : Blo 714321 4069871 := bstep (se 1 (by rfl) ⟨3052403, by rfl⟩ : syracuseStep 4069871 = 6104807) B6104807
theorem B2038375 : Blo 714321 2038375 := bstep (se 1 (by rfl) ⟨1528781, by rfl⟩ : syracuseStep 2038375 = 3057563) B3057563
theorem B2727067 : Blo 714321 2727067 := bstep (se 1 (by rfl) ⟨2045300, by rfl⟩ : syracuseStep 2727067 = 4090601) B4090601
theorem B1613339 : Blo 714321 1613339 := bstep (se 1 (by rfl) ⟨1210004, by rfl⟩ : syracuseStep 1613339 = 2420009) B2420009
theorem B1810259 : Blo 714321 1810259 := bstep (se 1 (by rfl) ⟨1357694, by rfl⟩ : syracuseStep 1810259 = 2715389) B2715389
theorem B1613897 : Blo 714321 1613897 := bstep (se 2 (by rfl) ⟨605211, by rfl⟩ : syracuseStep 1613897 = 1210423) B1210423
theorem B1614239 : Blo 714321 1614239 := bstep (se 1 (by rfl) ⟨1210679, by rfl⟩ : syracuseStep 1614239 = 2421359) B2421359
theorem B1615103 : Blo 714321 1615103 := bstep (se 1 (by rfl) ⟨1211327, by rfl⟩ : syracuseStep 1615103 = 2422655) B2422655
theorem B5449031 : Blo 714321 5449031 := bstep (se 1 (by rfl) ⟨4086773, by rfl⟩ : syracuseStep 5449031 = 8173547) B8173547
theorem B35858765 : Blo 714321 35858765 := bstep (se 3 (by rfl) ⟨6723518, by rfl⟩ : syracuseStep 35858765 = 13447037) B13447037
theorem B29731171 : Blo 714321 29731171 := bstep (se 1 (by rfl) ⟨22298378, by rfl⟩ : syracuseStep 29731171 = 44596757) B44596757
theorem B3058793 : Blo 714321 3058793 := bstep (se 2 (by rfl) ⟨1147047, by rfl⟩ : syracuseStep 3058793 = 2294095) B2294095
theorem B2764061 : Blo 714321 2764061 := bstep (se 3 (by rfl) ⟨518261, by rfl⟩ : syracuseStep 2764061 = 1036523) B1036523
theorem B4599467 : Blo 714321 4599467 := bstep (se 1 (by rfl) ⟨3449600, by rfl⟩ : syracuseStep 4599467 = 6899201) B6899201
theorem B2044025 : Blo 714321 2044025 := bstep (se 2 (by rfl) ⟨766509, by rfl⟩ : syracuseStep 2044025 = 1533019) B1533019
theorem B1356335 : Blo 714321 1356335 := bstep (se 1 (by rfl) ⟨1017251, by rfl⟩ : syracuseStep 1356335 = 2034503) B2034503
theorem B10630399 : Blo 714321 10630399 := bstep (se 1 (by rfl) ⟨7972799, by rfl⟩ : syracuseStep 10630399 = 15945599) B15945599
theorem B1292159 : Blo 714321 1292159 := bstep (se 1 (by rfl) ⟨969119, by rfl⟩ : syracuseStep 1292159 = 1938239) B1938239
theorem B5453891 : Blo 714321 5453891 := bstep (se 1 (by rfl) ⟨4090418, by rfl⟩ : syracuseStep 5453891 = 8180837) B8180837
theorem B41827195 : Blo 714321 41827195 := bstep (se 1 (by rfl) ⟨31370396, by rfl⟩ : syracuseStep 41827195 = 62740793) B62740793
theorem B1817711 : Blo 714321 1817711 := bstep (se 1 (by rfl) ⟨1363283, by rfl⟩ : syracuseStep 1817711 = 2726567) B2726567
theorem B1359175 : Blo 714321 1359175 := bstep (se 1 (by rfl) ⟨1019381, by rfl⟩ : syracuseStep 1359175 = 2038763) B2038763
theorem B8732681 : Blo 714321 8732681 := bstep (se 2 (by rfl) ⟨3274755, by rfl⟩ : syracuseStep 8732681 = 6549511) B6549511
theorem B4899001 : Blo 714321 4899001 := bstep (se 2 (by rfl) ⟨1837125, by rfl⟩ : syracuseStep 4899001 = 3674251) B3674251
theorem B803911 : Blo 714321 803911 := bstep (se 1 (by rfl) ⟨602933, by rfl⟩ : syracuseStep 803911 = 1205867) B1205867
theorem B41829533 : Blo 714321 41829533 := bstep (se 3 (by rfl) ⟨7843037, by rfl⟩ : syracuseStep 41829533 = 15686075) B15686075
theorem B3622481 : Blo 714321 3622481 := bstep (se 2 (by rfl) ⟨1358430, by rfl⟩ : syracuseStep 3622481 = 2716861) B2716861
theorem B4344475 : Blo 714321 4344475 := bstep (se 1 (by rfl) ⟨3258356, by rfl⟩ : syracuseStep 4344475 = 6516713) B6516713
theorem B3624263 : Blo 714321 3624263 := bstep (se 1 (by rfl) ⟨2718197, by rfl⟩ : syracuseStep 3624263 = 5436395) B5436395
theorem B2412287 : Blo 714321 2412287 := bstep (se 1 (by rfl) ⟨1809215, by rfl⟩ : syracuseStep 2412287 = 3618431) B3618431
theorem B5164829 : Blo 714321 5164829 := bstep (se 3 (by rfl) ⟨968405, by rfl⟩ : syracuseStep 5164829 = 1936811) B1936811
theorem B807079 : Blo 714321 807079 := bstep (se 1 (by rfl) ⟨605309, by rfl⟩ : syracuseStep 807079 = 1210619) B1210619
theorem B18370799 : Blo 714321 18370799 := bstep (se 1 (by rfl) ⟨13778099, by rfl⟩ : syracuseStep 18370799 = 27556199) B27556199
theorem B5734125917 : Blo 714321 5734125917 := bstep (se 3 (by rfl) ⟨1075148609, by rfl⟩ : syracuseStep 5734125917 = 2150297219) B2150297219
theorem B2412989 : Blo 714321 2412989 := bstep (se 3 (by rfl) ⟨452435, by rfl⟩ : syracuseStep 2412989 = 904871) B904871
theorem B4968955 : Blo 714321 4968955 := bstep (se 1 (by rfl) ⟨3726716, by rfl⟩ : syracuseStep 4968955 = 7453433) B7453433
theorem B4969783 : Blo 714321 4969783 := bstep (se 1 (by rfl) ⟨3727337, by rfl⟩ : syracuseStep 4969783 = 7454675) B7454675
theorem B1072121 : Blo 714321 1072121 := bstep (se 2 (by rfl) ⟨402045, by rfl⟩ : syracuseStep 1072121 = 804091) B804091
theorem B2579647 : Blo 714321 2579647 := bstep (se 1 (by rfl) ⟨1934735, by rfl⟩ : syracuseStep 2579647 = 3869471) B3869471
theorem B1072619 : Blo 714321 1072619 := bstep (se 1 (by rfl) ⟨804464, by rfl⟩ : syracuseStep 1072619 = 1608929) B1608929
theorem B908911 : Blo 714321 908911 := bstep (se 1 (by rfl) ⟨681683, by rfl⟩ : syracuseStep 908911 = 1363367) B1363367
theorem B5431049 : Blo 714321 5431049 := bstep (se 2 (by rfl) ⟨2036643, by rfl⟩ : syracuseStep 5431049 = 4073287) B4073287
theorem B1073033 : Blo 714321 1073033 := bstep (se 2 (by rfl) ⟨402387, by rfl⟩ : syracuseStep 1073033 = 804775) B804775
theorem B1073207 : Blo 714321 1073207 := bstep (se 1 (by rfl) ⟨804905, by rfl⟩ : syracuseStep 1073207 = 1609811) B1609811
theorem B1073279 : Blo 714321 1073279 := bstep (se 1 (by rfl) ⟨804959, by rfl⟩ : syracuseStep 1073279 = 1609919) B1609919
theorem B1073567 : Blo 714321 1073567 := bstep (se 1 (by rfl) ⟨805175, by rfl⟩ : syracuseStep 1073567 = 1610351) B1610351
theorem B45310369 : Blo 714321 45310369 := bstep (se 2 (by rfl) ⟨16991388, by rfl⟩ : syracuseStep 45310369 = 33982777) B33982777
theorem B8151677 : Blo 714321 8151677 := bstep (se 3 (by rfl) ⟨1528439, by rfl⟩ : syracuseStep 8151677 = 3056879) B3056879
theorem B2417471 : Blo 714321 2417471 := bstep (se 1 (by rfl) ⟨1813103, by rfl⟩ : syracuseStep 2417471 = 3626207) B3626207
theorem B1074023 : Blo 714321 1074023 := bstep (se 1 (by rfl) ⟨805517, by rfl⟩ : syracuseStep 1074023 = 1611035) B1611035
theorem B6120319 : Blo 714321 6120319 := bstep (se 1 (by rfl) ⟨4590239, by rfl⟩ : syracuseStep 6120319 = 9180479) B9180479
theorem B6120593 : Blo 714321 6120593 := bstep (se 2 (by rfl) ⟨2295222, by rfl⟩ : syracuseStep 6120593 = 4590445) B4590445
theorem B1074359 : Blo 714321 1074359 := bstep (se 1 (by rfl) ⟨805769, by rfl⟩ : syracuseStep 1074359 = 1611539) B1611539
theorem B2581723 : Blo 714321 2581723 := bstep (se 1 (by rfl) ⟨1936292, by rfl⟩ : syracuseStep 2581723 = 3872585) B3872585
theorem B9299501 : Blo 714321 9299501 := bstep (se 3 (by rfl) ⟨1743656, by rfl⟩ : syracuseStep 9299501 = 3487313) B3487313
theorem B1074953 : Blo 714321 1074953 := bstep (se 2 (by rfl) ⟨403107, by rfl⟩ : syracuseStep 1074953 = 806215) B806215
theorem B1075271 : Blo 714321 1075271 := bstep (se 1 (by rfl) ⟨806453, by rfl⟩ : syracuseStep 1075271 = 1612907) B1612907
theorem B2418875 : Blo 714321 2418875 := bstep (se 1 (by rfl) ⟨1814156, by rfl⟩ : syracuseStep 2418875 = 3628313) B3628313
theorem B1075451 : Blo 714321 1075451 := bstep (se 1 (by rfl) ⟨806588, by rfl⟩ : syracuseStep 1075451 = 1613177) B1613177
theorem B1075655 : Blo 714321 1075655 := bstep (se 1 (by rfl) ⟨806741, by rfl⟩ : syracuseStep 1075655 = 1613483) B1613483
theorem B715431 : Blo 714321 715431 := bstep (se 1 (by rfl) ⟨536573, by rfl⟩ : syracuseStep 715431 = 1073147) B1073147
theorem B1075967 : Blo 714321 1075967 := bstep (se 1 (by rfl) ⟨806975, by rfl⟩ : syracuseStep 1075967 = 1613951) B1613951
theorem B2419577 : Blo 714321 2419577 := bstep (se 2 (by rfl) ⟨907341, by rfl⟩ : syracuseStep 2419577 = 1814683) B1814683
theorem B1076135 : Blo 714321 1076135 := bstep (se 1 (by rfl) ⟨807101, by rfl⟩ : syracuseStep 1076135 = 1614203) B1614203
theorem B1076201 : Blo 714321 1076201 := bstep (se 2 (by rfl) ⟨403575, by rfl⟩ : syracuseStep 1076201 = 807151) B807151
theorem B1076207 : Blo 714321 1076207 := bstep (se 1 (by rfl) ⟨807155, by rfl⟩ : syracuseStep 1076207 = 1614311) B1614311
theorem B2321399 : Blo 714321 2321399 := bstep (se 1 (by rfl) ⟨1741049, by rfl⟩ : syracuseStep 2321399 = 3482099) B3482099
theorem B1076255 : Blo 714321 1076255 := bstep (se 1 (by rfl) ⟨807191, by rfl⟩ : syracuseStep 1076255 = 1614383) B1614383
theorem B715867 : Blo 714321 715867 := bstep (se 1 (by rfl) ⟨536900, by rfl⟩ : syracuseStep 715867 = 1073801) B1073801
theorem B1076315 : Blo 714321 1076315 := bstep (se 1 (by rfl) ⟨807236, by rfl⟩ : syracuseStep 1076315 = 1614473) B1614473
theorem B2714735 : Blo 714321 2714735 := bstep (se 1 (by rfl) ⟨2036051, by rfl⟩ : syracuseStep 2714735 = 4072103) B4072103
theorem B716027 : Blo 714321 716027 := bstep (se 1 (by rfl) ⟨537020, by rfl⟩ : syracuseStep 716027 = 1074041) B1074041
theorem B716059 : Blo 714321 716059 := bstep (se 1 (by rfl) ⟨537044, by rfl⟩ : syracuseStep 716059 = 1074089) B1074089
theorem B1076639 : Blo 714321 1076639 := bstep (se 1 (by rfl) ⟨807479, by rfl⟩ : syracuseStep 1076639 = 1614959) B1614959
theorem B716223 : Blo 714321 716223 := bstep (se 1 (by rfl) ⟨537167, by rfl⟩ : syracuseStep 716223 = 1074335) B1074335
theorem B716319 : Blo 714321 716319 := bstep (se 1 (by rfl) ⟨537239, by rfl⟩ : syracuseStep 716319 = 1074479) B1074479
theorem B1076777 : Blo 714321 1076777 := bstep (se 2 (by rfl) ⟨403791, by rfl⟩ : syracuseStep 1076777 = 807583) B807583
theorem B15494827 : Blo 714321 15494827 := bstep (se 1 (by rfl) ⟨11621120, by rfl⟩ : syracuseStep 15494827 = 23242241) B23242241
theorem B716479 : Blo 714321 716479 := bstep (se 1 (by rfl) ⟨537359, by rfl⟩ : syracuseStep 716479 = 1074719) B1074719
theorem B23260931 : Blo 714321 23260931 := bstep (se 1 (by rfl) ⟨17445698, by rfl⟩ : syracuseStep 23260931 = 34891397) B34891397
theorem B1077023 : Blo 714321 1077023 := bstep (se 1 (by rfl) ⟨807767, by rfl⟩ : syracuseStep 1077023 = 1615535) B1615535
theorem B3436415 : Blo 714321 3436415 := bstep (se 1 (by rfl) ⟨2577311, by rfl⟩ : syracuseStep 3436415 = 5154623) B5154623
theorem B1077191 : Blo 714321 1077191 := bstep (se 1 (by rfl) ⟨807893, by rfl⟩ : syracuseStep 1077191 = 1615787) B1615787
theorem B717247 : Blo 714321 717247 := bstep (se 1 (by rfl) ⟨537935, by rfl⟩ : syracuseStep 717247 = 1075871) B1075871
theorem B717343 : Blo 714321 717343 := bstep (se 1 (by rfl) ⟨538007, by rfl⟩ : syracuseStep 717343 = 1076015) B1076015
theorem B717359 : Blo 714321 717359 := bstep (se 1 (by rfl) ⟨538019, by rfl⟩ : syracuseStep 717359 = 1076039) B1076039
theorem B1208999 : Blo 714321 1208999 := bstep (se 1 (by rfl) ⟨906749, by rfl⟩ : syracuseStep 1208999 = 1813499) B1813499
theorem B717551 : Blo 714321 717551 := bstep (se 1 (by rfl) ⟨538163, by rfl⟩ : syracuseStep 717551 = 1076327) B1076327
theorem B8156051 : Blo 714321 8156051 := bstep (se 1 (by rfl) ⟨6117038, by rfl⟩ : syracuseStep 8156051 = 12234077) B12234077
theorem B2749373 : Blo 714321 2749373 := bstep (se 3 (by rfl) ⟨515507, by rfl⟩ : syracuseStep 2749373 = 1031015) B1031015
theorem B2716649 : Blo 714321 2716649 := bstep (se 2 (by rfl) ⟨1018743, by rfl⟩ : syracuseStep 2716649 = 2037487) B2037487
theorem B717935 : Blo 714321 717935 := bstep (se 1 (by rfl) ⟨538451, by rfl⟩ : syracuseStep 717935 = 1076903) B1076903
theorem B3437759 : Blo 714321 3437759 := bstep (se 1 (by rfl) ⟨2578319, by rfl⟩ : syracuseStep 3437759 = 5156639) B5156639
theorem B5175323 : Blo 714321 5175323 := bstep (se 1 (by rfl) ⟨3881492, by rfl⟩ : syracuseStep 5175323 = 7762985) B7762985
theorem B2717819 : Blo 714321 2717819 := bstep (se 1 (by rfl) ⟨2038364, by rfl⟩ : syracuseStep 2717819 = 4076729) B4076729
theorem B78608981 : Blo 714321 78608981 := bstep (se 8 (by rfl) ⟨460599, by rfl⟩ : syracuseStep 78608981 = 921199) B921199
theorem B2423411 : Blo 714321 2423411 := bstep (se 1 (by rfl) ⟨1817558, by rfl⟩ : syracuseStep 2423411 = 3635117) B3635117
theorem B1145639 : Blo 714321 1145639 := bstep (se 1 (by rfl) ⟨859229, by rfl⟩ : syracuseStep 1145639 = 1718459) B1718459
theorem B3636251 : Blo 714321 3636251 := bstep (se 1 (by rfl) ⟨2727188, by rfl⟩ : syracuseStep 3636251 = 5454377) B5454377
theorem B13074281 : Blo 714321 13074281 := bstep (se 2 (by rfl) ⟨4902855, by rfl⟩ : syracuseStep 13074281 = 9805711) B9805711
theorem B52887811 : Blo 714321 52887811 := bstep (se 1 (by rfl) ⟨39665858, by rfl⟩ : syracuseStep 52887811 = 79331717) B79331717
theorem B3146051 : Blo 714321 3146051 := bstep (se 1 (by rfl) ⟨2359538, by rfl⟩ : syracuseStep 3146051 = 4719077) B4719077
theorem B27886355 : Blo 714321 27886355 := bstep (se 1 (by rfl) ⟨20914766, by rfl⟩ : syracuseStep 27886355 = 41829533) B41829533
theorem B8160425 : Blo 714321 8160425 := bstep (se 2 (by rfl) ⟨3060159, by rfl⟩ : syracuseStep 8160425 = 6120319) B6120319
theorem B3442297 : Blo 714321 3442297 := bstep (se 2 (by rfl) ⟨1290861, by rfl⟩ : syracuseStep 3442297 = 2581723) B2581723
theorem B46401443 : Blo 714321 46401443 := bstep (se 1 (by rfl) ⟨34801082, by rfl⟩ : syracuseStep 46401443 = 69602165) B69602165
theorem B12584969 : Blo 714321 12584969 := bstep (se 2 (by rfl) ⟨4719363, by rfl⟩ : syracuseStep 12584969 = 9438727) B9438727
theorem B1608191 : Blo 714321 1608191 := bstep (se 1 (by rfl) ⟨1206143, by rfl⟩ : syracuseStep 1608191 = 2412287) B2412287
theorem B3443219 : Blo 714321 3443219 := bstep (se 1 (by rfl) ⟨2582414, by rfl⟩ : syracuseStep 3443219 = 5164829) B5164829
theorem B2755193 : Blo 714321 2755193 := bstep (se 2 (by rfl) ⟨1033197, by rfl⟩ : syracuseStep 2755193 = 2066395) B2066395
theorem B3822750611 : Blo 714321 3822750611 := bstep (se 1 (by rfl) ⟨2867062958, by rfl⟩ : syracuseStep 3822750611 = 5734125917) B5734125917
theorem B1608659 : Blo 714321 1608659 := bstep (se 1 (by rfl) ⟨1206494, by rfl⟩ : syracuseStep 1608659 = 2412989) B2412989
theorem B3673055 : Blo 714321 3673055 := bstep (se 1 (by rfl) ⟨2754791, by rfl⟩ : syracuseStep 3673055 = 5509583) B5509583
theorem B1611647 : Blo 714321 1611647 := bstep (se 1 (by rfl) ⟨1208735, by rfl⟩ : syracuseStep 1611647 = 2417471) B2417471
theorem B6625273 : Blo 714321 6625273 := bstep (se 2 (by rfl) ⟨2484477, by rfl⟩ : syracuseStep 6625273 = 4968955) B4968955
theorem B3872933 : Blo 714321 3872933 := bstep (se 4 (by rfl) ⟨363087, by rfl⟩ : syracuseStep 3872933 = 726175) B726175
theorem B6199667 : Blo 714321 6199667 := bstep (se 1 (by rfl) ⟨4649750, by rfl⟩ : syracuseStep 6199667 = 9299501) B9299501
theorem B1612583 : Blo 714321 1612583 := bstep (se 1 (by rfl) ⟨1209437, by rfl⟩ : syracuseStep 1612583 = 2418875) B2418875
theorem B6626377 : Blo 714321 6626377 := bstep (se 2 (by rfl) ⟨2484891, by rfl⟩ : syracuseStep 6626377 = 4969783) B4969783
theorem B1613051 : Blo 714321 1613051 := bstep (se 1 (by rfl) ⟨1209788, by rfl⟩ : syracuseStep 1613051 = 2419577) B2419577
theorem B1547599 : Blo 714321 1547599 := bstep (se 1 (by rfl) ⟨1160699, by rfl⟩ : syracuseStep 1547599 = 2321399) B2321399
theorem B2039195 : Blo 714321 2039195 := bstep (se 1 (by rfl) ⟨1529396, by rfl⟩ : syracuseStep 2039195 = 3058793) B3058793
theorem B1809823 : Blo 714321 1809823 := bstep (se 1 (by rfl) ⟨1357367, by rfl⟩ : syracuseStep 1809823 = 2714735) B2714735
theorem B1842707 : Blo 714321 1842707 := bstep (se 1 (by rfl) ⟨1382030, by rfl⟩ : syracuseStep 1842707 = 2764061) B2764061
theorem B15507287 : Blo 714321 15507287 := bstep (se 1 (by rfl) ⟨11630465, by rfl⟩ : syracuseStep 15507287 = 23260931) B23260931
theorem B1811099 : Blo 714321 1811099 := bstep (se 1 (by rfl) ⟨1358324, by rfl⟩ : syracuseStep 1811099 = 2716649) B2716649
theorem B861439 : Blo 714321 861439 := bstep (se 1 (by rfl) ⟨646079, by rfl⟩ : syracuseStep 861439 = 1292159) B1292159
theorem B3450215 : Blo 714321 3450215 := bstep (se 1 (by rfl) ⟨2587661, by rfl⟩ : syracuseStep 3450215 = 5175323) B5175323
theorem B1811879 : Blo 714321 1811879 := bstep (se 1 (by rfl) ⟨1358909, by rfl⟩ : syracuseStep 1811879 = 2717819) B2717819
theorem B52405987 : Blo 714321 52405987 := bstep (se 1 (by rfl) ⟨39304490, by rfl⟩ : syracuseStep 52405987 = 78608981) B78608981
theorem B1615607 : Blo 714321 1615607 := bstep (se 1 (by rfl) ⟨1211705, by rfl⟩ : syracuseStep 1615607 = 2423411) B2423411
theorem B1812233 : Blo 714321 1812233 := bstep (se 2 (by rfl) ⟨679587, by rfl⟩ : syracuseStep 1812233 = 1359175) B1359175
theorem B763759 : Blo 714321 763759 := bstep (se 1 (by rfl) ⟨572819, by rfl⟩ : syracuseStep 763759 = 1145639) B1145639
theorem B3451679 : Blo 714321 3451679 := bstep (se 1 (by rfl) ⟨2588759, by rfl⟩ : syracuseStep 3451679 = 5177519) B5177519
theorem B6532001 : Blo 714321 6532001 := bstep (se 2 (by rfl) ⟨2449500, by rfl⟩ : syracuseStep 6532001 = 4899001) B4899001
theorem B1814035 : Blo 714321 1814035 := bstep (se 1 (by rfl) ⟨1360526, by rfl⟩ : syracuseStep 1814035 = 2721053) B2721053
theorem B26455747 : Blo 714321 26455747 := bstep (se 1 (by rfl) ⟨19841810, by rfl⟩ : syracuseStep 26455747 = 39683621) B39683621
theorem B9155875 : Blo 714321 9155875 := bstep (se 1 (by rfl) ⟨6866906, by rfl⟩ : syracuseStep 9155875 = 13733813) B13733813
theorem B1358363 : Blo 714321 1358363 := bstep (se 1 (by rfl) ⟨1018772, by rfl⟩ : syracuseStep 1358363 = 2037545) B2037545
theorem B1358689 : Blo 714321 1358689 := bstep (se 2 (by rfl) ⟨509508, by rfl⟩ : syracuseStep 1358689 = 1019017) B1019017
theorem B20659769 : Blo 714321 20659769 := bstep (se 2 (by rfl) ⟨7747413, by rfl⟩ : syracuseStep 20659769 = 15494827) B15494827
theorem B3620699 : Blo 714321 3620699 := bstep (se 1 (by rfl) ⟨2715524, by rfl⟩ : syracuseStep 3620699 = 5431049) B5431049
theorem B4080395 : Blo 714321 4080395 := bstep (se 1 (by rfl) ⟨3060296, by rfl⟩ : syracuseStep 4080395 = 6120593) B6120593
theorem B23905843 : Blo 714321 23905843 := bstep (se 1 (by rfl) ⟨17929382, by rfl⟩ : syracuseStep 23905843 = 35858765) B35858765
theorem B14173865 : Blo 714321 14173865 := bstep (se 2 (by rfl) ⟨5315199, by rfl⟩ : syracuseStep 14173865 = 10630399) B10630399
theorem B3066311 : Blo 714321 3066311 := bstep (se 1 (by rfl) ⟨2299733, by rfl⟩ : syracuseStep 3066311 = 4599467) B4599467
theorem B1362683 : Blo 714321 1362683 := bstep (se 1 (by rfl) ⟨1022012, by rfl⟩ : syracuseStep 1362683 = 2044025) B2044025
theorem B904223 : Blo 714321 904223 := bstep (se 1 (by rfl) ⟨678167, by rfl⟩ : syracuseStep 904223 = 1356335) B1356335
theorem B805999 : Blo 714321 805999 := bstep (se 1 (by rfl) ⟨604499, by rfl⟩ : syracuseStep 805999 = 1208999) B1208999
theorem B5821787 : Blo 714321 5821787 := bstep (se 1 (by rfl) ⟨4366340, by rfl⟩ : syracuseStep 5821787 = 8732681) B8732681
theorem B1529363 : Blo 714321 1529363 := bstep (se 1 (by rfl) ⟨1147022, by rfl⟩ : syracuseStep 1529363 = 2294045) B2294045
theorem B60413825 : Blo 714321 60413825 := bstep (se 2 (by rfl) ⟨22655184, by rfl⟩ : syracuseStep 60413825 = 45310369) B45310369
theorem B29775923 : Blo 714321 29775923 := bstep (se 1 (by rfl) ⟨22331942, by rfl⟩ : syracuseStep 29775923 = 44663885) B44663885
theorem B2414987 : Blo 714321 2414987 := bstep (se 1 (by rfl) ⟨1811240, by rfl⟩ : syracuseStep 2414987 = 3622481) B3622481
theorem B1071599 : Blo 714321 1071599 := bstep (se 1 (by rfl) ⟨803699, by rfl⟩ : syracuseStep 1071599 = 1607399) B1607399
theorem B1071881 : Blo 714321 1071881 := bstep (se 2 (by rfl) ⟨401955, by rfl⟩ : syracuseStep 1071881 = 803911) B803911
theorem B2907343 : Blo 714321 2907343 := bstep (se 1 (by rfl) ⟨2180507, by rfl⟩ : syracuseStep 2907343 = 4361015) B4361015
theorem B1072607 : Blo 714321 1072607 := bstep (se 1 (by rfl) ⟨804455, by rfl⟩ : syracuseStep 1072607 = 1608911) B1608911
theorem B2416175 : Blo 714321 2416175 := bstep (se 1 (by rfl) ⟨1812131, by rfl⟩ : syracuseStep 2416175 = 3624263) B3624263
theorem B2908007 : Blo 714321 2908007 := bstep (se 1 (by rfl) ⟨2181005, by rfl⟩ : syracuseStep 2908007 = 4362011) B4362011
theorem B1073183 : Blo 714321 1073183 := bstep (se 1 (by rfl) ⟨804887, by rfl⟩ : syracuseStep 1073183 = 1609775) B1609775
theorem B12247199 : Blo 714321 12247199 := bstep (se 1 (by rfl) ⟨9185399, by rfl⟩ : syracuseStep 12247199 = 18370799) B18370799
theorem B39641561 : Blo 714321 39641561 := bstep (se 2 (by rfl) ⟨14865585, by rfl⟩ : syracuseStep 39641561 = 29731171) B29731171
theorem B9167357 : Blo 714321 9167357 := bstep (se 3 (by rfl) ⟨1718879, by rfl⟩ : syracuseStep 9167357 = 3437759) B3437759
theorem B5792633 : Blo 714321 5792633 := bstep (se 2 (by rfl) ⟨2172237, by rfl⟩ : syracuseStep 5792633 = 4344475) B4344475
theorem B1205759 : Blo 714321 1205759 := bstep (se 1 (by rfl) ⟨904319, by rfl⟩ : syracuseStep 1205759 = 1808639) B1808639
theorem B1074779 : Blo 714321 1074779 := bstep (se 1 (by rfl) ⟨806084, by rfl⟩ : syracuseStep 1074779 = 1612169) B1612169
theorem B46491245 : Blo 714321 46491245 := bstep (se 3 (by rfl) ⟨8717108, by rfl⟩ : syracuseStep 46491245 = 17434217) B17434217
theorem B1533583 : Blo 714321 1533583 := bstep (se 1 (by rfl) ⟨1150187, by rfl⟩ : syracuseStep 1533583 = 2300375) B2300375
theorem B2713247 : Blo 714321 2713247 := bstep (se 1 (by rfl) ⟨2034935, by rfl⟩ : syracuseStep 2713247 = 4069871) B4069871
theorem B714747 : Blo 714321 714747 := bstep (se 1 (by rfl) ⟨536060, by rfl⟩ : syracuseStep 714747 = 1072121) B1072121
theorem B715079 : Blo 714321 715079 := bstep (se 1 (by rfl) ⟨536309, by rfl⟩ : syracuseStep 715079 = 1072619) B1072619
theorem B1075559 : Blo 714321 1075559 := bstep (se 1 (by rfl) ⟨806669, by rfl⟩ : syracuseStep 1075559 = 1613339) B1613339
theorem B1206839 : Blo 714321 1206839 := bstep (se 1 (by rfl) ⟨905129, by rfl⟩ : syracuseStep 1206839 = 1810259) B1810259
theorem B715355 : Blo 714321 715355 := bstep (se 1 (by rfl) ⟨536516, by rfl⟩ : syracuseStep 715355 = 1073033) B1073033
theorem B715471 : Blo 714321 715471 := bstep (se 1 (by rfl) ⟨536603, by rfl⟩ : syracuseStep 715471 = 1073207) B1073207
theorem B1075931 : Blo 714321 1075931 := bstep (se 1 (by rfl) ⟨806948, by rfl⟩ : syracuseStep 1075931 = 1613897) B1613897
theorem B715519 : Blo 714321 715519 := bstep (se 1 (by rfl) ⟨536639, by rfl⟩ : syracuseStep 715519 = 1073279) B1073279
theorem B1076105 : Blo 714321 1076105 := bstep (se 2 (by rfl) ⟨403539, by rfl⟩ : syracuseStep 1076105 = 807079) B807079
theorem B715711 : Blo 714321 715711 := bstep (se 1 (by rfl) ⟨536783, by rfl⟩ : syracuseStep 715711 = 1073567) B1073567
theorem B1076159 : Blo 714321 1076159 := bstep (se 1 (by rfl) ⟨807119, by rfl⟩ : syracuseStep 1076159 = 1614239) B1614239
theorem B5434451 : Blo 714321 5434451 := bstep (se 1 (by rfl) ⟨4075838, by rfl⟩ : syracuseStep 5434451 = 8151677) B8151677
theorem B716015 : Blo 714321 716015 := bstep (se 1 (by rfl) ⟨537011, by rfl⟩ : syracuseStep 716015 = 1074023) B1074023
theorem B11627869 : Blo 714321 11627869 := bstep (se 3 (by rfl) ⟨2180225, by rfl⟩ : syracuseStep 11627869 = 4360451) B4360451
theorem B716239 : Blo 714321 716239 := bstep (se 1 (by rfl) ⟨537179, by rfl⟩ : syracuseStep 716239 = 1074359) B1074359
theorem B1076735 : Blo 714321 1076735 := bstep (se 1 (by rfl) ⟨807551, by rfl⟩ : syracuseStep 1076735 = 1615103) B1615103
theorem B3632687 : Blo 714321 3632687 := bstep (se 1 (by rfl) ⟨2724515, by rfl⟩ : syracuseStep 3632687 = 5449031) B5449031
theorem B716635 : Blo 714321 716635 := bstep (se 1 (by rfl) ⟨537476, by rfl⟩ : syracuseStep 716635 = 1074953) B1074953
theorem B716847 : Blo 714321 716847 := bstep (se 1 (by rfl) ⟨537635, by rfl⟩ : syracuseStep 716847 = 1075271) B1075271
theorem B716967 : Blo 714321 716967 := bstep (se 1 (by rfl) ⟨537725, by rfl⟩ : syracuseStep 716967 = 1075451) B1075451
theorem B717103 : Blo 714321 717103 := bstep (se 1 (by rfl) ⟨537827, by rfl⟩ : syracuseStep 717103 = 1075655) B1075655
theorem B717311 : Blo 714321 717311 := bstep (se 1 (by rfl) ⟨537983, by rfl⟩ : syracuseStep 717311 = 1075967) B1075967
theorem B717423 : Blo 714321 717423 := bstep (se 1 (by rfl) ⟨538067, by rfl⟩ : syracuseStep 717423 = 1076135) B1076135
theorem B717467 : Blo 714321 717467 := bstep (se 1 (by rfl) ⟨538100, by rfl⟩ : syracuseStep 717467 = 1076201) B1076201
theorem B717471 : Blo 714321 717471 := bstep (se 1 (by rfl) ⟨538103, by rfl⟩ : syracuseStep 717471 = 1076207) B1076207
theorem B717503 : Blo 714321 717503 := bstep (se 1 (by rfl) ⟨538127, by rfl⟩ : syracuseStep 717503 = 1076255) B1076255
theorem B717543 : Blo 714321 717543 := bstep (se 1 (by rfl) ⟨538157, by rfl⟩ : syracuseStep 717543 = 1076315) B1076315
theorem B717759 : Blo 714321 717759 := bstep (se 1 (by rfl) ⟨538319, by rfl⟩ : syracuseStep 717759 = 1076639) B1076639
theorem B717851 : Blo 714321 717851 := bstep (se 1 (by rfl) ⟨538388, by rfl⟩ : syracuseStep 717851 = 1076777) B1076777
theorem B718015 : Blo 714321 718015 := bstep (se 1 (by rfl) ⟨538511, by rfl⟩ : syracuseStep 718015 = 1077023) B1077023
theorem B2290943 : Blo 714321 2290943 := bstep (se 1 (by rfl) ⟨1718207, by rfl⟩ : syracuseStep 2290943 = 3436415) B3436415
theorem B718127 : Blo 714321 718127 := bstep (se 1 (by rfl) ⟨538595, by rfl⟩ : syracuseStep 718127 = 1077191) B1077191
theorem B5437367 : Blo 714321 5437367 := bstep (se 1 (by rfl) ⟨4078025, by rfl⟩ : syracuseStep 5437367 = 8156051) B8156051
theorem B1832915 : Blo 714321 1832915 := bstep (se 1 (by rfl) ⟨1374686, by rfl⟩ : syracuseStep 1832915 = 2749373) B2749373
theorem B2717833 : Blo 714321 2717833 := bstep (se 2 (by rfl) ⟨1019187, by rfl⟩ : syracuseStep 2717833 = 2038375) B2038375
theorem B55769593 : Blo 714321 55769593 := bstep (se 2 (by rfl) ⟨20913597, by rfl⟩ : syracuseStep 55769593 = 41827195) B41827195
theorem B3635927 : Blo 714321 3635927 := bstep (se 1 (by rfl) ⟨2726945, by rfl⟩ : syracuseStep 3635927 = 5453891) B5453891
theorem B3636089 : Blo 714321 3636089 := bstep (se 2 (by rfl) ⟨1363533, by rfl⟩ : syracuseStep 3636089 = 2727067) B2727067
theorem B3439529 : Blo 714321 3439529 := bstep (se 2 (by rfl) ⟨1289823, by rfl⟩ : syracuseStep 3439529 = 2579647) B2579647
theorem B2424167 : Blo 714321 2424167 := bstep (se 1 (by rfl) ⟨1818125, by rfl⟩ : syracuseStep 2424167 = 3636251) B3636251
theorem B1211807 : Blo 714321 1211807 := bstep (se 1 (by rfl) ⟨908855, by rfl⟩ : syracuseStep 1211807 = 1817711) B1817711
theorem B1211881 : Blo 714321 1211881 := bstep (se 2 (by rfl) ⟨454455, by rfl⟩ : syracuseStep 1211881 = 908911) B908911
theorem B8716187 : Blo 714321 8716187 := bstep (se 1 (by rfl) ⟨6537140, by rfl⟩ : syracuseStep 8716187 = 13074281) B13074281
theorem B70517081 : Blo 714321 70517081 := bstep (se 2 (by rfl) ⟨26443905, by rfl⟩ : syracuseStep 70517081 = 52887811) B52887811
theorem B2720263 : Blo 714321 2720263 := bstep (se 1 (by rfl) ⟨2040197, by rfl⟩ : syracuseStep 2720263 = 4080395) B4080395
theorem B5440283 : Blo 714321 5440283 := bstep (se 1 (by rfl) ⟨4080212, by rfl⟩ : syracuseStep 5440283 = 8160425) B8160425
theorem B8389469 : Blo 714321 8389469 := bstep (se 3 (by rfl) ⟨1573025, by rfl⟩ : syracuseStep 8389469 = 3146051) B3146051
theorem B30934295 : Blo 714321 30934295 := bstep (se 1 (by rfl) ⟨23200721, by rfl⟩ : syracuseStep 30934295 = 46401443) B46401443
theorem B8389979 : Blo 714321 8389979 := bstep (se 1 (by rfl) ⟨6292484, by rfl⟩ : syracuseStep 8389979 = 12584969) B12584969
theorem B1148585 : Blo 714321 1148585 := bstep (se 2 (by rfl) ⟨430719, by rfl⟩ : syracuseStep 1148585 = 861439) B861439
theorem B2295479 : Blo 714321 2295479 := bstep (se 1 (by rfl) ⟨1721609, by rfl⟩ : syracuseStep 2295479 = 3443219) B3443219
theorem B2548500407 : Blo 714321 2548500407 := bstep (se 1 (by rfl) ⟨1911375305, by rfl⟩ : syracuseStep 2548500407 = 3822750611) B3822750611
theorem B4589729 : Blo 714321 4589729 := bstep (se 2 (by rfl) ⟨1721148, by rfl⟩ : syracuseStep 4589729 = 3442297) B3442297
theorem B1018345 : Blo 714321 1018345 := bstep (se 2 (by rfl) ⟨381879, by rfl⟩ : syracuseStep 1018345 = 763759) B763759
theorem B1019575 : Blo 714321 1019575 := bstep (se 1 (by rfl) ⟨764681, by rfl⟩ : syracuseStep 1019575 = 1529363) B1529363
theorem B40275883 : Blo 714321 40275883 := bstep (se 1 (by rfl) ⟨30206912, by rfl⟩ : syracuseStep 40275883 = 60413825) B60413825
theorem B4133111 : Blo 714321 4133111 := bstep (se 1 (by rfl) ⟨3099833, by rfl⟩ : syracuseStep 4133111 = 6199667) B6199667
theorem B1609991 : Blo 714321 1609991 := bstep (se 1 (by rfl) ⟨1207493, by rfl⟩ : syracuseStep 1609991 = 2414987) B2414987
theorem B15503825 : Blo 714321 15503825 := bstep (se 2 (by rfl) ⟨5813934, by rfl⟩ : syracuseStep 15503825 = 11627869) B11627869
theorem B1610783 : Blo 714321 1610783 := bstep (se 1 (by rfl) ⟨1208087, by rfl⟩ : syracuseStep 1610783 = 2416175) B2416175
theorem B4887773 : Blo 714321 4887773 := bstep (se 3 (by rfl) ⟨916457, by rfl⟩ : syracuseStep 4887773 = 1832915) B1832915
theorem B1938671 : Blo 714321 1938671 := bstep (se 1 (by rfl) ⟨1454003, by rfl⟩ : syracuseStep 1938671 = 2908007) B2908007
theorem B8164799 : Blo 714321 8164799 := bstep (se 1 (by rfl) ⟨6123599, by rfl⟩ : syracuseStep 8164799 = 12247199) B12247199
theorem B15505829 : Blo 714321 15505829 := bstep (se 4 (by rfl) ⟨1453671, by rfl⟩ : syracuseStep 15505829 = 2907343) B2907343
theorem B1808831 : Blo 714321 1808831 := bstep (se 1 (by rfl) ⟨1356623, by rfl⟩ : syracuseStep 1808831 = 2713247) B2713247
theorem B7347181 : Blo 714321 7347181 := bstep (se 3 (by rfl) ⟨1377596, by rfl⟩ : syracuseStep 7347181 = 2755193) B2755193
theorem B2301119 : Blo 714321 2301119 := bstep (se 1 (by rfl) ⟨1725839, by rfl⟩ : syracuseStep 2301119 = 3451679) B3451679
theorem B74359457 : Blo 714321 74359457 := bstep (se 2 (by rfl) ⟨27884796, by rfl⟩ : syracuseStep 74359457 = 55769593) B55769593
theorem B1811585 : Blo 714321 1811585 := bstep (se 2 (by rfl) ⟨679344, by rfl⟩ : syracuseStep 1811585 = 1358689) B1358689
theorem B1615841 : Blo 714321 1615841 := bstep (se 2 (by rfl) ⟨605940, by rfl⟩ : syracuseStep 1615841 = 1211881) B1211881
theorem B1616111 : Blo 714321 1616111 := bstep (se 1 (by rfl) ⟨1212083, by rfl⟩ : syracuseStep 1616111 = 2424167) B2424167
theorem B13773179 : Blo 714321 13773179 := bstep (se 1 (by rfl) ⟨10329884, by rfl⟩ : syracuseStep 13773179 = 20659769) B20659769
theorem B5810791 : Blo 714321 5810791 := bstep (se 1 (by rfl) ⟨4358093, by rfl⟩ : syracuseStep 5810791 = 8716187) B8716187
theorem B18590903 : Blo 714321 18590903 := bstep (se 1 (by rfl) ⟨13943177, by rfl⟩ : syracuseStep 18590903 = 27886355) B27886355
theorem B9449243 : Blo 714321 9449243 := bstep (se 1 (by rfl) ⟨7086932, by rfl⟩ : syracuseStep 9449243 = 14173865) B14173865
theorem B2044207 : Blo 714321 2044207 := bstep (se 1 (by rfl) ⟨1533155, by rfl⟩ : syracuseStep 2044207 = 3066311) B3066311
theorem B2044777 : Blo 714321 2044777 := bstep (se 2 (by rfl) ⟨766791, by rfl⟩ : syracuseStep 2044777 = 1533583) B1533583
theorem B69874649 : Blo 714321 69874649 := bstep (se 2 (by rfl) ⟨26202993, by rfl⟩ : syracuseStep 69874649 = 52405987) B52405987
theorem B6109181 : Blo 714321 6109181 := bstep (se 3 (by rfl) ⟨1145471, by rfl⟩ : syracuseStep 6109181 = 2290943) B2290943
theorem B3881191 : Blo 714321 3881191 := bstep (se 1 (by rfl) ⟨2910893, by rfl⟩ : syracuseStep 3881191 = 5821787) B5821787
theorem B35274329 : Blo 714321 35274329 := bstep (se 2 (by rfl) ⟨13227873, by rfl⟩ : syracuseStep 35274329 = 26455747) B26455747
theorem B10338191 : Blo 714321 10338191 := bstep (se 1 (by rfl) ⟨7753643, by rfl⟩ : syracuseStep 10338191 = 15507287) B15507287
theorem B26427707 : Blo 714321 26427707 := bstep (se 1 (by rfl) ⟨19820780, by rfl⟩ : syracuseStep 26427707 = 39641561) B39641561
theorem B6111571 : Blo 714321 6111571 := bstep (se 1 (by rfl) ⟨4583678, by rfl⟩ : syracuseStep 6111571 = 9167357) B9167357
theorem B803839 : Blo 714321 803839 := bstep (se 1 (by rfl) ⟨602879, by rfl⟩ : syracuseStep 803839 = 1205759) B1205759
theorem B804559 : Blo 714321 804559 := bstep (se 1 (by rfl) ⟨603419, by rfl⟩ : syracuseStep 804559 = 1206839) B1206839
theorem B12207833 : Blo 714321 12207833 := bstep (se 2 (by rfl) ⟨4577937, by rfl⟩ : syracuseStep 12207833 = 9155875) B9155875
theorem B3622967 : Blo 714321 3622967 := bstep (se 1 (by rfl) ⟨2717225, by rfl⟩ : syracuseStep 3622967 = 5434451) B5434451
theorem B8833697 : Blo 714321 8833697 := bstep (se 2 (by rfl) ⟨3312636, by rfl⟩ : syracuseStep 8833697 = 6625273) B6625273
theorem B2411261 : Blo 714321 2411261 := bstep (se 3 (by rfl) ⟨452111, by rfl⟩ : syracuseStep 2411261 = 904223) B904223
theorem B3623777 : Blo 714321 3623777 := bstep (se 2 (by rfl) ⟨1358916, by rfl⟩ : syracuseStep 3623777 = 2717833) B2717833
theorem B3624911 : Blo 714321 3624911 := bstep (se 1 (by rfl) ⟨2718683, by rfl⟩ : syracuseStep 3624911 = 5437367) B5437367
theorem B8835169 : Blo 714321 8835169 := bstep (se 2 (by rfl) ⟨3313188, by rfl⟩ : syracuseStep 8835169 = 6626377) B6626377
theorem B905575 : Blo 714321 905575 := bstep (se 1 (by rfl) ⟨679181, by rfl⟩ : syracuseStep 905575 = 1358363) B1358363
theorem B2413097 : Blo 714321 2413097 := bstep (se 2 (by rfl) ⟨904911, by rfl⟩ : syracuseStep 2413097 = 1809823) B1809823
theorem B807871 : Blo 714321 807871 := bstep (se 1 (by rfl) ⟨605903, by rfl⟩ : syracuseStep 807871 = 1211807) B1211807
theorem B2413799 : Blo 714321 2413799 := bstep (se 1 (by rfl) ⟨1810349, by rfl⟩ : syracuseStep 2413799 = 3620699) B3620699
theorem B1072127 : Blo 714321 1072127 := bstep (se 1 (by rfl) ⟨804095, by rfl⟩ : syracuseStep 1072127 = 1608191) B1608191
theorem B1072439 : Blo 714321 1072439 := bstep (se 1 (by rfl) ⟨804329, by rfl⟩ : syracuseStep 1072439 = 1608659) B1608659
theorem B2448703 : Blo 714321 2448703 := bstep (se 1 (by rfl) ⟨1836527, by rfl⟩ : syracuseStep 2448703 = 3673055) B3673055
theorem B9200573 : Blo 714321 9200573 := bstep (se 3 (by rfl) ⟨1725107, by rfl⟩ : syracuseStep 9200573 = 3450215) B3450215
theorem B1074431 : Blo 714321 1074431 := bstep (se 1 (by rfl) ⟨805823, by rfl⟩ : syracuseStep 1074431 = 1611647) B1611647
theorem B19850615 : Blo 714321 19850615 := bstep (se 1 (by rfl) ⟨14887961, by rfl⟩ : syracuseStep 19850615 = 29775923) B29775923
theorem B2581955 : Blo 714321 2581955 := bstep (se 1 (by rfl) ⟨1936466, by rfl⟩ : syracuseStep 2581955 = 3872933) B3872933
theorem B1074665 : Blo 714321 1074665 := bstep (se 2 (by rfl) ⟨402999, by rfl⟩ : syracuseStep 1074665 = 805999) B805999
theorem B714399 : Blo 714321 714399 := bstep (se 1 (by rfl) ⟨535799, by rfl⟩ : syracuseStep 714399 = 1071599) B1071599
theorem B714587 : Blo 714321 714587 := bstep (se 1 (by rfl) ⟨535940, by rfl⟩ : syracuseStep 714587 = 1071881) B1071881
theorem B1075055 : Blo 714321 1075055 := bstep (se 1 (by rfl) ⟨806291, by rfl⟩ : syracuseStep 1075055 = 1612583) B1612583
theorem B2418713 : Blo 714321 2418713 := bstep (se 2 (by rfl) ⟨907017, by rfl⟩ : syracuseStep 2418713 = 1814035) B1814035
theorem B1075367 : Blo 714321 1075367 := bstep (se 1 (by rfl) ⟨806525, by rfl⟩ : syracuseStep 1075367 = 1613051) B1613051
theorem B715071 : Blo 714321 715071 := bstep (se 1 (by rfl) ⟨536303, by rfl⟩ : syracuseStep 715071 = 1072607) B1072607
theorem B715455 : Blo 714321 715455 := bstep (se 1 (by rfl) ⟨536591, by rfl⟩ : syracuseStep 715455 = 1073183) B1073183
theorem B1207399 : Blo 714321 1207399 := bstep (se 1 (by rfl) ⟨905549, by rfl⟩ : syracuseStep 1207399 = 1811099) B1811099
theorem B3861755 : Blo 714321 3861755 := bstep (se 1 (by rfl) ⟨2896316, by rfl⟩ : syracuseStep 3861755 = 5792633) B5792633
theorem B1207919 : Blo 714321 1207919 := bstep (se 1 (by rfl) ⟨905939, by rfl⟩ : syracuseStep 1207919 = 1811879) B1811879
theorem B716519 : Blo 714321 716519 := bstep (se 1 (by rfl) ⟨537389, by rfl⟩ : syracuseStep 716519 = 1074779) B1074779
theorem B30994163 : Blo 714321 30994163 := bstep (se 1 (by rfl) ⟨23245622, by rfl⟩ : syracuseStep 30994163 = 46491245) B46491245
theorem B1077071 : Blo 714321 1077071 := bstep (se 1 (by rfl) ⟨807803, by rfl⟩ : syracuseStep 1077071 = 1615607) B1615607
theorem B1208155 : Blo 714321 1208155 := bstep (se 1 (by rfl) ⟨906116, by rfl⟩ : syracuseStep 1208155 = 1812233) B1812233
theorem B717039 : Blo 714321 717039 := bstep (se 1 (by rfl) ⟨537779, by rfl⟩ : syracuseStep 717039 = 1075559) B1075559
theorem B717287 : Blo 714321 717287 := bstep (se 1 (by rfl) ⟨537965, by rfl⟩ : syracuseStep 717287 = 1075931) B1075931
theorem B717403 : Blo 714321 717403 := bstep (se 1 (by rfl) ⟨538052, by rfl⟩ : syracuseStep 717403 = 1076105) B1076105
theorem B4354667 : Blo 714321 4354667 := bstep (se 1 (by rfl) ⟨3266000, by rfl⟩ : syracuseStep 4354667 = 6532001) B6532001
theorem B717439 : Blo 714321 717439 := bstep (se 1 (by rfl) ⟨538079, by rfl⟩ : syracuseStep 717439 = 1076159) B1076159
theorem B3633821 : Blo 714321 3633821 := bstep (se 3 (by rfl) ⟨681341, by rfl⟩ : syracuseStep 3633821 = 1362683) B1362683
theorem B717823 : Blo 714321 717823 := bstep (se 1 (by rfl) ⟨538367, by rfl⟩ : syracuseStep 717823 = 1076735) B1076735
theorem B2421791 : Blo 714321 2421791 := bstep (se 1 (by rfl) ⟨1816343, by rfl⟩ : syracuseStep 2421791 = 3632687) B3632687
theorem B127497829 : Blo 714321 127497829 := bstep (se 4 (by rfl) ⟨11952921, by rfl⟩ : syracuseStep 127497829 = 23905843) B23905843
theorem B5437853 : Blo 714321 5437853 := bstep (se 3 (by rfl) ⟨1019597, by rfl⟩ : syracuseStep 5437853 = 2039195) B2039195
theorem B4913885 : Blo 714321 4913885 := bstep (se 3 (by rfl) ⟨921353, by rfl⟩ : syracuseStep 4913885 = 1842707) B1842707
theorem B2063465 : Blo 714321 2063465 := bstep (se 2 (by rfl) ⟨773799, by rfl⟩ : syracuseStep 2063465 = 1547599) B1547599
theorem B2423951 : Blo 714321 2423951 := bstep (se 1 (by rfl) ⟨1817963, by rfl⟩ : syracuseStep 2423951 = 3635927) B3635927
theorem B2424059 : Blo 714321 2424059 := bstep (se 1 (by rfl) ⟨1818044, by rfl⟩ : syracuseStep 2424059 = 3636089) B3636089
theorem B2293019 : Blo 714321 2293019 := bstep (se 1 (by rfl) ⟨1719764, by rfl⟩ : syracuseStep 2293019 = 3439529) B3439529
theorem B1607507 : Blo 714321 1607507 := bstep (se 1 (by rfl) ⟨1205630, by rfl⟩ : syracuseStep 1607507 = 2411261) B2411261
theorem B1608731 : Blo 714321 1608731 := bstep (se 1 (by rfl) ⟨1206548, by rfl⟩ : syracuseStep 1608731 = 2413097) B2413097
theorem B1609199 : Blo 714321 1609199 := bstep (se 1 (by rfl) ⟨1206899, by rfl⟩ : syracuseStep 1609199 = 2413799) B2413799
theorem B5443199 : Blo 714321 5443199 := bstep (se 1 (by rfl) ⟨4082399, by rfl⟩ : syracuseStep 5443199 = 8164799) B8164799
theorem B1609865 : Blo 714321 1609865 := bstep (se 2 (by rfl) ⟨603699, by rfl⟩ : syracuseStep 1609865 = 1207399) B1207399
theorem B1610873 : Blo 714321 1610873 := bstep (se 2 (by rfl) ⟨604077, by rfl⟩ : syracuseStep 1610873 = 1208155) B1208155
theorem B2725609 : Blo 714321 2725609 := bstep (se 2 (by rfl) ⟨1022103, by rfl⟩ : syracuseStep 2725609 = 2044207) B2044207
theorem B6133715 : Blo 714321 6133715 := bstep (se 1 (by rfl) ⟨4600286, by rfl⟩ : syracuseStep 6133715 = 9200573) B9200573
theorem B2726369 : Blo 714321 2726369 := bstep (se 2 (by rfl) ⟨1022388, by rfl⟩ : syracuseStep 2726369 = 2044777) B2044777
theorem B1612475 : Blo 714321 1612475 := bstep (se 1 (by rfl) ⟨1209356, by rfl⟩ : syracuseStep 1612475 = 2418713) B2418713
theorem B9182119 : Blo 714321 9182119 := bstep (se 1 (by rfl) ⟨6886589, by rfl⟩ : syracuseStep 9182119 = 13773179) B13773179
theorem B12393935 : Blo 714321 12393935 := bstep (se 1 (by rfl) ⟨9295451, by rfl⟩ : syracuseStep 12393935 = 18590903) B18590903
theorem B6299495 : Blo 714321 6299495 := bstep (se 1 (by rfl) ⟨4724621, by rfl⟩ : syracuseStep 6299495 = 9449243) B9449243
theorem B1614527 : Blo 714321 1614527 := bstep (se 1 (by rfl) ⟨1210895, by rfl⟩ : syracuseStep 1614527 = 2421791) B2421791
theorem B4072787 : Blo 714321 4072787 := bstep (se 1 (by rfl) ⟨3054590, by rfl⟩ : syracuseStep 4072787 = 6109181) B6109181
theorem B1615967 : Blo 714321 1615967 := bstep (se 1 (by rfl) ⟨1211975, by rfl⟩ : syracuseStep 1615967 = 2423951) B2423951
theorem B1616039 : Blo 714321 1616039 := bstep (se 1 (by rfl) ⟨1212029, by rfl⟩ : syracuseStep 1616039 = 2424059) B2424059
theorem B6892127 : Blo 714321 6892127 := bstep (se 1 (by rfl) ⟨5169095, by rfl⟩ : syracuseStep 6892127 = 10338191) B10338191
theorem B20622863 : Blo 714321 20622863 := bstep (se 1 (by rfl) ⟨15467147, by rfl⟩ : syracuseStep 20622863 = 30934295) B30934295
theorem B8138555 : Blo 714321 8138555 := bstep (se 1 (by rfl) ⟨6103916, by rfl⟩ : syracuseStep 8138555 = 12207833) B12207833
theorem B1699000271 : Blo 714321 1699000271 := bstep (se 1 (by rfl) ⟨1274250203, by rfl⟩ : syracuseStep 1699000271 = 2548500407) B2548500407
theorem B3059819 : Blo 714321 3059819 := bstep (se 1 (by rfl) ⟨2294864, by rfl⟩ : syracuseStep 3059819 = 4589729) B4589729
theorem B44086517 : Blo 714321 44086517 := bstep (se 5 (by rfl) ⟨2066555, by rfl⟩ : syracuseStep 44086517 = 4133111) B4133111
theorem B10335883 : Blo 714321 10335883 := bstep (se 1 (by rfl) ⟨7751912, by rfl⟩ : syracuseStep 10335883 = 15503825) B15503825
theorem B1357793 : Blo 714321 1357793 := bstep (se 2 (by rfl) ⟨509172, by rfl⟩ : syracuseStep 1357793 = 1018345) B1018345
theorem B7747721 : Blo 714321 7747721 := bstep (se 2 (by rfl) ⟨2905395, by rfl⟩ : syracuseStep 7747721 = 5810791) B5810791
theorem B3258515 : Blo 714321 3258515 := bstep (se 1 (by rfl) ⟨2443886, by rfl⟩ : syracuseStep 3258515 = 4887773) B4887773
theorem B1292447 : Blo 714321 1292447 := bstep (se 1 (by rfl) ⟨969335, by rfl⟩ : syracuseStep 1292447 = 1938671) B1938671
theorem B10337219 : Blo 714321 10337219 := bstep (se 1 (by rfl) ⟨7752914, by rfl⟩ : syracuseStep 10337219 = 15505829) B15505829
theorem B1359433 : Blo 714321 1359433 := bstep (se 2 (by rfl) ⟨509787, by rfl⟩ : syracuseStep 1359433 = 1019575) B1019575
theorem B11780225 : Blo 714321 11780225 := bstep (se 2 (by rfl) ⟨4417584, by rfl⟩ : syracuseStep 11780225 = 8835169) B8835169
theorem B1721303 : Blo 714321 1721303 := bstep (se 1 (by rfl) ⟨1290977, by rfl⟩ : syracuseStep 1721303 = 2581955) B2581955
theorem B2574503 : Blo 714321 2574503 := bstep (se 1 (by rfl) ⟨1930877, by rfl⟩ : syracuseStep 2574503 = 3861755) B3861755
theorem B805279 : Blo 714321 805279 := bstep (se 1 (by rfl) ⟨603959, by rfl⟩ : syracuseStep 805279 = 1207919) B1207919
theorem B20662775 : Blo 714321 20662775 := bstep (se 1 (by rfl) ⟨15497081, by rfl⟩ : syracuseStep 20662775 = 30994163) B30994163
theorem B2903111 : Blo 714321 2903111 := bstep (se 1 (by rfl) ⟨2177333, by rfl⟩ : syracuseStep 2903111 = 4354667) B4354667
theorem B46583099 : Blo 714321 46583099 := bstep (se 1 (by rfl) ⟨34937324, by rfl⟩ : syracuseStep 46583099 = 69874649) B69874649
theorem B3625235 : Blo 714321 3625235 := bstep (se 1 (by rfl) ⟨2718926, by rfl⟩ : syracuseStep 3625235 = 5437853) B5437853
theorem B3264937 : Blo 714321 3264937 := bstep (se 2 (by rfl) ⟨1224351, by rfl⟩ : syracuseStep 3264937 = 2448703) B2448703
theorem B1528679 : Blo 714321 1528679 := bstep (se 1 (by rfl) ⟨1146509, by rfl⟩ : syracuseStep 1528679 = 2293019) B2293019
theorem B23516219 : Blo 714321 23516219 := bstep (se 1 (by rfl) ⟨17637164, by rfl⟩ : syracuseStep 23516219 = 35274329) B35274329
theorem B17618471 : Blo 714321 17618471 := bstep (se 1 (by rfl) ⟨13213853, by rfl⟩ : syracuseStep 17618471 = 26427707) B26427707
theorem B47011387 : Blo 714321 47011387 := bstep (se 1 (by rfl) ⟨35258540, by rfl⟩ : syracuseStep 47011387 = 70517081) B70517081
theorem B8148761 : Blo 714321 8148761 := bstep (se 2 (by rfl) ⟨3055785, by rfl⟩ : syracuseStep 8148761 = 6111571) B6111571
theorem B3626855 : Blo 714321 3626855 := bstep (se 1 (by rfl) ⟨2720141, by rfl⟩ : syracuseStep 3626855 = 5440283) B5440283
theorem B5592979 : Blo 714321 5592979 := bstep (se 1 (by rfl) ⟨4194734, by rfl⟩ : syracuseStep 5592979 = 8389469) B8389469
theorem B3627017 : Blo 714321 3627017 := bstep (se 2 (by rfl) ⟨1360131, by rfl⟩ : syracuseStep 3627017 = 2720263) B2720263
theorem B5593319 : Blo 714321 5593319 := bstep (se 1 (by rfl) ⟨4194989, by rfl⟩ : syracuseStep 5593319 = 8389979) B8389979
theorem B1071785 : Blo 714321 1071785 := bstep (se 2 (by rfl) ⟨401919, by rfl⟩ : syracuseStep 1071785 = 803839) B803839
theorem B2415311 : Blo 714321 2415311 := bstep (se 1 (by rfl) ⟨1811483, by rfl⟩ : syracuseStep 2415311 = 3622967) B3622967
theorem B5889131 : Blo 714321 5889131 := bstep (se 1 (by rfl) ⟨4416848, by rfl⟩ : syracuseStep 5889131 = 8833697) B8833697
theorem B2415851 : Blo 714321 2415851 := bstep (se 1 (by rfl) ⟨1811888, by rfl⟩ : syracuseStep 2415851 = 3623777) B3623777
theorem B1072745 : Blo 714321 1072745 := bstep (se 2 (by rfl) ⟨402279, by rfl⟩ : syracuseStep 1072745 = 804559) B804559
theorem B2416607 : Blo 714321 2416607 := bstep (se 1 (by rfl) ⟨1812455, by rfl⟩ : syracuseStep 2416607 = 3624911) B3624911
theorem B1073327 : Blo 714321 1073327 := bstep (se 1 (by rfl) ⟨804995, by rfl⟩ : syracuseStep 1073327 = 1609991) B1609991
theorem B1073855 : Blo 714321 1073855 := bstep (se 1 (by rfl) ⟨805391, by rfl⟩ : syracuseStep 1073855 = 1610783) B1610783
theorem B1205887 : Blo 714321 1205887 := bstep (se 1 (by rfl) ⟨904415, by rfl⟩ : syracuseStep 1205887 = 1808831) B1808831
theorem B6121277 : Blo 714321 6121277 := bstep (se 3 (by rfl) ⟨1147739, by rfl⟩ : syracuseStep 6121277 = 2295479) B2295479
theorem B714751 : Blo 714321 714751 := bstep (se 1 (by rfl) ⟨536063, by rfl⟩ : syracuseStep 714751 = 1072127) B1072127
theorem B1534079 : Blo 714321 1534079 := bstep (se 1 (by rfl) ⟨1150559, by rfl⟩ : syracuseStep 1534079 = 2301119) B2301119
theorem B714959 : Blo 714321 714959 := bstep (se 1 (by rfl) ⟨536219, by rfl⟩ : syracuseStep 714959 = 1072439) B1072439
theorem B53701177 : Blo 714321 53701177 := bstep (se 2 (by rfl) ⟨20137941, by rfl⟩ : syracuseStep 53701177 = 40275883) B40275883
theorem B49572971 : Blo 714321 49572971 := bstep (se 1 (by rfl) ⟨37179728, by rfl⟩ : syracuseStep 49572971 = 74359457) B74359457
theorem B1207433 : Blo 714321 1207433 := bstep (se 2 (by rfl) ⟨452787, by rfl⟩ : syracuseStep 1207433 = 905575) B905575
theorem B1207723 : Blo 714321 1207723 := bstep (se 1 (by rfl) ⟨905792, by rfl⟩ : syracuseStep 1207723 = 1811585) B1811585
theorem B716287 : Blo 714321 716287 := bstep (se 1 (by rfl) ⟨537215, by rfl⟩ : syracuseStep 716287 = 1074431) B1074431
theorem B13233743 : Blo 714321 13233743 := bstep (se 1 (by rfl) ⟨9925307, by rfl⟩ : syracuseStep 13233743 = 19850615) B19850615
theorem B716443 : Blo 714321 716443 := bstep (se 1 (by rfl) ⟨537332, by rfl⟩ : syracuseStep 716443 = 1074665) B1074665
theorem B716703 : Blo 714321 716703 := bstep (se 1 (by rfl) ⟨537527, by rfl⟩ : syracuseStep 716703 = 1075055) B1075055
theorem B1077161 : Blo 714321 1077161 := bstep (se 2 (by rfl) ⟨403935, by rfl⟩ : syracuseStep 1077161 = 807871) B807871
theorem B1077227 : Blo 714321 1077227 := bstep (se 1 (by rfl) ⟨807920, by rfl⟩ : syracuseStep 1077227 = 1615841) B1615841
theorem B716911 : Blo 714321 716911 := bstep (se 1 (by rfl) ⟨537683, by rfl⟩ : syracuseStep 716911 = 1075367) B1075367
theorem B1077407 : Blo 714321 1077407 := bstep (se 1 (by rfl) ⟨808055, by rfl⟩ : syracuseStep 1077407 = 1616111) B1616111
theorem B12251573 : Blo 714321 12251573 := bstep (se 5 (by rfl) ⟨574292, by rfl⟩ : syracuseStep 12251573 = 1148585) B1148585
theorem B13103693 : Blo 714321 13103693 := bstep (se 3 (by rfl) ⟨2456942, by rfl⟩ : syracuseStep 13103693 = 4913885) B4913885
theorem B169997105 : Blo 714321 169997105 := bstep (se 2 (by rfl) ⟨63748914, by rfl⟩ : syracuseStep 169997105 = 127497829) B127497829
theorem B718047 : Blo 714321 718047 := bstep (se 1 (by rfl) ⟨538535, by rfl⟩ : syracuseStep 718047 = 1077071) B1077071
theorem B5174921 : Blo 714321 5174921 := bstep (se 2 (by rfl) ⟨1940595, by rfl⟩ : syracuseStep 5174921 = 3881191) B3881191
theorem B2422547 : Blo 714321 2422547 := bstep (se 1 (by rfl) ⟨1816910, by rfl⟩ : syracuseStep 2422547 = 3633821) B3633821
theorem B9796241 : Blo 714321 9796241 := bstep (se 2 (by rfl) ⟨3673590, by rfl⟩ : syracuseStep 9796241 = 7347181) B7347181
theorem B1375643 : Blo 714321 1375643 := bstep (se 1 (by rfl) ⟨1031732, by rfl⟩ : syracuseStep 1375643 = 2063465) B2063465
theorem B1147535 : Blo 714321 1147535 := bstep (se 1 (by rfl) ⟨860651, by rfl⟩ : syracuseStep 1147535 = 1721303) B1721303
theorem B1935407 : Blo 714321 1935407 := bstep (se 1 (by rfl) ⟨1451555, by rfl⟩ : syracuseStep 1935407 = 2903111) B2903111
theorem B1607849 : Blo 714321 1607849 := bstep (se 2 (by rfl) ⟨602943, by rfl⟩ : syracuseStep 1607849 = 1205887) B1205887
theorem B71601569 : Blo 714321 71601569 := bstep (se 2 (by rfl) ⟨26850588, by rfl⟩ : syracuseStep 71601569 = 53701177) B53701177
theorem B1610207 : Blo 714321 1610207 := bstep (se 1 (by rfl) ⟨1207655, by rfl⟩ : syracuseStep 1610207 = 2415311) B2415311
theorem B1610297 : Blo 714321 1610297 := bstep (se 2 (by rfl) ⟨603861, by rfl⟩ : syracuseStep 1610297 = 1207723) B1207723
theorem B1610567 : Blo 714321 1610567 := bstep (se 1 (by rfl) ⟨1207925, by rfl⟩ : syracuseStep 1610567 = 2415851) B2415851
theorem B8262623 : Blo 714321 8262623 := bstep (se 1 (by rfl) ⟨6196967, by rfl⟩ : syracuseStep 8262623 = 12393935) B12393935
theorem B4199663 : Blo 714321 4199663 := bstep (se 1 (by rfl) ⟨3149747, by rfl⟩ : syracuseStep 4199663 = 6299495) B6299495
theorem B1611071 : Blo 714321 1611071 := bstep (se 1 (by rfl) ⟨1208303, by rfl⟩ : syracuseStep 1611071 = 2416607) B2416607
theorem B8689373 : Blo 714321 8689373 := bstep (se 3 (by rfl) ⟨1629257, by rfl⟩ : syracuseStep 8689373 = 3258515) B3258515
theorem B3446525 : Blo 714321 3446525 := bstep (se 3 (by rfl) ⟨646223, by rfl⟩ : syracuseStep 3446525 = 1292447) B1292447
theorem B1022719 : Blo 714321 1022719 := bstep (se 1 (by rfl) ⟨767039, by rfl⟩ : syracuseStep 1022719 = 1534079) B1534079
theorem B4594751 : Blo 714321 4594751 := bstep (se 1 (by rfl) ⟨3446063, by rfl⟩ : syracuseStep 4594751 = 6892127) B6892127
theorem B8822495 : Blo 714321 8822495 := bstep (se 1 (by rfl) ⟨6616871, by rfl⟩ : syracuseStep 8822495 = 13233743) B13233743
theorem B1132666847 : Blo 714321 1132666847 := bstep (se 1 (by rfl) ⟨849500135, by rfl⟩ : syracuseStep 1132666847 = 1699000271) B1699000271
theorem B2039879 : Blo 714321 2039879 := bstep (se 1 (by rfl) ⟨1529909, by rfl⟩ : syracuseStep 2039879 = 3059819) B3059819
theorem B8167715 : Blo 714321 8167715 := bstep (se 1 (by rfl) ⟨6125786, by rfl⟩ : syracuseStep 8167715 = 12251573) B12251573
theorem B3449947 : Blo 714321 3449947 := bstep (se 1 (by rfl) ⟨2587460, by rfl⟩ : syracuseStep 3449947 = 5174921) B5174921
theorem B1615031 : Blo 714321 1615031 := bstep (se 1 (by rfl) ⟨1211273, by rfl⟩ : syracuseStep 1615031 = 2422547) B2422547
theorem B6530827 : Blo 714321 6530827 := bstep (se 1 (by rfl) ⟨4898120, by rfl⟩ : syracuseStep 6530827 = 9796241) B9796241
theorem B6891479 : Blo 714321 6891479 := bstep (se 1 (by rfl) ⟨5168609, by rfl⟩ : syracuseStep 6891479 = 10337219) B10337219
theorem B1812577 : Blo 714321 1812577 := bstep (se 2 (by rfl) ⟨679716, by rfl⟩ : syracuseStep 1812577 = 1359433) B1359433
theorem B1716335 : Blo 714321 1716335 := bstep (se 1 (by rfl) ⟨1287251, by rfl⟩ : syracuseStep 1716335 = 2574503) B2574503
theorem B13775183 : Blo 714321 13775183 := bstep (se 1 (by rfl) ⟨10331387, by rfl⟩ : syracuseStep 13775183 = 20662775) B20662775
theorem B17412997 : Blo 714321 17412997 := bstep (se 4 (by rfl) ⟨1632468, by rfl⟩ : syracuseStep 17412997 = 3264937) B3264937
theorem B4076477 : Blo 714321 4076477 := bstep (se 3 (by rfl) ⟨764339, by rfl⟩ : syracuseStep 4076477 = 1528679) B1528679
theorem B15677479 : Blo 714321 15677479 := bstep (se 1 (by rfl) ⟨11758109, by rfl⟩ : syracuseStep 15677479 = 23516219) B23516219
theorem B11745647 : Blo 714321 11745647 := bstep (se 1 (by rfl) ⟨8809235, by rfl⟩ : syracuseStep 11745647 = 17618471) B17618471
theorem B1817579 : Blo 714321 1817579 := bstep (se 1 (by rfl) ⟨1363184, by rfl⟩ : syracuseStep 1817579 = 2726369) B2726369
theorem B4080851 : Blo 714321 4080851 := bstep (se 1 (by rfl) ⟨3060638, by rfl⟩ : syracuseStep 4080851 = 6121277) B6121277
theorem B33048647 : Blo 714321 33048647 := bstep (se 1 (by rfl) ⟨24786485, by rfl⟩ : syracuseStep 33048647 = 49572971) B49572971
theorem B804955 : Blo 714321 804955 := bstep (se 1 (by rfl) ⟨603716, by rfl⟩ : syracuseStep 804955 = 1207433) B1207433
theorem B13781177 : Blo 714321 13781177 := bstep (se 2 (by rfl) ⟨5167941, by rfl⟩ : syracuseStep 13781177 = 10335883) B10335883
theorem B13748575 : Blo 714321 13748575 := bstep (se 1 (by rfl) ⟨10311431, by rfl⟩ : syracuseStep 13748575 = 20622863) B20622863
theorem B7457305 : Blo 714321 7457305 := bstep (se 2 (by rfl) ⟨2796489, by rfl⟩ : syracuseStep 7457305 = 5592979) B5592979
theorem B5425703 : Blo 714321 5425703 := bstep (se 1 (by rfl) ⟨4069277, by rfl⟩ : syracuseStep 5425703 = 8138555) B8138555
theorem B8735795 : Blo 714321 8735795 := bstep (se 1 (by rfl) ⟨6551846, by rfl⟩ : syracuseStep 8735795 = 13103693) B13103693
theorem B113331403 : Blo 714321 113331403 := bstep (se 1 (by rfl) ⟨84998552, by rfl⟩ : syracuseStep 113331403 = 169997105) B169997105
theorem B12242825 : Blo 714321 12242825 := bstep (se 2 (by rfl) ⟨4591059, by rfl⟩ : syracuseStep 12242825 = 9182119) B9182119
theorem B905195 : Blo 714321 905195 := bstep (se 1 (by rfl) ⟨678896, by rfl⟩ : syracuseStep 905195 = 1357793) B1357793
theorem B5165147 : Blo 714321 5165147 := bstep (se 1 (by rfl) ⟨3873860, by rfl⟩ : syracuseStep 5165147 = 7747721) B7747721
theorem B7853483 : Blo 714321 7853483 := bstep (se 1 (by rfl) ⟨5890112, by rfl⟩ : syracuseStep 7853483 = 11780225) B11780225
theorem B1071671 : Blo 714321 1071671 := bstep (se 1 (by rfl) ⟨803753, by rfl⟩ : syracuseStep 1071671 = 1607507) B1607507
theorem B1072487 : Blo 714321 1072487 := bstep (se 1 (by rfl) ⟨804365, by rfl⟩ : syracuseStep 1072487 = 1608731) B1608731
theorem B31055399 : Blo 714321 31055399 := bstep (se 1 (by rfl) ⟨23291549, by rfl⟩ : syracuseStep 31055399 = 46583099) B46583099
theorem B1072799 : Blo 714321 1072799 := bstep (se 1 (by rfl) ⟨804599, by rfl⟩ : syracuseStep 1072799 = 1609199) B1609199
theorem B3628799 : Blo 714321 3628799 := bstep (se 1 (by rfl) ⟨2721599, by rfl⟩ : syracuseStep 3628799 = 5443199) B5443199
theorem B1073243 : Blo 714321 1073243 := bstep (se 1 (by rfl) ⟨804932, by rfl⟩ : syracuseStep 1073243 = 1609865) B1609865
theorem B2416823 : Blo 714321 2416823 := bstep (se 1 (by rfl) ⟨1812617, by rfl⟩ : syracuseStep 2416823 = 3625235) B3625235
theorem B1073705 : Blo 714321 1073705 := bstep (se 2 (by rfl) ⟨402639, by rfl⟩ : syracuseStep 1073705 = 805279) B805279
theorem B1073915 : Blo 714321 1073915 := bstep (se 1 (by rfl) ⟨805436, by rfl⟩ : syracuseStep 1073915 = 1610873) B1610873
theorem B5432507 : Blo 714321 5432507 := bstep (se 1 (by rfl) ⟨4074380, by rfl⟩ : syracuseStep 5432507 = 8148761) B8148761
theorem B2417903 : Blo 714321 2417903 := bstep (se 1 (by rfl) ⟨1813427, by rfl⟩ : syracuseStep 2417903 = 3626855) B3626855
theorem B4089143 : Blo 714321 4089143 := bstep (se 1 (by rfl) ⟨3066857, by rfl⟩ : syracuseStep 4089143 = 6133715) B6133715
theorem B2418011 : Blo 714321 2418011 := bstep (se 1 (by rfl) ⟨1813508, by rfl⟩ : syracuseStep 2418011 = 3627017) B3627017
theorem B3728879 : Blo 714321 3728879 := bstep (se 1 (by rfl) ⟨2796659, by rfl⟩ : syracuseStep 3728879 = 5593319) B5593319
theorem B714523 : Blo 714321 714523 := bstep (se 1 (by rfl) ⟨535892, by rfl⟩ : syracuseStep 714523 = 1071785) B1071785
theorem B1074983 : Blo 714321 1074983 := bstep (se 1 (by rfl) ⟨806237, by rfl⟩ : syracuseStep 1074983 = 1612475) B1612475
theorem B3926087 : Blo 714321 3926087 := bstep (se 1 (by rfl) ⟨2944565, by rfl⟩ : syracuseStep 3926087 = 5889131) B5889131
theorem B715163 : Blo 714321 715163 := bstep (se 1 (by rfl) ⟨536372, by rfl⟩ : syracuseStep 715163 = 1072745) B1072745
theorem B715551 : Blo 714321 715551 := bstep (se 1 (by rfl) ⟨536663, by rfl⟩ : syracuseStep 715551 = 1073327) B1073327
theorem B715903 : Blo 714321 715903 := bstep (se 1 (by rfl) ⟨536927, by rfl⟩ : syracuseStep 715903 = 1073855) B1073855
theorem B1076351 : Blo 714321 1076351 := bstep (se 1 (by rfl) ⟨807263, by rfl⟩ : syracuseStep 1076351 = 1614527) B1614527
theorem B2715191 : Blo 714321 2715191 := bstep (se 1 (by rfl) ⟨2036393, by rfl⟩ : syracuseStep 2715191 = 4072787) B4072787
theorem B1077311 : Blo 714321 1077311 := bstep (se 1 (by rfl) ⟨807983, by rfl⟩ : syracuseStep 1077311 = 1615967) B1615967
theorem B1077359 : Blo 714321 1077359 := bstep (se 1 (by rfl) ⟨808019, by rfl⟩ : syracuseStep 1077359 = 1616039) B1616039
theorem B62681849 : Blo 714321 62681849 := bstep (se 2 (by rfl) ⟨23505693, by rfl⟩ : syracuseStep 62681849 = 47011387) B47011387
theorem B3634145 : Blo 714321 3634145 := bstep (se 2 (by rfl) ⟨1362804, by rfl⟩ : syracuseStep 3634145 = 2725609) B2725609
theorem B718107 : Blo 714321 718107 := bstep (se 1 (by rfl) ⟨538580, by rfl⟩ : syracuseStep 718107 = 1077161) B1077161
theorem B718151 : Blo 714321 718151 := bstep (se 1 (by rfl) ⟨538613, by rfl⟩ : syracuseStep 718151 = 1077227) B1077227
theorem B718271 : Blo 714321 718271 := bstep (se 1 (by rfl) ⟨538703, by rfl⟩ : syracuseStep 718271 = 1077407) B1077407
theorem B29391011 : Blo 714321 29391011 := bstep (se 1 (by rfl) ⟨22043258, by rfl⟩ : syracuseStep 29391011 = 44086517) B44086517
theorem B917095 : Blo 714321 917095 := bstep (se 1 (by rfl) ⟨687821, by rfl⟩ : syracuseStep 917095 = 1375643) B1375643
theorem B2720567 : Blo 714321 2720567 := bstep (se 1 (by rfl) ⟨2040425, by rfl⟩ : syracuseStep 2720567 = 4080851) B4080851
theorem B8161883 : Blo 714321 8161883 := bstep (se 1 (by rfl) ⟨6121412, by rfl⟩ : syracuseStep 8161883 = 12242825) B12242825
theorem B5508415 : Blo 714321 5508415 := bstep (se 1 (by rfl) ⟨4131311, by rfl⟩ : syracuseStep 5508415 = 8262623) B8262623
theorem B20942621 : Blo 714321 20942621 := bstep (se 3 (by rfl) ⟨3926741, by rfl⟩ : syracuseStep 20942621 = 7853483) B7853483
theorem B2297683 : Blo 714321 2297683 := bstep (se 1 (by rfl) ⟨1723262, by rfl⟩ : syracuseStep 2297683 = 3446525) B3446525
theorem B755111231 : Blo 714321 755111231 := bstep (se 1 (by rfl) ⟨566333423, by rfl⟩ : syracuseStep 755111231 = 1132666847) B1132666847
theorem B1611215 : Blo 714321 1611215 := bstep (se 1 (by rfl) ⟨1208411, by rfl⟩ : syracuseStep 1611215 = 2416823) B2416823
theorem B5445143 : Blo 714321 5445143 := bstep (se 1 (by rfl) ⟨4083857, by rfl⟩ : syracuseStep 5445143 = 8167715) B8167715
theorem B1611935 : Blo 714321 1611935 := bstep (se 1 (by rfl) ⟨1208951, by rfl⟩ : syracuseStep 1611935 = 2417903) B2417903
theorem B2726095 : Blo 714321 2726095 := bstep (se 1 (by rfl) ⟨2044571, by rfl⟩ : syracuseStep 2726095 = 4089143) B4089143
theorem B1612007 : Blo 714321 1612007 := bstep (se 1 (by rfl) ⟨1209005, by rfl⟩ : syracuseStep 1612007 = 2418011) B2418011
theorem B4594319 : Blo 714321 4594319 := bstep (se 1 (by rfl) ⟨3445739, by rfl⟩ : syracuseStep 4594319 = 6891479) B6891479
theorem B1810127 : Blo 714321 1810127 := bstep (se 1 (by rfl) ⟨1357595, by rfl⟩ : syracuseStep 1810127 = 2715191) B2715191
theorem B9183455 : Blo 714321 9183455 := bstep (se 1 (by rfl) ⟨6887591, by rfl⟩ : syracuseStep 9183455 = 13775183) B13775183
theorem B41787899 : Blo 714321 41787899 := bstep (se 1 (by rfl) ⟨31340924, by rfl⟩ : syracuseStep 41787899 = 62681849) B62681849
theorem B1222793 : Blo 714321 1222793 := bstep (se 2 (by rfl) ⟨458547, by rfl⟩ : syracuseStep 1222793 = 917095) B917095
theorem B13773725 : Blo 714321 13773725 := bstep (se 3 (by rfl) ⟨2582573, by rfl⟩ : syracuseStep 13773725 = 5165147) B5165147
theorem B765023 : Blo 714321 765023 := bstep (se 1 (by rfl) ⟨573767, by rfl⟩ : syracuseStep 765023 = 1147535) B1147535
theorem B1290271 : Blo 714321 1290271 := bstep (se 1 (by rfl) ⟨967703, by rfl⟩ : syracuseStep 1290271 = 1935407) B1935407
theorem B22032431 : Blo 714321 22032431 := bstep (se 1 (by rfl) ⟨16524323, by rfl⟩ : syracuseStep 22032431 = 33048647) B33048647
theorem B4599929 : Blo 714321 4599929 := bstep (se 2 (by rfl) ⟨1724973, by rfl⟩ : syracuseStep 4599929 = 3449947) B3449947
theorem B9187451 : Blo 714321 9187451 := bstep (se 1 (by rfl) ⟨6890588, by rfl⟩ : syracuseStep 9187451 = 13781177) B13781177
theorem B3617135 : Blo 714321 3617135 := bstep (se 1 (by rfl) ⟨2712851, by rfl⟩ : syracuseStep 3617135 = 5425703) B5425703
theorem B18331433 : Blo 714321 18331433 := bstep (se 2 (by rfl) ⟨6874287, by rfl⟩ : syracuseStep 18331433 = 13748575) B13748575
theorem B9943073 : Blo 714321 9943073 := bstep (se 2 (by rfl) ⟨3728652, by rfl⟩ : syracuseStep 9943073 = 7457305) B7457305
theorem B2799775 : Blo 714321 2799775 := bstep (se 1 (by rfl) ⟨2099831, by rfl⟩ : syracuseStep 2799775 = 4199663) B4199663
theorem B151108537 : Blo 714321 151108537 := bstep (se 2 (by rfl) ⟨56665701, by rfl⟩ : syracuseStep 151108537 = 113331403) B113331403
theorem B3063167 : Blo 714321 3063167 := bstep (se 1 (by rfl) ⟨2297375, by rfl⟩ : syracuseStep 3063167 = 4594751) B4594751
theorem B5881663 : Blo 714321 5881663 := bstep (se 1 (by rfl) ⟨4411247, by rfl⟩ : syracuseStep 5881663 = 8822495) B8822495
theorem B1359919 : Blo 714321 1359919 := bstep (se 1 (by rfl) ⟨1019939, by rfl⟩ : syracuseStep 1359919 = 2039879) B2039879
theorem B3621671 : Blo 714321 3621671 := bstep (se 1 (by rfl) ⟨2716253, by rfl⟩ : syracuseStep 3621671 = 5432507) B5432507
theorem B23217329 : Blo 714321 23217329 := bstep (se 2 (by rfl) ⟨8706498, by rfl⟩ : syracuseStep 23217329 = 17412997) B17412997
theorem B1363625 : Blo 714321 1363625 := bstep (se 2 (by rfl) ⟨511359, by rfl⟩ : syracuseStep 1363625 = 1022719) B1022719
theorem B2413853 : Blo 714321 2413853 := bstep (se 3 (by rfl) ⟨452597, by rfl⟩ : syracuseStep 2413853 = 905195) B905195
theorem B1071899 : Blo 714321 1071899 := bstep (se 1 (by rfl) ⟨803924, by rfl⟩ : syracuseStep 1071899 = 1607849) B1607849
theorem B5823863 : Blo 714321 5823863 := bstep (se 1 (by rfl) ⟨4367897, by rfl⟩ : syracuseStep 5823863 = 8735795) B8735795
theorem B47734379 : Blo 714321 47734379 := bstep (se 1 (by rfl) ⟨35800784, by rfl⟩ : syracuseStep 47734379 = 71601569) B71601569
theorem B8707769 : Blo 714321 8707769 := bstep (se 2 (by rfl) ⟨3265413, by rfl⟩ : syracuseStep 8707769 = 6530827) B6530827
theorem B1073273 : Blo 714321 1073273 := bstep (se 2 (by rfl) ⟨402477, by rfl⟩ : syracuseStep 1073273 = 804955) B804955
theorem B2416769 : Blo 714321 2416769 := bstep (se 2 (by rfl) ⟨906288, by rfl⟩ : syracuseStep 2416769 = 1812577) B1812577
theorem B1073471 : Blo 714321 1073471 := bstep (se 1 (by rfl) ⟨805103, by rfl⟩ : syracuseStep 1073471 = 1610207) B1610207
theorem B1073531 : Blo 714321 1073531 := bstep (se 1 (by rfl) ⟨805148, by rfl⟩ : syracuseStep 1073531 = 1610297) B1610297
theorem B1073711 : Blo 714321 1073711 := bstep (se 1 (by rfl) ⟨805283, by rfl⟩ : syracuseStep 1073711 = 1610567) B1610567
theorem B1074047 : Blo 714321 1074047 := bstep (se 1 (by rfl) ⟨805535, by rfl⟩ : syracuseStep 1074047 = 1611071) B1611071
theorem B5792915 : Blo 714321 5792915 := bstep (se 1 (by rfl) ⟨4344686, by rfl⟩ : syracuseStep 5792915 = 8689373) B8689373
theorem B714447 : Blo 714321 714447 := bstep (se 1 (by rfl) ⟨535835, by rfl⟩ : syracuseStep 714447 = 1071671) B1071671
theorem B714991 : Blo 714321 714991 := bstep (se 1 (by rfl) ⟨536243, by rfl⟩ : syracuseStep 714991 = 1072487) B1072487
theorem B20703599 : Blo 714321 20703599 := bstep (se 1 (by rfl) ⟨15527699, by rfl⟩ : syracuseStep 20703599 = 31055399) B31055399
theorem B715199 : Blo 714321 715199 := bstep (se 1 (by rfl) ⟨536399, by rfl⟩ : syracuseStep 715199 = 1072799) B1072799
theorem B2419199 : Blo 714321 2419199 := bstep (se 1 (by rfl) ⟨1814399, by rfl⟩ : syracuseStep 2419199 = 3628799) B3628799
theorem B715495 : Blo 714321 715495 := bstep (se 1 (by rfl) ⟨536621, by rfl⟩ : syracuseStep 715495 = 1073243) B1073243
theorem B715803 : Blo 714321 715803 := bstep (se 1 (by rfl) ⟨536852, by rfl⟩ : syracuseStep 715803 = 1073705) B1073705
theorem B715943 : Blo 714321 715943 := bstep (se 1 (by rfl) ⟨536957, by rfl⟩ : syracuseStep 715943 = 1073915) B1073915
theorem B1076687 : Blo 714321 1076687 := bstep (se 1 (by rfl) ⟨807515, by rfl⟩ : syracuseStep 1076687 = 1615031) B1615031
theorem B2485919 : Blo 714321 2485919 := bstep (se 1 (by rfl) ⟨1864439, by rfl⟩ : syracuseStep 2485919 = 3728879) B3728879
theorem B716655 : Blo 714321 716655 := bstep (se 1 (by rfl) ⟨537491, by rfl⟩ : syracuseStep 716655 = 1074983) B1074983
theorem B2617391 : Blo 714321 2617391 := bstep (se 1 (by rfl) ⟨1963043, by rfl⟩ : syracuseStep 2617391 = 3926087) B3926087
theorem B717567 : Blo 714321 717567 := bstep (se 1 (by rfl) ⟨538175, by rfl⟩ : syracuseStep 717567 = 1076351) B1076351
theorem B718207 : Blo 714321 718207 := bstep (se 1 (by rfl) ⟨538655, by rfl⟩ : syracuseStep 718207 = 1077311) B1077311
theorem B20903305 : Blo 714321 20903305 := bstep (se 2 (by rfl) ⟨7838739, by rfl⟩ : syracuseStep 20903305 = 15677479) B15677479
theorem B1144223 : Blo 714321 1144223 := bstep (se 1 (by rfl) ⟨858167, by rfl⟩ : syracuseStep 1144223 = 1716335) B1716335
theorem B718239 : Blo 714321 718239 := bstep (se 1 (by rfl) ⟨538679, by rfl⟩ : syracuseStep 718239 = 1077359) B1077359
theorem B2717651 : Blo 714321 2717651 := bstep (se 1 (by rfl) ⟨2038238, by rfl⟩ : syracuseStep 2717651 = 4076477) B4076477
theorem B2422763 : Blo 714321 2422763 := bstep (se 1 (by rfl) ⟨1817072, by rfl⟩ : syracuseStep 2422763 = 3634145) B3634145
theorem B19594007 : Blo 714321 19594007 := bstep (se 1 (by rfl) ⟨14695505, by rfl⟩ : syracuseStep 19594007 = 29391011) B29391011
theorem B7830431 : Blo 714321 7830431 := bstep (se 1 (by rfl) ⟨5872823, by rfl⟩ : syracuseStep 7830431 = 11745647) B11745647
theorem B1211719 : Blo 714321 1211719 := bstep (se 1 (by rfl) ⟨908789, by rfl⟩ : syracuseStep 1211719 = 1817579) B1817579
theorem B6979709 : Blo 714321 6979709 := bstep (se 3 (by rfl) ⟨1308695, by rfl⟩ : syracuseStep 6979709 = 2617391) B2617391
theorem B5441255 : Blo 714321 5441255 := bstep (se 1 (by rfl) ⟨4080941, by rfl⟩ : syracuseStep 5441255 = 8161883) B8161883
theorem B13961747 : Blo 714321 13961747 := bstep (se 1 (by rfl) ⟨10471310, by rfl⟩ : syracuseStep 13961747 = 20942621) B20942621
theorem B1609235 : Blo 714321 1609235 := bstep (se 1 (by rfl) ⟨1206926, by rfl⟩ : syracuseStep 1609235 = 2413853) B2413853
theorem B31822919 : Blo 714321 31822919 := bstep (se 1 (by rfl) ⟨23867189, by rfl⟩ : syracuseStep 31822919 = 47734379) B47734379
theorem B5805179 : Blo 714321 5805179 := bstep (se 1 (by rfl) ⟨4353884, by rfl⟩ : syracuseStep 5805179 = 8707769) B8707769
theorem B1611179 : Blo 714321 1611179 := bstep (se 1 (by rfl) ⟨1208384, by rfl⟩ : syracuseStep 1611179 = 2416769) B2416769
theorem B27858599 : Blo 714321 27858599 := bstep (se 1 (by rfl) ⟨20893949, by rfl⟩ : syracuseStep 27858599 = 41787899) B41787899
theorem B13802399 : Blo 714321 13802399 := bstep (se 1 (by rfl) ⟨10351799, by rfl⟩ : syracuseStep 13802399 = 20703599) B20703599
theorem B1612799 : Blo 714321 1612799 := bstep (se 1 (by rfl) ⟨1209599, by rfl⟩ : syracuseStep 1612799 = 2419199) B2419199
theorem B9182483 : Blo 714321 9182483 := bstep (se 1 (by rfl) ⟨6886862, by rfl⟩ : syracuseStep 9182483 = 13773725) B13773725
theorem B14688287 : Blo 714321 14688287 := bstep (se 1 (by rfl) ⟨11016215, by rfl⟩ : syracuseStep 14688287 = 22032431) B22032431
theorem B2040061 : Blo 714321 2040061 := bstep (se 3 (by rfl) ⟨382511, by rfl⟩ : syracuseStep 2040061 = 765023) B765023
theorem B762815 : Blo 714321 762815 := bstep (se 1 (by rfl) ⟨572111, by rfl⟩ : syracuseStep 762815 = 1144223) B1144223
theorem B1811767 : Blo 714321 1811767 := bstep (se 1 (by rfl) ⟨1358825, by rfl⟩ : syracuseStep 1811767 = 2717651) B2717651
theorem B1615175 : Blo 714321 1615175 := bstep (se 1 (by rfl) ⟨1211381, by rfl⟩ : syracuseStep 1615175 = 2422763) B2422763
theorem B6628715 : Blo 714321 6628715 := bstep (se 1 (by rfl) ⟨4971536, by rfl⟩ : syracuseStep 6628715 = 9943073) B9943073
theorem B1615625 : Blo 714321 1615625 := bstep (se 2 (by rfl) ⟨605859, by rfl⟩ : syracuseStep 1615625 = 1211719) B1211719
theorem B5220287 : Blo 714321 5220287 := bstep (se 1 (by rfl) ⟨3915215, by rfl⟩ : syracuseStep 5220287 = 7830431) B7830431
theorem B2042111 : Blo 714321 2042111 := bstep (se 1 (by rfl) ⟨1531583, by rfl⟩ : syracuseStep 2042111 = 3063167) B3063167
theorem B7842217 : Blo 714321 7842217 := bstep (se 2 (by rfl) ⟨2940831, by rfl⟩ : syracuseStep 7842217 = 5881663) B5881663
theorem B1813225 : Blo 714321 1813225 := bstep (se 2 (by rfl) ⟨679959, by rfl⟩ : syracuseStep 1813225 = 1359919) B1359919
theorem B1813711 : Blo 714321 1813711 := bstep (se 1 (by rfl) ⟨1360283, by rfl⟩ : syracuseStep 1813711 = 2720567) B2720567
theorem B15478219 : Blo 714321 15478219 := bstep (se 1 (by rfl) ⟨11608664, by rfl⟩ : syracuseStep 15478219 = 23217329) B23217329
theorem B15447773 : Blo 714321 15447773 := bstep (se 3 (by rfl) ⟨2896457, by rfl⟩ : syracuseStep 15447773 = 5792915) B5792915
theorem B3062879 : Blo 714321 3062879 := bstep (se 1 (by rfl) ⟨2297159, by rfl⟩ : syracuseStep 3062879 = 4594319) B4594319
theorem B3882575 : Blo 714321 3882575 := bstep (se 1 (by rfl) ⟨2911931, by rfl⟩ : syracuseStep 3882575 = 5823863) B5823863
theorem B3063577 : Blo 714321 3063577 := bstep (se 2 (by rfl) ⟨1148841, by rfl⟩ : syracuseStep 3063577 = 2297683) B2297683
theorem B1720361 : Blo 714321 1720361 := bstep (se 2 (by rfl) ⟨645135, by rfl⟩ : syracuseStep 1720361 = 1290271) B1290271
theorem B29378213 : Blo 714321 29378213 := bstep (se 4 (by rfl) ⟨2754207, by rfl⟩ : syracuseStep 29378213 = 5508415) B5508415
theorem B27871073 : Blo 714321 27871073 := bstep (se 2 (by rfl) ⟨10451652, by rfl⟩ : syracuseStep 27871073 = 20903305) B20903305
theorem B1657279 : Blo 714321 1657279 := bstep (se 1 (by rfl) ⟨1242959, by rfl⟩ : syracuseStep 1657279 = 2485919) B2485919
theorem B3066619 : Blo 714321 3066619 := bstep (se 1 (by rfl) ⟨2299964, by rfl⟩ : syracuseStep 3066619 = 4599929) B4599929
theorem B2411423 : Blo 714321 2411423 := bstep (se 1 (by rfl) ⟨1808567, by rfl⟩ : syracuseStep 2411423 = 3617135) B3617135
theorem B201478049 : Blo 714321 201478049 := bstep (se 2 (by rfl) ⟨75554268, by rfl⟩ : syracuseStep 201478049 = 151108537) B151108537
theorem B13062671 : Blo 714321 13062671 := bstep (se 1 (by rfl) ⟨9797003, by rfl⟩ : syracuseStep 13062671 = 19594007) B19594007
theorem B2414447 : Blo 714321 2414447 := bstep (se 1 (by rfl) ⟨1810835, by rfl⟩ : syracuseStep 2414447 = 3621671) B3621671
theorem B909083 : Blo 714321 909083 := bstep (se 1 (by rfl) ⟨681812, by rfl⟩ : syracuseStep 909083 = 1363625) B1363625
theorem B503407487 : Blo 714321 503407487 := bstep (se 1 (by rfl) ⟨377555615, by rfl⟩ : syracuseStep 503407487 = 755111231) B755111231
theorem B1074143 : Blo 714321 1074143 := bstep (se 1 (by rfl) ⟨805607, by rfl⟩ : syracuseStep 1074143 = 1611215) B1611215
theorem B3630095 : Blo 714321 3630095 := bstep (se 1 (by rfl) ⟨2722571, by rfl⟩ : syracuseStep 3630095 = 5445143) B5445143
theorem B1074623 : Blo 714321 1074623 := bstep (se 1 (by rfl) ⟨805967, by rfl⟩ : syracuseStep 1074623 = 1611935) B1611935
theorem B1074671 : Blo 714321 1074671 := bstep (se 1 (by rfl) ⟨806003, by rfl⟩ : syracuseStep 1074671 = 1612007) B1612007
theorem B714599 : Blo 714321 714599 := bstep (se 1 (by rfl) ⟨535949, by rfl⟩ : syracuseStep 714599 = 1071899) B1071899
theorem B1206751 : Blo 714321 1206751 := bstep (se 1 (by rfl) ⟨905063, by rfl⟩ : syracuseStep 1206751 = 1810127) B1810127
theorem B715515 : Blo 714321 715515 := bstep (se 1 (by rfl) ⟨536636, by rfl⟩ : syracuseStep 715515 = 1073273) B1073273
theorem B6122303 : Blo 714321 6122303 := bstep (se 1 (by rfl) ⟨4591727, by rfl⟩ : syracuseStep 6122303 = 9183455) B9183455
theorem B715647 : Blo 714321 715647 := bstep (se 1 (by rfl) ⟨536735, by rfl⟩ : syracuseStep 715647 = 1073471) B1073471
theorem B715687 : Blo 714321 715687 := bstep (se 1 (by rfl) ⟨536765, by rfl⟩ : syracuseStep 715687 = 1073531) B1073531
theorem B715807 : Blo 714321 715807 := bstep (se 1 (by rfl) ⟨536855, by rfl⟩ : syracuseStep 715807 = 1073711) B1073711
theorem B716031 : Blo 714321 716031 := bstep (se 1 (by rfl) ⟨537023, by rfl⟩ : syracuseStep 716031 = 1074047) B1074047
theorem B815195 : Blo 714321 815195 := bstep (se 1 (by rfl) ⟨611396, by rfl⟩ : syracuseStep 815195 = 1222793) B1222793
theorem B717791 : Blo 714321 717791 := bstep (se 1 (by rfl) ⟨538343, by rfl⟩ : syracuseStep 717791 = 1076687) B1076687
theorem B6124967 : Blo 714321 6124967 := bstep (se 1 (by rfl) ⟨4593725, by rfl⟩ : syracuseStep 6124967 = 9187451) B9187451
theorem B3733033 : Blo 714321 3733033 := bstep (se 2 (by rfl) ⟨1399887, by rfl⟩ : syracuseStep 3733033 = 2799775) B2799775
theorem B3634793 : Blo 714321 3634793 := bstep (se 2 (by rfl) ⟨1363047, by rfl⟩ : syracuseStep 3634793 = 2726095) B2726095
theorem B12220955 : Blo 714321 12220955 := bstep (se 1 (by rfl) ⟨9165716, by rfl⟩ : syracuseStep 12220955 = 18331433) B18331433
theorem B1146907 : Blo 714321 1146907 := bstep (se 1 (by rfl) ⟨860180, by rfl⟩ : syracuseStep 1146907 = 1720361) B1720361
theorem B4653139 : Blo 714321 4653139 := bstep (se 1 (by rfl) ⟨3489854, by rfl⟩ : syracuseStep 4653139 = 6979709) B6979709
theorem B2720081 : Blo 714321 2720081 := bstep (se 2 (by rfl) ⟨1020030, by rfl⟩ : syracuseStep 2720081 = 2040061) B2040061
theorem B18580715 : Blo 714321 18580715 := bstep (se 1 (by rfl) ⟨13935536, by rfl⟩ : syracuseStep 18580715 = 27871073) B27871073
theorem B9307831 : Blo 714321 9307831 := bstep (se 1 (by rfl) ⟨6980873, by rfl⟩ : syracuseStep 9307831 = 13961747) B13961747
theorem B1607615 : Blo 714321 1607615 := bstep (se 1 (by rfl) ⟨1205711, by rfl⟩ : syracuseStep 1607615 = 2411423) B2411423
theorem B2034173 : Blo 714321 2034173 := bstep (se 3 (by rfl) ⟨381407, by rfl⟩ : syracuseStep 2034173 = 762815) B762815
theorem B134318699 : Blo 714321 134318699 := bstep (se 1 (by rfl) ⟨100739024, by rfl⟩ : syracuseStep 134318699 = 201478049) B201478049
theorem B10456289 : Blo 714321 10456289 := bstep (se 2 (by rfl) ⟨3921108, by rfl⟩ : syracuseStep 10456289 = 7842217) B7842217
theorem B1609001 : Blo 714321 1609001 := bstep (se 2 (by rfl) ⟨603375, by rfl⟩ : syracuseStep 1609001 = 1206751) B1206751
theorem B3870119 : Blo 714321 3870119 := bstep (se 1 (by rfl) ⟨2902589, by rfl⟩ : syracuseStep 3870119 = 5805179) B5805179
theorem B1609631 : Blo 714321 1609631 := bstep (se 1 (by rfl) ⟨1207223, by rfl⟩ : syracuseStep 1609631 = 2414447) B2414447
theorem B5445629 : Blo 714321 5445629 := bstep (se 3 (by rfl) ⟨1021055, by rfl⟩ : syracuseStep 5445629 = 2042111) B2042111
theorem B3480191 : Blo 714321 3480191 := bstep (se 1 (by rfl) ⟨2610143, by rfl⟩ : syracuseStep 3480191 = 5220287) B5220287
theorem B10298515 : Blo 714321 10298515 := bstep (se 1 (by rfl) ⟨7723886, by rfl⟩ : syracuseStep 10298515 = 15447773) B15447773
theorem B2041919 : Blo 714321 2041919 := bstep (se 1 (by rfl) ⟨1531439, by rfl⟩ : syracuseStep 2041919 = 3062879) B3062879
theorem B2173853 : Blo 714321 2173853 := bstep (se 3 (by rfl) ⟨407597, by rfl⟩ : syracuseStep 2173853 = 815195) B815195
theorem B21215279 : Blo 714321 21215279 := bstep (se 1 (by rfl) ⟨15911459, by rfl⟩ : syracuseStep 21215279 = 31822919) B31822919
theorem B4081535 : Blo 714321 4081535 := bstep (se 1 (by rfl) ⟨3061151, by rfl⟩ : syracuseStep 4081535 = 6122303) B6122303
theorem B4083311 : Blo 714321 4083311 := bstep (se 1 (by rfl) ⟨3062483, by rfl⟩ : syracuseStep 4083311 = 6124967) B6124967
theorem B8147303 : Blo 714321 8147303 := bstep (se 1 (by rfl) ⟨6110477, by rfl⟩ : syracuseStep 8147303 = 12220955) B12220955
theorem B4084769 : Blo 714321 4084769 := bstep (se 2 (by rfl) ⟨1531788, by rfl⟩ : syracuseStep 4084769 = 3063577) B3063577
theorem B19585475 : Blo 714321 19585475 := bstep (se 1 (by rfl) ⟨14689106, by rfl⟩ : syracuseStep 19585475 = 29378213) B29378213
theorem B3627503 : Blo 714321 3627503 := bstep (se 1 (by rfl) ⟨2720627, by rfl⟩ : syracuseStep 3627503 = 5441255) B5441255
theorem B2415689 : Blo 714321 2415689 := bstep (se 2 (by rfl) ⟨905883, by rfl⟩ : syracuseStep 2415689 = 1811767) B1811767
theorem B8838821 : Blo 714321 8838821 := bstep (se 4 (by rfl) ⟨828639, by rfl⟩ : syracuseStep 8838821 = 1657279) B1657279
theorem B1072823 : Blo 714321 1072823 := bstep (se 1 (by rfl) ⟨804617, by rfl⟩ : syracuseStep 1072823 = 1609235) B1609235
theorem B8708447 : Blo 714321 8708447 := bstep (se 1 (by rfl) ⟨6531335, by rfl⟩ : syracuseStep 8708447 = 13062671) B13062671
theorem B1074119 : Blo 714321 1074119 := bstep (se 1 (by rfl) ⟨805589, by rfl⟩ : syracuseStep 1074119 = 1611179) B1611179
theorem B2417633 : Blo 714321 2417633 := bstep (se 2 (by rfl) ⟨906612, by rfl⟩ : syracuseStep 2417633 = 1813225) B1813225
theorem B4088825 : Blo 714321 4088825 := bstep (se 2 (by rfl) ⟨1533309, by rfl⟩ : syracuseStep 4088825 = 3066619) B3066619
theorem B18572399 : Blo 714321 18572399 := bstep (se 1 (by rfl) ⟨13929299, by rfl⟩ : syracuseStep 18572399 = 27858599) B27858599
theorem B2418281 : Blo 714321 2418281 := bstep (se 2 (by rfl) ⟨906855, by rfl⟩ : syracuseStep 2418281 = 1813711) B1813711
theorem B20637625 : Blo 714321 20637625 := bstep (se 2 (by rfl) ⟨7739109, by rfl⟩ : syracuseStep 20637625 = 15478219) B15478219
theorem B9201599 : Blo 714321 9201599 := bstep (se 1 (by rfl) ⟨6901199, by rfl⟩ : syracuseStep 9201599 = 13802399) B13802399
theorem B1075199 : Blo 714321 1075199 := bstep (se 1 (by rfl) ⟨806399, by rfl⟩ : syracuseStep 1075199 = 1612799) B1612799
theorem B6121655 : Blo 714321 6121655 := bstep (se 1 (by rfl) ⟨4591241, by rfl⟩ : syracuseStep 6121655 = 9182483) B9182483
theorem B9792191 : Blo 714321 9792191 := bstep (se 1 (by rfl) ⟨7344143, by rfl⟩ : syracuseStep 9792191 = 14688287) B14688287
theorem B335604991 : Blo 714321 335604991 := bstep (se 1 (by rfl) ⟨251703743, by rfl⟩ : syracuseStep 335604991 = 503407487) B503407487
theorem B716095 : Blo 714321 716095 := bstep (se 1 (by rfl) ⟨537071, by rfl⟩ : syracuseStep 716095 = 1074143) B1074143
theorem B2420063 : Blo 714321 2420063 := bstep (se 1 (by rfl) ⟨1815047, by rfl⟩ : syracuseStep 2420063 = 3630095) B3630095
theorem B1076783 : Blo 714321 1076783 := bstep (se 1 (by rfl) ⟨807587, by rfl⟩ : syracuseStep 1076783 = 1615175) B1615175
theorem B4419143 : Blo 714321 4419143 := bstep (se 1 (by rfl) ⟨3314357, by rfl⟩ : syracuseStep 4419143 = 6628715) B6628715
theorem B716415 : Blo 714321 716415 := bstep (se 1 (by rfl) ⟨537311, by rfl⟩ : syracuseStep 716415 = 1074623) B1074623
theorem B716447 : Blo 714321 716447 := bstep (se 1 (by rfl) ⟨537335, by rfl⟩ : syracuseStep 716447 = 1074671) B1074671
theorem B1077083 : Blo 714321 1077083 := bstep (se 1 (by rfl) ⟨807812, by rfl⟩ : syracuseStep 1077083 = 1615625) B1615625
theorem B4977377 : Blo 714321 4977377 := bstep (se 2 (by rfl) ⟨1866516, by rfl⟩ : syracuseStep 4977377 = 3733033) B3733033
theorem B2423195 : Blo 714321 2423195 := bstep (se 1 (by rfl) ⟨1817396, by rfl⟩ : syracuseStep 2423195 = 3634793) B3634793
theorem B2424221 : Blo 714321 2424221 := bstep (se 3 (by rfl) ⟨454541, by rfl⟩ : syracuseStep 2424221 = 909083) B909083
theorem B2588383 : Blo 714321 2588383 := bstep (se 1 (by rfl) ⟨1941287, by rfl⟩ : syracuseStep 2588383 = 3882575) B3882575
theorem B12387143 : Blo 714321 12387143 := bstep (se 1 (by rfl) ⟨9290357, by rfl⟩ : syracuseStep 12387143 = 18580715) B18580715
theorem B2721023 : Blo 714321 2721023 := bstep (se 1 (by rfl) ⟨2040767, by rfl⟩ : syracuseStep 2721023 = 4081535) B4081535
theorem B13731353 : Blo 714321 13731353 := bstep (se 2 (by rfl) ⟨5149257, by rfl⟩ : syracuseStep 13731353 = 10298515) B10298515
theorem B2722207 : Blo 714321 2722207 := bstep (se 1 (by rfl) ⟨2041655, by rfl⟩ : syracuseStep 2722207 = 4083311) B4083311
theorem B2723179 : Blo 714321 2723179 := bstep (se 1 (by rfl) ⟨2042384, by rfl⟩ : syracuseStep 2723179 = 4084769) B4084769
theorem B1610459 : Blo 714321 1610459 := bstep (se 1 (by rfl) ⟨1207844, by rfl⟩ : syracuseStep 1610459 = 2415689) B2415689
theorem B5805631 : Blo 714321 5805631 := bstep (se 1 (by rfl) ⟨4354223, by rfl⟩ : syracuseStep 5805631 = 8708447) B8708447
theorem B1611755 : Blo 714321 1611755 := bstep (se 1 (by rfl) ⟨1208816, by rfl⟩ : syracuseStep 1611755 = 2417633) B2417633
theorem B2725883 : Blo 714321 2725883 := bstep (se 1 (by rfl) ⟨2044412, by rfl⟩ : syracuseStep 2725883 = 4088825) B4088825
theorem B1612187 : Blo 714321 1612187 := bstep (se 1 (by rfl) ⟨1209140, by rfl⟩ : syracuseStep 1612187 = 2418281) B2418281
theorem B6134399 : Blo 714321 6134399 := bstep (se 1 (by rfl) ⟨4600799, by rfl⟩ : syracuseStep 6134399 = 9201599) B9201599
theorem B6528127 : Blo 714321 6528127 := bstep (se 1 (by rfl) ⟨4896095, by rfl⟩ : syracuseStep 6528127 = 9792191) B9792191
theorem B1449235 : Blo 714321 1449235 := bstep (se 1 (by rfl) ⟨1086926, by rfl⟩ : syracuseStep 1449235 = 2173853) B2173853
theorem B1613375 : Blo 714321 1613375 := bstep (se 1 (by rfl) ⟨1210031, by rfl⟩ : syracuseStep 1613375 = 2420063) B2420063
theorem B3318251 : Blo 714321 3318251 := bstep (se 1 (by rfl) ⟨2488688, by rfl⟩ : syracuseStep 3318251 = 4977377) B4977377
theorem B1615463 : Blo 714321 1615463 := bstep (se 1 (by rfl) ⟨1211597, by rfl⟩ : syracuseStep 1615463 = 2423195) B2423195
theorem B23570189 : Blo 714321 23570189 := bstep (se 3 (by rfl) ⟨4419410, by rfl⟩ : syracuseStep 23570189 = 8838821) B8838821
theorem B1616147 : Blo 714321 1616147 := bstep (se 1 (by rfl) ⟨1212110, by rfl⟩ : syracuseStep 1616147 = 2424221) B2424221
theorem B3451177 : Blo 714321 3451177 := bstep (se 2 (by rfl) ⟨1294191, by rfl⟩ : syracuseStep 3451177 = 2588383) B2588383
theorem B6204185 : Blo 714321 6204185 := bstep (se 2 (by rfl) ⟨2326569, by rfl⟩ : syracuseStep 6204185 = 4653139) B4653139
theorem B1813387 : Blo 714321 1813387 := bstep (se 1 (by rfl) ⟨1360040, by rfl⟩ : syracuseStep 1813387 = 2720081) B2720081
theorem B1356115 : Blo 714321 1356115 := bstep (se 1 (by rfl) ⟨1017086, by rfl⟩ : syracuseStep 1356115 = 2034173) B2034173
theorem B13056983 : Blo 714321 13056983 := bstep (se 1 (by rfl) ⟨9792737, by rfl⟩ : syracuseStep 13056983 = 19585475) B19585475
theorem B1361279 : Blo 714321 1361279 := bstep (se 1 (by rfl) ⟨1020959, by rfl⟩ : syracuseStep 1361279 = 2041919) B2041919
theorem B4081103 : Blo 714321 4081103 := bstep (se 1 (by rfl) ⟨3060827, by rfl⟩ : syracuseStep 4081103 = 6121655) B6121655
theorem B14143519 : Blo 714321 14143519 := bstep (se 1 (by rfl) ⟨10607639, by rfl⟩ : syracuseStep 14143519 = 21215279) B21215279
theorem B1529209 : Blo 714321 1529209 := bstep (se 2 (by rfl) ⟨573453, by rfl⟩ : syracuseStep 1529209 = 1146907) B1146907
theorem B1071743 : Blo 714321 1071743 := bstep (se 1 (by rfl) ⟨803807, by rfl⟩ : syracuseStep 1071743 = 1607615) B1607615
theorem B89545799 : Blo 714321 89545799 := bstep (se 1 (by rfl) ⟨67159349, by rfl⟩ : syracuseStep 89545799 = 134318699) B134318699
theorem B6970859 : Blo 714321 6970859 := bstep (se 1 (by rfl) ⟨5228144, by rfl⟩ : syracuseStep 6970859 = 10456289) B10456289
theorem B1072667 : Blo 714321 1072667 := bstep (se 1 (by rfl) ⟨804500, by rfl⟩ : syracuseStep 1072667 = 1609001) B1609001
theorem B12410441 : Blo 714321 12410441 := bstep (se 2 (by rfl) ⟨4653915, by rfl⟩ : syracuseStep 12410441 = 9307831) B9307831
theorem B27516833 : Blo 714321 27516833 := bstep (se 2 (by rfl) ⟨10318812, by rfl⟩ : syracuseStep 27516833 = 20637625) B20637625
theorem B1073087 : Blo 714321 1073087 := bstep (se 1 (by rfl) ⟨804815, by rfl⟩ : syracuseStep 1073087 = 1609631) B1609631
theorem B5431535 : Blo 714321 5431535 := bstep (se 1 (by rfl) ⟨4073651, by rfl⟩ : syracuseStep 5431535 = 8147303) B8147303
theorem B3630419 : Blo 714321 3630419 := bstep (se 1 (by rfl) ⟨2722814, by rfl⟩ : syracuseStep 3630419 = 5445629) B5445629
theorem B2418335 : Blo 714321 2418335 := bstep (se 1 (by rfl) ⟨1813751, by rfl⟩ : syracuseStep 2418335 = 3627503) B3627503
theorem B447473321 : Blo 714321 447473321 := bstep (se 2 (by rfl) ⟨167802495, by rfl⟩ : syracuseStep 447473321 = 335604991) B335604991
theorem B2320127 : Blo 714321 2320127 := bstep (se 1 (by rfl) ⟨1740095, by rfl⟩ : syracuseStep 2320127 = 3480191) B3480191
theorem B715215 : Blo 714321 715215 := bstep (se 1 (by rfl) ⟨536411, by rfl⟩ : syracuseStep 715215 = 1072823) B1072823
theorem B716079 : Blo 714321 716079 := bstep (se 1 (by rfl) ⟨537059, by rfl⟩ : syracuseStep 716079 = 1074119) B1074119
theorem B12381599 : Blo 714321 12381599 := bstep (se 1 (by rfl) ⟨9286199, by rfl⟩ : syracuseStep 12381599 = 18572399) B18572399
theorem B716799 : Blo 714321 716799 := bstep (se 1 (by rfl) ⟨537599, by rfl⟩ : syracuseStep 716799 = 1075199) B1075199
theorem B717855 : Blo 714321 717855 := bstep (se 1 (by rfl) ⟨538391, by rfl⟩ : syracuseStep 717855 = 1076783) B1076783
theorem B2946095 : Blo 714321 2946095 := bstep (se 1 (by rfl) ⟨2209571, by rfl⟩ : syracuseStep 2946095 = 4419143) B4419143
theorem B718055 : Blo 714321 718055 := bstep (se 1 (by rfl) ⟨538541, by rfl⟩ : syracuseStep 718055 = 1077083) B1077083
theorem B10320317 : Blo 714321 10320317 := bstep (se 3 (by rfl) ⟨1935059, by rfl⟩ : syracuseStep 10320317 = 3870119) B3870119
theorem B8258095 : Blo 714321 8258095 := bstep (se 1 (by rfl) ⟨6193571, by rfl⟩ : syracuseStep 8258095 = 12387143) B12387143
theorem B2720735 : Blo 714321 2720735 := bstep (se 1 (by rfl) ⟨2040551, by rfl⟩ : syracuseStep 2720735 = 4081103) B4081103
theorem B8848669 : Blo 714321 8848669 := bstep (se 3 (by rfl) ⟨1659125, by rfl⟩ : syracuseStep 8848669 = 3318251) B3318251
theorem B1808153 : Blo 714321 1808153 := bstep (se 2 (by rfl) ⟨678057, by rfl⟩ : syracuseStep 1808153 = 1356115) B1356115
theorem B1612223 : Blo 714321 1612223 := bstep (se 1 (by rfl) ⟨1209167, by rfl⟩ : syracuseStep 1612223 = 2418335) B2418335
theorem B1546751 : Blo 714321 1546751 := bstep (se 1 (by rfl) ⟨1160063, by rfl⟩ : syracuseStep 1546751 = 2320127) B2320127
theorem B2038945 : Blo 714321 2038945 := bstep (se 2 (by rfl) ⟨764604, by rfl⟩ : syracuseStep 2038945 = 1529209) B1529209
theorem B4136123 : Blo 714321 4136123 := bstep (se 1 (by rfl) ⟨3102092, by rfl⟩ : syracuseStep 4136123 = 6204185) B6204185
theorem B7740841 : Blo 714321 7740841 := bstep (se 2 (by rfl) ⟨2902815, by rfl⟩ : syracuseStep 7740841 = 5805631) B5805631
theorem B1814015 : Blo 714321 1814015 := bstep (se 1 (by rfl) ⟨1360511, by rfl⟩ : syracuseStep 1814015 = 2721023) B2721023
theorem B9154235 : Blo 714321 9154235 := bstep (se 1 (by rfl) ⟨6865676, by rfl⟩ : syracuseStep 9154235 = 13731353) B13731353
theorem B4601569 : Blo 714321 4601569 := bstep (se 2 (by rfl) ⟨1725588, by rfl⟩ : syracuseStep 4601569 = 3451177) B3451177
theorem B1817255 : Blo 714321 1817255 := bstep (se 1 (by rfl) ⟨1362941, by rfl⟩ : syracuseStep 1817255 = 2725883) B2725883
theorem B8273627 : Blo 714321 8273627 := bstep (se 1 (by rfl) ⟨6205220, by rfl⟩ : syracuseStep 8273627 = 12410441) B12410441
theorem B18858025 : Blo 714321 18858025 := bstep (se 2 (by rfl) ⟨7071759, by rfl⟩ : syracuseStep 18858025 = 14143519) B14143519
theorem B3621023 : Blo 714321 3621023 := bstep (se 1 (by rfl) ⟨2715767, by rfl⟩ : syracuseStep 3621023 = 5431535) B5431535
theorem B15713459 : Blo 714321 15713459 := bstep (se 1 (by rfl) ⟨11785094, by rfl⟩ : syracuseStep 15713459 = 23570189) B23570189
theorem B8704169 : Blo 714321 8704169 := bstep (se 2 (by rfl) ⟨3264063, by rfl⟩ : syracuseStep 8704169 = 6528127) B6528127
theorem B8704655 : Blo 714321 8704655 := bstep (se 1 (by rfl) ⟨6528491, by rfl⟩ : syracuseStep 8704655 = 13056983) B13056983
theorem B907519 : Blo 714321 907519 := bstep (se 1 (by rfl) ⟨680639, by rfl⟩ : syracuseStep 907519 = 1361279) B1361279
theorem B1073639 : Blo 714321 1073639 := bstep (se 1 (by rfl) ⟨805229, by rfl⟩ : syracuseStep 1073639 = 1610459) B1610459
theorem B3629609 : Blo 714321 3629609 := bstep (se 2 (by rfl) ⟨1361103, by rfl⟩ : syracuseStep 3629609 = 2722207) B2722207
theorem B2417849 : Blo 714321 2417849 := bstep (se 2 (by rfl) ⟨906693, by rfl⟩ : syracuseStep 2417849 = 1813387) B1813387
theorem B1074503 : Blo 714321 1074503 := bstep (se 1 (by rfl) ⟨805877, by rfl⟩ : syracuseStep 1074503 = 1611755) B1611755
theorem B1074791 : Blo 714321 1074791 := bstep (se 1 (by rfl) ⟨806093, by rfl⟩ : syracuseStep 1074791 = 1612187) B1612187
theorem B714495 : Blo 714321 714495 := bstep (se 1 (by rfl) ⟨535871, by rfl⟩ : syracuseStep 714495 = 1071743) B1071743
theorem B4089599 : Blo 714321 4089599 := bstep (se 1 (by rfl) ⟨3067199, by rfl⟩ : syracuseStep 4089599 = 6134399) B6134399
theorem B3630905 : Blo 714321 3630905 := bstep (se 2 (by rfl) ⟨1361589, by rfl⟩ : syracuseStep 3630905 = 2723179) B2723179
theorem B59697199 : Blo 714321 59697199 := bstep (se 1 (by rfl) ⟨44772899, by rfl⟩ : syracuseStep 59697199 = 89545799) B89545799
theorem B4647239 : Blo 714321 4647239 := bstep (se 1 (by rfl) ⟨3485429, by rfl⟩ : syracuseStep 4647239 = 6970859) B6970859
theorem B715111 : Blo 714321 715111 := bstep (se 1 (by rfl) ⟨536333, by rfl⟩ : syracuseStep 715111 = 1072667) B1072667
theorem B1075583 : Blo 714321 1075583 := bstep (se 1 (by rfl) ⟨806687, by rfl⟩ : syracuseStep 1075583 = 1613375) B1613375
theorem B18344555 : Blo 714321 18344555 := bstep (se 1 (by rfl) ⟨13758416, by rfl⟩ : syracuseStep 18344555 = 27516833) B27516833
theorem B715391 : Blo 714321 715391 := bstep (se 1 (by rfl) ⟨536543, by rfl⟩ : syracuseStep 715391 = 1073087) B1073087
theorem B2420279 : Blo 714321 2420279 := bstep (se 1 (by rfl) ⟨1815209, by rfl⟩ : syracuseStep 2420279 = 3630419) B3630419
theorem B1076975 : Blo 714321 1076975 := bstep (se 1 (by rfl) ⟨807731, by rfl⟩ : syracuseStep 1076975 = 1615463) B1615463
theorem B298315547 : Blo 714321 298315547 := bstep (se 1 (by rfl) ⟨223736660, by rfl⟩ : syracuseStep 298315547 = 447473321) B447473321
theorem B7729253 : Blo 714321 7729253 := bstep (se 4 (by rfl) ⟨724617, by rfl⟩ : syracuseStep 7729253 = 1449235) B1449235
theorem B1077431 : Blo 714321 1077431 := bstep (se 1 (by rfl) ⟨808073, by rfl⟩ : syracuseStep 1077431 = 1616147) B1616147
theorem B8254399 : Blo 714321 8254399 := bstep (se 1 (by rfl) ⟨6190799, by rfl⟩ : syracuseStep 8254399 = 12381599) B12381599
theorem B1964063 : Blo 714321 1964063 := bstep (se 1 (by rfl) ⟨1473047, by rfl⟩ : syracuseStep 1964063 = 2946095) B2946095
theorem B6880211 : Blo 714321 6880211 := bstep (se 1 (by rfl) ⟨5160158, by rfl⟩ : syracuseStep 6880211 = 10320317) B10320317
theorem B11798225 : Blo 714321 11798225 := bstep (se 2 (by rfl) ⟨4424334, by rfl⟩ : syracuseStep 11798225 = 8848669) B8848669
theorem B79596265 : Blo 714321 79596265 := bstep (se 2 (by rfl) ⟨29848599, by rfl⟩ : syracuseStep 79596265 = 59697199) B59697199
theorem B5802779 : Blo 714321 5802779 := bstep (se 1 (by rfl) ⟨4352084, by rfl⟩ : syracuseStep 5802779 = 8704169) B8704169
theorem B44043173 : Blo 714321 44043173 := bstep (se 4 (by rfl) ⟨4129047, by rfl⟩ : syracuseStep 44043173 = 8258095) B8258095
theorem B5803103 : Blo 714321 5803103 := bstep (se 1 (by rfl) ⟨4352327, by rfl⟩ : syracuseStep 5803103 = 8704655) B8704655
theorem B2757415 : Blo 714321 2757415 := bstep (se 1 (by rfl) ⟨2068061, by rfl⟩ : syracuseStep 2757415 = 4136123) B4136123
theorem B1611899 : Blo 714321 1611899 := bstep (se 1 (by rfl) ⟨1208924, by rfl⟩ : syracuseStep 1611899 = 2417849) B2417849
theorem B2726399 : Blo 714321 2726399 := bstep (se 1 (by rfl) ⟨2044799, by rfl⟩ : syracuseStep 2726399 = 4089599) B4089599
theorem B12229703 : Blo 714321 12229703 := bstep (se 1 (by rfl) ⟨9172277, by rfl⟩ : syracuseStep 12229703 = 18344555) B18344555
theorem B6135425 : Blo 714321 6135425 := bstep (se 2 (by rfl) ⟨2300784, by rfl⟩ : syracuseStep 6135425 = 4601569) B4601569
theorem B1613519 : Blo 714321 1613519 := bstep (se 1 (by rfl) ⟨1210139, by rfl⟩ : syracuseStep 1613519 = 2420279) B2420279
theorem B6102823 : Blo 714321 6102823 := bstep (se 1 (by rfl) ⟨4577117, by rfl⟩ : syracuseStep 6102823 = 9154235) B9154235
theorem B198877031 : Blo 714321 198877031 := bstep (se 1 (by rfl) ⟨149157773, by rfl⟩ : syracuseStep 198877031 = 298315547) B298315547
theorem B5152835 : Blo 714321 5152835 := bstep (se 1 (by rfl) ⟨3864626, by rfl⟩ : syracuseStep 5152835 = 7729253) B7729253
theorem B5515751 : Blo 714321 5515751 := bstep (se 1 (by rfl) ⟨4136813, by rfl⟩ : syracuseStep 5515751 = 8273627) B8273627
theorem B100576133 : Blo 714321 100576133 := bstep (se 4 (by rfl) ⟨9429012, by rfl⟩ : syracuseStep 100576133 = 18858025) B18858025
theorem B1813823 : Blo 714321 1813823 := bstep (se 1 (by rfl) ⟨1360367, by rfl⟩ : syracuseStep 1813823 = 2720735) B2720735
theorem B1031167 : Blo 714321 1031167 := bstep (se 1 (by rfl) ⟨773375, by rfl⟩ : syracuseStep 1031167 = 1546751) B1546751
theorem B3098159 : Blo 714321 3098159 := bstep (se 1 (by rfl) ⟨2323619, by rfl⟩ : syracuseStep 3098159 = 4647239) B4647239
theorem B2414015 : Blo 714321 2414015 := bstep (se 1 (by rfl) ⟨1810511, by rfl⟩ : syracuseStep 2414015 = 3621023) B3621023
theorem B10475639 : Blo 714321 10475639 := bstep (se 1 (by rfl) ⟨7856729, by rfl⟩ : syracuseStep 10475639 = 15713459) B15713459
theorem B1205435 : Blo 714321 1205435 := bstep (se 1 (by rfl) ⟨904076, by rfl⟩ : syracuseStep 1205435 = 1808153) B1808153
theorem B1074815 : Blo 714321 1074815 := bstep (se 1 (by rfl) ⟨806111, by rfl⟩ : syracuseStep 1074815 = 1612223) B1612223
theorem B715759 : Blo 714321 715759 := bstep (se 1 (by rfl) ⟨536819, by rfl⟩ : syracuseStep 715759 = 1073639) B1073639
theorem B2419739 : Blo 714321 2419739 := bstep (se 1 (by rfl) ⟨1814804, by rfl⟩ : syracuseStep 2419739 = 3629609) B3629609
theorem B716335 : Blo 714321 716335 := bstep (se 1 (by rfl) ⟨537251, by rfl⟩ : syracuseStep 716335 = 1074503) B1074503
theorem B716527 : Blo 714321 716527 := bstep (se 1 (by rfl) ⟨537395, by rfl⟩ : syracuseStep 716527 = 1074791) B1074791
theorem B2420603 : Blo 714321 2420603 := bstep (se 1 (by rfl) ⟨1815452, by rfl⟩ : syracuseStep 2420603 = 3630905) B3630905
theorem B11005865 : Blo 714321 11005865 := bstep (se 2 (by rfl) ⟨4127199, by rfl⟩ : syracuseStep 11005865 = 8254399) B8254399
theorem B717055 : Blo 714321 717055 := bstep (se 1 (by rfl) ⟨537791, by rfl⟩ : syracuseStep 717055 = 1075583) B1075583
theorem B1209343 : Blo 714321 1209343 := bstep (se 1 (by rfl) ⟨907007, by rfl⟩ : syracuseStep 1209343 = 1814015) B1814015
theorem B717983 : Blo 714321 717983 := bstep (se 1 (by rfl) ⟨538487, by rfl⟩ : syracuseStep 717983 = 1076975) B1076975
theorem B718287 : Blo 714321 718287 := bstep (se 1 (by rfl) ⟨538715, by rfl⟩ : syracuseStep 718287 = 1077431) B1077431
theorem B1210025 : Blo 714321 1210025 := bstep (se 2 (by rfl) ⟨453759, by rfl⟩ : syracuseStep 1210025 = 907519) B907519
theorem B1309375 : Blo 714321 1309375 := bstep (se 1 (by rfl) ⟨982031, by rfl⟩ : syracuseStep 1309375 = 1964063) B1964063
theorem B2718593 : Blo 714321 2718593 := bstep (se 2 (by rfl) ⟨1019472, by rfl⟩ : syracuseStep 2718593 = 2038945) B2038945
theorem B1211503 : Blo 714321 1211503 := bstep (se 1 (by rfl) ⟨908627, by rfl⟩ : syracuseStep 1211503 = 1817255) B1817255
theorem B10321121 : Blo 714321 10321121 := bstep (se 2 (by rfl) ⟨3870420, by rfl⟩ : syracuseStep 10321121 = 7740841) B7740841
theorem B4586807 : Blo 714321 4586807 := bstep (se 1 (by rfl) ⟨3440105, by rfl⟩ : syracuseStep 4586807 = 6880211) B6880211
theorem B2065439 : Blo 714321 2065439 := bstep (se 1 (by rfl) ⟨1549079, by rfl⟩ : syracuseStep 2065439 = 3098159) B3098159
theorem B7865483 : Blo 714321 7865483 := bstep (se 1 (by rfl) ⟨5899112, by rfl⟩ : syracuseStep 7865483 = 11798225) B11798225
theorem B3868519 : Blo 714321 3868519 := bstep (se 1 (by rfl) ⟨2901389, by rfl⟩ : syracuseStep 3868519 = 5802779) B5802779
theorem B29362115 : Blo 714321 29362115 := bstep (se 1 (by rfl) ⟨22021586, by rfl⟩ : syracuseStep 29362115 = 44043173) B44043173
theorem B3868735 : Blo 714321 3868735 := bstep (se 1 (by rfl) ⟨2901551, by rfl⟩ : syracuseStep 3868735 = 5803103) B5803103
theorem B1609343 : Blo 714321 1609343 := bstep (se 1 (by rfl) ⟨1207007, by rfl⟩ : syracuseStep 1609343 = 2414015) B2414015
theorem B6983333 : Blo 714321 6983333 := bstep (se 4 (by rfl) ⟨654687, by rfl⟩ : syracuseStep 6983333 = 1309375) B1309375
theorem B6983759 : Blo 714321 6983759 := bstep (se 1 (by rfl) ⟨5237819, by rfl⟩ : syracuseStep 6983759 = 10475639) B10475639
theorem B132584687 : Blo 714321 132584687 := bstep (se 1 (by rfl) ⟨99438515, by rfl⟩ : syracuseStep 132584687 = 198877031) B198877031
theorem B3676553 : Blo 714321 3676553 := bstep (se 2 (by rfl) ⟨1378707, by rfl⟩ : syracuseStep 3676553 = 2757415) B2757415
theorem B1612457 : Blo 714321 1612457 := bstep (se 2 (by rfl) ⟨604671, by rfl⟩ : syracuseStep 1612457 = 1209343) B1209343
theorem B3677167 : Blo 714321 3677167 := bstep (se 1 (by rfl) ⟨2757875, by rfl⟩ : syracuseStep 3677167 = 5515751) B5515751
theorem B67050755 : Blo 714321 67050755 := bstep (se 1 (by rfl) ⟨50288066, by rfl⟩ : syracuseStep 67050755 = 100576133) B100576133
theorem B1613159 : Blo 714321 1613159 := bstep (se 1 (by rfl) ⟨1209869, by rfl⟩ : syracuseStep 1613159 = 2419739) B2419739
theorem B1613735 : Blo 714321 1613735 := bstep (se 1 (by rfl) ⟨1210301, by rfl⟩ : syracuseStep 1613735 = 2420603) B2420603
theorem B1615337 : Blo 714321 1615337 := bstep (se 2 (by rfl) ⟨605751, by rfl⟩ : syracuseStep 1615337 = 1211503) B1211503
theorem B1812395 : Blo 714321 1812395 := bstep (se 1 (by rfl) ⟨1359296, by rfl⟩ : syracuseStep 1812395 = 2718593) B2718593
theorem B3057871 : Blo 714321 3057871 := bstep (se 1 (by rfl) ⟨2293403, by rfl⟩ : syracuseStep 3057871 = 4586807) B4586807
theorem B8137097 : Blo 714321 8137097 := bstep (se 2 (by rfl) ⟨3051411, by rfl⟩ : syracuseStep 8137097 = 6102823) B6102823
theorem B1817599 : Blo 714321 1817599 := bstep (se 1 (by rfl) ⟨1363199, by rfl⟩ : syracuseStep 1817599 = 2726399) B2726399
theorem B803623 : Blo 714321 803623 := bstep (se 1 (by rfl) ⟨602717, by rfl⟩ : syracuseStep 803623 = 1205435) B1205435
theorem B806683 : Blo 714321 806683 := bstep (se 1 (by rfl) ⟨605012, by rfl⟩ : syracuseStep 806683 = 1210025) B1210025
theorem B106128353 : Blo 714321 106128353 := bstep (se 2 (by rfl) ⟨39798132, by rfl⟩ : syracuseStep 106128353 = 79596265) B79596265
theorem B1074599 : Blo 714321 1074599 := bstep (se 1 (by rfl) ⟨805949, by rfl⟩ : syracuseStep 1074599 = 1611899) B1611899
theorem B8153135 : Blo 714321 8153135 := bstep (se 1 (by rfl) ⟨6114851, by rfl⟩ : syracuseStep 8153135 = 12229703) B12229703
theorem B4090283 : Blo 714321 4090283 := bstep (se 1 (by rfl) ⟨3067712, by rfl⟩ : syracuseStep 4090283 = 6135425) B6135425
theorem B1075679 : Blo 714321 1075679 := bstep (se 1 (by rfl) ⟨806759, by rfl⟩ : syracuseStep 1075679 = 1613519) B1613519
theorem B3435223 : Blo 714321 3435223 := bstep (se 1 (by rfl) ⟨2576417, by rfl⟩ : syracuseStep 3435223 = 5152835) B5152835
theorem B716543 : Blo 714321 716543 := bstep (se 1 (by rfl) ⟨537407, by rfl⟩ : syracuseStep 716543 = 1074815) B1074815
theorem B1209215 : Blo 714321 1209215 := bstep (se 1 (by rfl) ⟨906911, by rfl⟩ : syracuseStep 1209215 = 1813823) B1813823
theorem B7337243 : Blo 714321 7337243 := bstep (se 1 (by rfl) ⟨5502932, by rfl⟩ : syracuseStep 7337243 = 11005865) B11005865
theorem B1374889 : Blo 714321 1374889 := bstep (se 2 (by rfl) ⟨515583, by rfl⟩ : syracuseStep 1374889 = 1031167) B1031167
theorem B6880747 : Blo 714321 6880747 := bstep (se 1 (by rfl) ⟨5160560, by rfl⟩ : syracuseStep 6880747 = 10321121) B10321121
theorem B4655555 : Blo 714321 4655555 := bstep (se 1 (by rfl) ⟨3491666, by rfl⟩ : syracuseStep 4655555 = 6983333) B6983333
theorem B4655839 : Blo 714321 4655839 := bstep (se 1 (by rfl) ⟨3491879, by rfl⟩ : syracuseStep 4655839 = 6983759) B6983759
theorem B5507837 : Blo 714321 5507837 := bstep (se 3 (by rfl) ⟨1032719, by rfl⟩ : syracuseStep 5507837 = 2065439) B2065439
theorem B20974621 : Blo 714321 20974621 := bstep (se 3 (by rfl) ⟨3932741, by rfl⟩ : syracuseStep 20974621 = 7865483) B7865483
theorem B19565981 : Blo 714321 19565981 := bstep (se 3 (by rfl) ⟨3668621, by rfl⟩ : syracuseStep 19565981 = 7337243) B7337243
theorem B44700503 : Blo 714321 44700503 := bstep (se 1 (by rfl) ⟨33525377, by rfl⟩ : syracuseStep 44700503 = 67050755) B67050755
theorem B2726855 : Blo 714321 2726855 := bstep (se 1 (by rfl) ⟨2045141, by rfl⟩ : syracuseStep 2726855 = 4090283) B4090283
theorem B5158025 : Blo 714321 5158025 := bstep (se 2 (by rfl) ⟨1934259, by rfl⟩ : syracuseStep 5158025 = 3868519) B3868519
theorem B5158313 : Blo 714321 5158313 := bstep (se 2 (by rfl) ⟨1934367, by rfl⟩ : syracuseStep 5158313 = 3868735) B3868735
theorem B4077161 : Blo 714321 4077161 := bstep (se 2 (by rfl) ⟨1528935, by rfl⟩ : syracuseStep 4077161 = 3057871) B3057871
theorem B88389791 : Blo 714321 88389791 := bstep (se 1 (by rfl) ⟨66292343, by rfl⟩ : syracuseStep 88389791 = 132584687) B132584687
theorem B78298973 : Blo 714321 78298973 := bstep (se 3 (by rfl) ⟨14681057, by rfl⟩ : syracuseStep 78298973 = 29362115) B29362115
theorem B5424731 : Blo 714321 5424731 := bstep (se 1 (by rfl) ⟨4068548, by rfl⟩ : syracuseStep 5424731 = 8137097) B8137097
theorem B806143 : Blo 714321 806143 := bstep (se 1 (by rfl) ⟨604607, by rfl⟩ : syracuseStep 806143 = 1209215) B1209215
theorem B4902889 : Blo 714321 4902889 := bstep (se 2 (by rfl) ⟨1838583, by rfl⟩ : syracuseStep 4902889 = 3677167) B3677167
theorem B1071497 : Blo 714321 1071497 := bstep (se 2 (by rfl) ⟨401811, by rfl⟩ : syracuseStep 1071497 = 803623) B803623
theorem B1072895 : Blo 714321 1072895 := bstep (se 1 (by rfl) ⟨804671, by rfl⟩ : syracuseStep 1072895 = 1609343) B1609343
theorem B283008941 : Blo 714321 283008941 := bstep (se 3 (by rfl) ⟨53064176, by rfl⟩ : syracuseStep 283008941 = 106128353) B106128353
theorem B4580297 : Blo 714321 4580297 := bstep (se 2 (by rfl) ⟨1717611, by rfl⟩ : syracuseStep 4580297 = 3435223) B3435223
theorem B2451035 : Blo 714321 2451035 := bstep (se 1 (by rfl) ⟨1838276, by rfl⟩ : syracuseStep 2451035 = 3676553) B3676553
theorem B1074971 : Blo 714321 1074971 := bstep (se 1 (by rfl) ⟨806228, by rfl⟩ : syracuseStep 1074971 = 1612457) B1612457
theorem B1075439 : Blo 714321 1075439 := bstep (se 1 (by rfl) ⟨806579, by rfl⟩ : syracuseStep 1075439 = 1613159) B1613159
theorem B1075577 : Blo 714321 1075577 := bstep (se 2 (by rfl) ⟨403341, by rfl⟩ : syracuseStep 1075577 = 806683) B806683
theorem B1075823 : Blo 714321 1075823 := bstep (se 1 (by rfl) ⟨806867, by rfl⟩ : syracuseStep 1075823 = 1613735) B1613735
theorem B716399 : Blo 714321 716399 := bstep (se 1 (by rfl) ⟨537299, by rfl⟩ : syracuseStep 716399 = 1074599) B1074599
theorem B1076891 : Blo 714321 1076891 := bstep (se 1 (by rfl) ⟨807668, by rfl⟩ : syracuseStep 1076891 = 1615337) B1615337
theorem B1208263 : Blo 714321 1208263 := bstep (se 1 (by rfl) ⟨906197, by rfl⟩ : syracuseStep 1208263 = 1812395) B1812395
theorem B5435423 : Blo 714321 5435423 := bstep (se 1 (by rfl) ⟨4076567, by rfl⟩ : syracuseStep 5435423 = 8153135) B8153135
theorem B717119 : Blo 714321 717119 := bstep (se 1 (by rfl) ⟨537839, by rfl⟩ : syracuseStep 717119 = 1075679) B1075679
theorem B1833185 : Blo 714321 1833185 := bstep (se 2 (by rfl) ⟨687444, by rfl⟩ : syracuseStep 1833185 = 1374889) B1374889
theorem B2423465 : Blo 714321 2423465 := bstep (se 2 (by rfl) ⟨908799, by rfl⟩ : syracuseStep 2423465 = 1817599) B1817599
theorem B9174329 : Blo 714321 9174329 := bstep (se 2 (by rfl) ⟨3440373, by rfl⟩ : syracuseStep 9174329 = 6880747) B6880747
theorem B3671891 : Blo 714321 3671891 := bstep (se 1 (by rfl) ⟨2753918, by rfl⟩ : syracuseStep 3671891 = 5507837) B5507837
theorem B13043987 : Blo 714321 13043987 := bstep (se 1 (by rfl) ⟨9782990, by rfl⟩ : syracuseStep 13043987 = 19565981) B19565981
theorem B1611017 : Blo 714321 1611017 := bstep (se 2 (by rfl) ⟨604131, by rfl⟩ : syracuseStep 1611017 = 1208263) B1208263
theorem B3053531 : Blo 714321 3053531 := bstep (se 1 (by rfl) ⟨2290148, by rfl⟩ : syracuseStep 3053531 = 4580297) B4580297
theorem B58926527 : Blo 714321 58926527 := bstep (se 1 (by rfl) ⟨44194895, by rfl⟩ : syracuseStep 58926527 = 88389791) B88389791
theorem B1222123 : Blo 714321 1222123 := bstep (se 1 (by rfl) ⟨916592, by rfl⟩ : syracuseStep 1222123 = 1833185) B1833185
theorem B1615643 : Blo 714321 1615643 := bstep (se 1 (by rfl) ⟨1211732, by rfl⟩ : syracuseStep 1615643 = 2423465) B2423465
theorem B3616487 : Blo 714321 3616487 := bstep (se 1 (by rfl) ⟨2712365, by rfl⟩ : syracuseStep 3616487 = 5424731) B5424731
theorem B6207785 : Blo 714321 6207785 := bstep (se 2 (by rfl) ⟨2327919, by rfl⟩ : syracuseStep 6207785 = 4655839) B4655839
theorem B27966161 : Blo 714321 27966161 := bstep (se 2 (by rfl) ⟨10487310, by rfl⟩ : syracuseStep 27966161 = 20974621) B20974621
theorem B1817903 : Blo 714321 1817903 := bstep (se 1 (by rfl) ⟨1363427, by rfl⟩ : syracuseStep 1817903 = 2726855) B2726855
theorem B6537185 : Blo 714321 6537185 := bstep (se 2 (by rfl) ⟨2451444, by rfl⟩ : syracuseStep 6537185 = 4902889) B4902889
theorem B3623615 : Blo 714321 3623615 := bstep (se 1 (by rfl) ⟨2717711, by rfl⟩ : syracuseStep 3623615 = 5435423) B5435423
theorem B6116219 : Blo 714321 6116219 := bstep (se 1 (by rfl) ⟨4587164, by rfl⟩ : syracuseStep 6116219 = 9174329) B9174329
theorem B3103703 : Blo 714321 3103703 := bstep (se 1 (by rfl) ⟨2327777, by rfl⟩ : syracuseStep 3103703 = 4655555) B4655555
theorem B119201341 : Blo 714321 119201341 := bstep (se 3 (by rfl) ⟨22350251, by rfl⟩ : syracuseStep 119201341 = 44700503) B44700503
theorem B714331 : Blo 714321 714331 := bstep (se 1 (by rfl) ⟨535748, by rfl⟩ : syracuseStep 714331 = 1071497) B1071497
theorem B1074857 : Blo 714321 1074857 := bstep (se 2 (by rfl) ⟨403071, by rfl⟩ : syracuseStep 1074857 = 806143) B806143
theorem B715263 : Blo 714321 715263 := bstep (se 1 (by rfl) ⟨536447, by rfl⟩ : syracuseStep 715263 = 1072895) B1072895
theorem B188672627 : Blo 714321 188672627 := bstep (se 1 (by rfl) ⟨141504470, by rfl⟩ : syracuseStep 188672627 = 283008941) B283008941
theorem B1634023 : Blo 714321 1634023 := bstep (se 1 (by rfl) ⟨1225517, by rfl⟩ : syracuseStep 1634023 = 2451035) B2451035
theorem B716647 : Blo 714321 716647 := bstep (se 1 (by rfl) ⟨537485, by rfl⟩ : syracuseStep 716647 = 1074971) B1074971
theorem B716959 : Blo 714321 716959 := bstep (se 1 (by rfl) ⟨537719, by rfl⟩ : syracuseStep 716959 = 1075439) B1075439
theorem B717051 : Blo 714321 717051 := bstep (se 1 (by rfl) ⟨537788, by rfl⟩ : syracuseStep 717051 = 1075577) B1075577
theorem B717215 : Blo 714321 717215 := bstep (se 1 (by rfl) ⟨537911, by rfl⟩ : syracuseStep 717215 = 1075823) B1075823
theorem B717927 : Blo 714321 717927 := bstep (se 1 (by rfl) ⟨538445, by rfl⟩ : syracuseStep 717927 = 1076891) B1076891
theorem B3438683 : Blo 714321 3438683 := bstep (se 1 (by rfl) ⟨2579012, by rfl⟩ : syracuseStep 3438683 = 5158025) B5158025
theorem B3438875 : Blo 714321 3438875 := bstep (se 1 (by rfl) ⟨2579156, by rfl⟩ : syracuseStep 3438875 = 5158313) B5158313
theorem B2718107 : Blo 714321 2718107 := bstep (se 1 (by rfl) ⟨2038580, by rfl⟩ : syracuseStep 2718107 = 4077161) B4077161
theorem B52199315 : Blo 714321 52199315 := bstep (se 1 (by rfl) ⟨39149486, by rfl⟩ : syracuseStep 52199315 = 78298973) B78298973
theorem B2035687 : Blo 714321 2035687 := bstep (se 1 (by rfl) ⟨1526765, by rfl⟩ : syracuseStep 2035687 = 3053531) B3053531
theorem B2069135 : Blo 714321 2069135 := bstep (se 1 (by rfl) ⟨1551851, by rfl⟩ : syracuseStep 2069135 = 3103703) B3103703
theorem B4138523 : Blo 714321 4138523 := bstep (se 1 (by rfl) ⟨3103892, by rfl⟩ : syracuseStep 4138523 = 6207785) B6207785
theorem B1812071 : Blo 714321 1812071 := bstep (se 1 (by rfl) ⟨1359053, by rfl⟩ : syracuseStep 1812071 = 2718107) B2718107
theorem B158935121 : Blo 714321 158935121 := bstep (se 2 (by rfl) ⟨59600670, by rfl⟩ : syracuseStep 158935121 = 119201341) B119201341
theorem B8695991 : Blo 714321 8695991 := bstep (se 1 (by rfl) ⟨6521993, by rfl⟩ : syracuseStep 8695991 = 13043987) B13043987
theorem B4077479 : Blo 714321 4077479 := bstep (se 1 (by rfl) ⟨3058109, by rfl⟩ : syracuseStep 4077479 = 6116219) B6116219
theorem B2178697 : Blo 714321 2178697 := bstep (se 2 (by rfl) ⟨817011, by rfl⟩ : syracuseStep 2178697 = 1634023) B1634023
theorem B125781751 : Blo 714321 125781751 := bstep (se 1 (by rfl) ⟨94336313, by rfl⟩ : syracuseStep 125781751 = 188672627) B188672627
theorem B2410991 : Blo 714321 2410991 := bstep (se 1 (by rfl) ⟨1808243, by rfl⟩ : syracuseStep 2410991 = 3616487) B3616487
theorem B2447927 : Blo 714321 2447927 := bstep (se 1 (by rfl) ⟨1835945, by rfl⟩ : syracuseStep 2447927 = 3671891) B3671891
theorem B2415743 : Blo 714321 2415743 := bstep (se 1 (by rfl) ⟨1811807, by rfl⟩ : syracuseStep 2415743 = 3623615) B3623615
theorem B1629497 : Blo 714321 1629497 := bstep (se 2 (by rfl) ⟨611061, by rfl⟩ : syracuseStep 1629497 = 1222123) B1222123
theorem B1074011 : Blo 714321 1074011 := bstep (se 1 (by rfl) ⟨805508, by rfl⟩ : syracuseStep 1074011 = 1611017) B1611017
theorem B9170333 : Blo 714321 9170333 := bstep (se 3 (by rfl) ⟨1719437, by rfl⟩ : syracuseStep 9170333 = 3438875) B3438875
theorem B39284351 : Blo 714321 39284351 := bstep (se 1 (by rfl) ⟨29463263, by rfl⟩ : syracuseStep 39284351 = 58926527) B58926527
theorem B716571 : Blo 714321 716571 := bstep (se 1 (by rfl) ⟨537428, by rfl⟩ : syracuseStep 716571 = 1074857) B1074857
theorem B1077095 : Blo 714321 1077095 := bstep (se 1 (by rfl) ⟨807821, by rfl⟩ : syracuseStep 1077095 = 1615643) B1615643
theorem B2292455 : Blo 714321 2292455 := bstep (se 1 (by rfl) ⟨1719341, by rfl⟩ : syracuseStep 2292455 = 3438683) B3438683
theorem B18644107 : Blo 714321 18644107 := bstep (se 1 (by rfl) ⟨13983080, by rfl⟩ : syracuseStep 18644107 = 27966161) B27966161
theorem B1211935 : Blo 714321 1211935 := bstep (se 1 (by rfl) ⟨908951, by rfl⟩ : syracuseStep 1211935 = 1817903) B1817903
theorem B34799543 : Blo 714321 34799543 := bstep (se 1 (by rfl) ⟨26099657, by rfl⟩ : syracuseStep 34799543 = 52199315) B52199315
theorem B4358123 : Blo 714321 4358123 := bstep (se 1 (by rfl) ⟨3268592, by rfl⟩ : syracuseStep 4358123 = 6537185) B6537185
theorem B1607327 : Blo 714321 1607327 := bstep (se 1 (by rfl) ⟨1205495, by rfl⟩ : syracuseStep 1607327 = 2410991) B2410991
theorem B167709001 : Blo 714321 167709001 := bstep (se 2 (by rfl) ⟨62890875, by rfl⟩ : syracuseStep 167709001 = 125781751) B125781751
theorem B1379423 : Blo 714321 1379423 := bstep (se 1 (by rfl) ⟨1034567, by rfl⟩ : syracuseStep 1379423 = 2069135) B2069135
theorem B1610495 : Blo 714321 1610495 := bstep (se 1 (by rfl) ⟨1207871, by rfl⟩ : syracuseStep 1610495 = 2415743) B2415743
theorem B2759015 : Blo 714321 2759015 := bstep (se 1 (by rfl) ⟨2069261, by rfl⟩ : syracuseStep 2759015 = 4138523) B4138523
theorem B26189567 : Blo 714321 26189567 := bstep (se 1 (by rfl) ⟨19642175, by rfl⟩ : syracuseStep 26189567 = 39284351) B39284351
theorem B1615913 : Blo 714321 1615913 := bstep (se 2 (by rfl) ⟨605967, by rfl⟩ : syracuseStep 1615913 = 1211935) B1211935
theorem B105956747 : Blo 714321 105956747 := bstep (se 1 (by rfl) ⟨79467560, by rfl⟩ : syracuseStep 105956747 = 158935121) B158935121
theorem B6113555 : Blo 714321 6113555 := bstep (se 1 (by rfl) ⟨4585166, by rfl⟩ : syracuseStep 6113555 = 9170333) B9170333
theorem B4345325 : Blo 714321 4345325 := bstep (se 3 (by rfl) ⟨814748, by rfl⟩ : syracuseStep 4345325 = 1629497) B1629497
theorem B24858809 : Blo 714321 24858809 := bstep (se 2 (by rfl) ⟨9322053, by rfl⟩ : syracuseStep 24858809 = 18644107) B18644107
theorem B1528303 : Blo 714321 1528303 := bstep (se 1 (by rfl) ⟨1146227, by rfl⟩ : syracuseStep 1528303 = 2292455) B2292455
theorem B2904929 : Blo 714321 2904929 := bstep (se 2 (by rfl) ⟨1089348, by rfl⟩ : syracuseStep 2904929 = 2178697) B2178697
theorem B2905415 : Blo 714321 2905415 := bstep (se 1 (by rfl) ⟨2179061, by rfl⟩ : syracuseStep 2905415 = 4358123) B4358123
theorem B1631951 : Blo 714321 1631951 := bstep (se 1 (by rfl) ⟨1223963, by rfl⟩ : syracuseStep 1631951 = 2447927) B2447927
theorem B2714249 : Blo 714321 2714249 := bstep (se 2 (by rfl) ⟨1017843, by rfl⟩ : syracuseStep 2714249 = 2035687) B2035687
theorem B716007 : Blo 714321 716007 := bstep (se 1 (by rfl) ⟨537005, by rfl⟩ : syracuseStep 716007 = 1074011) B1074011
theorem B1208047 : Blo 714321 1208047 := bstep (se 1 (by rfl) ⟨906035, by rfl⟩ : syracuseStep 1208047 = 1812071) B1812071
theorem B718063 : Blo 714321 718063 := bstep (se 1 (by rfl) ⟨538547, by rfl⟩ : syracuseStep 718063 = 1077095) B1077095
theorem B5797327 : Blo 714321 5797327 := bstep (se 1 (by rfl) ⟨4347995, by rfl⟩ : syracuseStep 5797327 = 8695991) B8695991
theorem B2718319 : Blo 714321 2718319 := bstep (se 1 (by rfl) ⟨2038739, by rfl⟩ : syracuseStep 2718319 = 4077479) B4077479
theorem B23199695 : Blo 714321 23199695 := bstep (se 1 (by rfl) ⟨17399771, by rfl⟩ : syracuseStep 23199695 = 34799543) B34799543
theorem B919615 : Blo 714321 919615 := bstep (se 1 (by rfl) ⟨689711, by rfl⟩ : syracuseStep 919615 = 1379423) B1379423
theorem B223612001 : Blo 714321 223612001 := bstep (se 2 (by rfl) ⟨83854500, by rfl⟩ : syracuseStep 223612001 = 167709001) B167709001
theorem B1936619 : Blo 714321 1936619 := bstep (se 1 (by rfl) ⟨1452464, by rfl⟩ : syracuseStep 1936619 = 2904929) B2904929
theorem B1936943 : Blo 714321 1936943 := bstep (se 1 (by rfl) ⟨1452707, by rfl⟩ : syracuseStep 1936943 = 2905415) B2905415
theorem B1839343 : Blo 714321 1839343 := bstep (se 1 (by rfl) ⟨1379507, by rfl⟩ : syracuseStep 1839343 = 2759015) B2759015
theorem B1610729 : Blo 714321 1610729 := bstep (se 2 (by rfl) ⟨604023, by rfl⟩ : syracuseStep 1610729 = 1208047) B1208047
theorem B2037737 : Blo 714321 2037737 := bstep (se 2 (by rfl) ⟨764151, by rfl⟩ : syracuseStep 2037737 = 1528303) B1528303
theorem B1087967 : Blo 714321 1087967 := bstep (se 1 (by rfl) ⟨815975, by rfl⟩ : syracuseStep 1087967 = 1631951) B1631951
theorem B1809499 : Blo 714321 1809499 := bstep (se 1 (by rfl) ⟨1357124, by rfl⟩ : syracuseStep 1809499 = 2714249) B2714249
theorem B4075703 : Blo 714321 4075703 := bstep (se 1 (by rfl) ⟨3056777, by rfl⟩ : syracuseStep 4075703 = 6113555) B6113555
theorem B2896883 : Blo 714321 2896883 := bstep (se 1 (by rfl) ⟨2172662, by rfl⟩ : syracuseStep 2896883 = 4345325) B4345325
theorem B3624425 : Blo 714321 3624425 := bstep (se 2 (by rfl) ⟨1359159, by rfl⟩ : syracuseStep 3624425 = 2718319) B2718319
theorem B70637831 : Blo 714321 70637831 := bstep (se 1 (by rfl) ⟨52978373, by rfl⟩ : syracuseStep 70637831 = 105956747) B105956747
theorem B1071551 : Blo 714321 1071551 := bstep (se 1 (by rfl) ⟨803663, by rfl⟩ : syracuseStep 1071551 = 1607327) B1607327
theorem B16572539 : Blo 714321 16572539 := bstep (se 1 (by rfl) ⟨12429404, by rfl⟩ : syracuseStep 16572539 = 24858809) B24858809
theorem B1073663 : Blo 714321 1073663 := bstep (se 1 (by rfl) ⟨805247, by rfl⟩ : syracuseStep 1073663 = 1610495) B1610495
theorem B17459711 : Blo 714321 17459711 := bstep (se 1 (by rfl) ⟨13094783, by rfl⟩ : syracuseStep 17459711 = 26189567) B26189567
theorem B1077275 : Blo 714321 1077275 := bstep (se 1 (by rfl) ⟨807956, by rfl⟩ : syracuseStep 1077275 = 1615913) B1615913
theorem B7729769 : Blo 714321 7729769 := bstep (se 2 (by rfl) ⟨2898663, by rfl⟩ : syracuseStep 7729769 = 5797327) B5797327
theorem B15466463 : Blo 714321 15466463 := bstep (se 1 (by rfl) ⟨11599847, by rfl⟩ : syracuseStep 15466463 = 23199695) B23199695
theorem B20612717 : Blo 714321 20612717 := bstep (se 3 (by rfl) ⟨3864884, by rfl⟩ : syracuseStep 20612717 = 7729769) B7729769
theorem B47091887 : Blo 714321 47091887 := bstep (se 1 (by rfl) ⟨35318915, by rfl⟩ : syracuseStep 47091887 = 70637831) B70637831
theorem B725311 : Blo 714321 725311 := bstep (se 1 (by rfl) ⟨543983, by rfl⟩ : syracuseStep 725311 = 1087967) B1087967
theorem B11048359 : Blo 714321 11048359 := bstep (se 1 (by rfl) ⟨8286269, by rfl⟩ : syracuseStep 11048359 = 16572539) B16572539
theorem B11639807 : Blo 714321 11639807 := bstep (se 1 (by rfl) ⟨8729855, by rfl⟩ : syracuseStep 11639807 = 17459711) B17459711
theorem B149074667 : Blo 714321 149074667 := bstep (se 1 (by rfl) ⟨111806000, by rfl⟩ : syracuseStep 149074667 = 223612001) B223612001
theorem B1291079 : Blo 714321 1291079 := bstep (se 1 (by rfl) ⟨968309, by rfl⟩ : syracuseStep 1291079 = 1936619) B1936619
theorem B1291295 : Blo 714321 1291295 := bstep (se 1 (by rfl) ⟨968471, by rfl⟩ : syracuseStep 1291295 = 1936943) B1936943
theorem B1226153 : Blo 714321 1226153 := bstep (se 2 (by rfl) ⟨459807, by rfl⟩ : syracuseStep 1226153 = 919615) B919615
theorem B2412665 : Blo 714321 2412665 := bstep (se 2 (by rfl) ⟨904749, by rfl⟩ : syracuseStep 2412665 = 1809499) B1809499
theorem B10310975 : Blo 714321 10310975 := bstep (se 1 (by rfl) ⟨7733231, by rfl⟩ : syracuseStep 10310975 = 15466463) B15466463
theorem B2416283 : Blo 714321 2416283 := bstep (se 1 (by rfl) ⟨1812212, by rfl⟩ : syracuseStep 2416283 = 3624425) B3624425
theorem B1073819 : Blo 714321 1073819 := bstep (se 1 (by rfl) ⟨805364, by rfl⟩ : syracuseStep 1073819 = 1610729) B1610729
theorem B714367 : Blo 714321 714367 := bstep (se 1 (by rfl) ⟨535775, by rfl⟩ : syracuseStep 714367 = 1071551) B1071551
theorem B5433965 : Blo 714321 5433965 := bstep (se 3 (by rfl) ⟨1018868, by rfl⟩ : syracuseStep 5433965 = 2037737) B2037737
theorem B2452457 : Blo 714321 2452457 := bstep (se 2 (by rfl) ⟨919671, by rfl⟩ : syracuseStep 2452457 = 1839343) B1839343
theorem B715775 : Blo 714321 715775 := bstep (se 1 (by rfl) ⟨536831, by rfl⟩ : syracuseStep 715775 = 1073663) B1073663
theorem B718183 : Blo 714321 718183 := bstep (se 1 (by rfl) ⟨538637, by rfl⟩ : syracuseStep 718183 = 1077275) B1077275
theorem B2717135 : Blo 714321 2717135 := bstep (se 1 (by rfl) ⟨2037851, by rfl⟩ : syracuseStep 2717135 = 4075703) B4075703
theorem B1931255 : Blo 714321 1931255 := bstep (se 1 (by rfl) ⟨1448441, by rfl⟩ : syracuseStep 1931255 = 2896883) B2896883
theorem B3868325 : Blo 714321 3868325 := bstep (se 4 (by rfl) ⟨362655, by rfl⟩ : syracuseStep 3868325 = 725311) B725311
theorem B1608443 : Blo 714321 1608443 := bstep (se 1 (by rfl) ⟨1206332, by rfl⟩ : syracuseStep 1608443 = 2412665) B2412665
theorem B31394591 : Blo 714321 31394591 := bstep (se 1 (by rfl) ⟨23545943, by rfl⟩ : syracuseStep 31394591 = 47091887) B47091887
theorem B1610855 : Blo 714321 1610855 := bstep (se 1 (by rfl) ⟨1208141, by rfl⟩ : syracuseStep 1610855 = 2416283) B2416283
theorem B860719 : Blo 714321 860719 := bstep (se 1 (by rfl) ⟨645539, by rfl⟩ : syracuseStep 860719 = 1291079) B1291079
theorem B860863 : Blo 714321 860863 := bstep (se 1 (by rfl) ⟨645647, by rfl⟩ : syracuseStep 860863 = 1291295) B1291295
theorem B1811423 : Blo 714321 1811423 := bstep (se 1 (by rfl) ⟨1358567, by rfl⟩ : syracuseStep 1811423 = 2717135) B2717135
theorem B1287503 : Blo 714321 1287503 := bstep (se 1 (by rfl) ⟨965627, by rfl⟩ : syracuseStep 1287503 = 1931255) B1931255
theorem B13741811 : Blo 714321 13741811 := bstep (se 1 (by rfl) ⟨10306358, by rfl⟩ : syracuseStep 13741811 = 20612717) B20612717
theorem B3622643 : Blo 714321 3622643 := bstep (se 1 (by rfl) ⟨2716982, by rfl⟩ : syracuseStep 3622643 = 5433965) B5433965
theorem B14731145 : Blo 714321 14731145 := bstep (se 2 (by rfl) ⟨5524179, by rfl⟩ : syracuseStep 14731145 = 11048359) B11048359
theorem B6873983 : Blo 714321 6873983 := bstep (se 1 (by rfl) ⟨5155487, by rfl⟩ : syracuseStep 6873983 = 10310975) B10310975
theorem B7759871 : Blo 714321 7759871 := bstep (se 1 (by rfl) ⟨5819903, by rfl⟩ : syracuseStep 7759871 = 11639807) B11639807
theorem B715879 : Blo 714321 715879 := bstep (se 1 (by rfl) ⟨536909, by rfl⟩ : syracuseStep 715879 = 1073819) B1073819
theorem B1634971 : Blo 714321 1634971 := bstep (se 1 (by rfl) ⟨1226228, by rfl⟩ : syracuseStep 1634971 = 2452457) B2452457
theorem B99383111 : Blo 714321 99383111 := bstep (se 1 (by rfl) ⟨74537333, by rfl⟩ : syracuseStep 99383111 = 149074667) B149074667
theorem B817435 : Blo 714321 817435 := bstep (se 1 (by rfl) ⟨613076, by rfl⟩ : syracuseStep 817435 = 1226153) B1226153
theorem B1147625 : Blo 714321 1147625 := bstep (se 2 (by rfl) ⟨430359, by rfl⟩ : syracuseStep 1147625 = 860719) B860719
theorem B1147817 : Blo 714321 1147817 := bstep (se 2 (by rfl) ⟨430431, by rfl⟩ : syracuseStep 1147817 = 860863) B860863
theorem B4359653 : Blo 714321 4359653 := bstep (se 4 (by rfl) ⟨408717, by rfl⟩ : syracuseStep 4359653 = 817435) B817435
theorem B858335 : Blo 714321 858335 := bstep (se 1 (by rfl) ⟨643751, by rfl⟩ : syracuseStep 858335 = 1287503) B1287503
theorem B2179961 : Blo 714321 2179961 := bstep (se 2 (by rfl) ⟨817485, by rfl⟩ : syracuseStep 2179961 = 1634971) B1634971
theorem B9161207 : Blo 714321 9161207 := bstep (se 1 (by rfl) ⟨6870905, by rfl⟩ : syracuseStep 9161207 = 13741811) B13741811
theorem B2578883 : Blo 714321 2578883 := bstep (se 1 (by rfl) ⟨1934162, by rfl⟩ : syracuseStep 2578883 = 3868325) B3868325
theorem B2415095 : Blo 714321 2415095 := bstep (se 1 (by rfl) ⟨1811321, by rfl⟩ : syracuseStep 2415095 = 3622643) B3622643
theorem B9820763 : Blo 714321 9820763 := bstep (se 1 (by rfl) ⟨7365572, by rfl⟩ : syracuseStep 9820763 = 14731145) B14731145
theorem B1072295 : Blo 714321 1072295 := bstep (se 1 (by rfl) ⟨804221, by rfl⟩ : syracuseStep 1072295 = 1608443) B1608443
theorem B20929727 : Blo 714321 20929727 := bstep (se 1 (by rfl) ⟨15697295, by rfl⟩ : syracuseStep 20929727 = 31394591) B31394591
theorem B1073903 : Blo 714321 1073903 := bstep (se 1 (by rfl) ⟨805427, by rfl⟩ : syracuseStep 1073903 = 1610855) B1610855
theorem B4582655 : Blo 714321 4582655 := bstep (se 1 (by rfl) ⟨3436991, by rfl⟩ : syracuseStep 4582655 = 6873983) B6873983
theorem B1207615 : Blo 714321 1207615 := bstep (se 1 (by rfl) ⟨905711, by rfl⟩ : syracuseStep 1207615 = 1811423) B1811423
theorem B5173247 : Blo 714321 5173247 := bstep (se 1 (by rfl) ⟨3879935, by rfl⟩ : syracuseStep 5173247 = 7759871) B7759871
theorem B66255407 : Blo 714321 66255407 := bstep (se 1 (by rfl) ⟨49691555, by rfl⟩ : syracuseStep 66255407 = 99383111) B99383111
theorem B1610063 : Blo 714321 1610063 := bstep (se 1 (by rfl) ⟨1207547, by rfl⟩ : syracuseStep 1610063 = 2415095) B2415095
theorem B1610153 : Blo 714321 1610153 := bstep (se 2 (by rfl) ⟨603807, by rfl⟩ : syracuseStep 1610153 = 1207615) B1207615
theorem B3055103 : Blo 714321 3055103 := bstep (se 1 (by rfl) ⟨2291327, by rfl⟩ : syracuseStep 3055103 = 4582655) B4582655
theorem B3448831 : Blo 714321 3448831 := bstep (se 1 (by rfl) ⟨2586623, by rfl⟩ : syracuseStep 3448831 = 5173247) B5173247
theorem B765083 : Blo 714321 765083 := bstep (se 1 (by rfl) ⟨573812, by rfl⟩ : syracuseStep 765083 = 1147625) B1147625
theorem B1453307 : Blo 714321 1453307 := bstep (se 1 (by rfl) ⟨1089980, by rfl⟩ : syracuseStep 1453307 = 2179961) B2179961
theorem B765211 : Blo 714321 765211 := bstep (se 1 (by rfl) ⟨573908, by rfl⟩ : syracuseStep 765211 = 1147817) B1147817
theorem B6107471 : Blo 714321 6107471 := bstep (se 1 (by rfl) ⟨4580603, by rfl⟩ : syracuseStep 6107471 = 9161207) B9161207
theorem B2906435 : Blo 714321 2906435 := bstep (se 1 (by rfl) ⟨2179826, by rfl⟩ : syracuseStep 2906435 = 4359653) B4359653
theorem B6547175 : Blo 714321 6547175 := bstep (se 1 (by rfl) ⟨4910381, by rfl⟩ : syracuseStep 6547175 = 9820763) B9820763
theorem B714863 : Blo 714321 714863 := bstep (se 1 (by rfl) ⟨536147, by rfl⟩ : syracuseStep 714863 = 1072295) B1072295
theorem B13953151 : Blo 714321 13953151 := bstep (se 1 (by rfl) ⟨10464863, by rfl⟩ : syracuseStep 13953151 = 20929727) B20929727
theorem B715935 : Blo 714321 715935 := bstep (se 1 (by rfl) ⟨536951, by rfl⟩ : syracuseStep 715935 = 1073903) B1073903
theorem B2288893 : Blo 714321 2288893 := bstep (se 3 (by rfl) ⟨429167, by rfl⟩ : syracuseStep 2288893 = 858335) B858335
theorem B6877021 : Blo 714321 6877021 := bstep (se 3 (by rfl) ⟨1289441, by rfl⟩ : syracuseStep 6877021 = 2578883) B2578883
theorem B44170271 : Blo 714321 44170271 := bstep (se 1 (by rfl) ⟨33127703, by rfl⟩ : syracuseStep 44170271 = 66255407) B66255407
theorem B1937623 : Blo 714321 1937623 := bstep (se 1 (by rfl) ⟨1453217, by rfl⟩ : syracuseStep 1937623 = 2906435) B2906435
theorem B3051857 : Blo 714321 3051857 := bstep (se 2 (by rfl) ⟨1144446, by rfl⟩ : syracuseStep 3051857 = 2288893) B2288893
theorem B1020281 : Blo 714321 1020281 := bstep (se 2 (by rfl) ⟨382605, by rfl⟩ : syracuseStep 1020281 = 765211) B765211
theorem B2036735 : Blo 714321 2036735 := bstep (se 1 (by rfl) ⟨1527551, by rfl⟩ : syracuseStep 2036735 = 3055103) B3055103
theorem B4364783 : Blo 714321 4364783 := bstep (se 1 (by rfl) ⟨3273587, by rfl⟩ : syracuseStep 4364783 = 6547175) B6547175
theorem B4071647 : Blo 714321 4071647 := bstep (se 1 (by rfl) ⟨3053735, by rfl⟩ : syracuseStep 4071647 = 6107471) B6107471
theorem B2040221 : Blo 714321 2040221 := bstep (se 3 (by rfl) ⟨382541, by rfl⟩ : syracuseStep 2040221 = 765083) B765083
theorem B3875485 : Blo 714321 3875485 := bstep (se 3 (by rfl) ⟨726653, by rfl⟩ : syracuseStep 3875485 = 1453307) B1453307
theorem B4598441 : Blo 714321 4598441 := bstep (se 2 (by rfl) ⟨1724415, by rfl⟩ : syracuseStep 4598441 = 3448831) B3448831
theorem B29446847 : Blo 714321 29446847 := bstep (se 1 (by rfl) ⟨22085135, by rfl⟩ : syracuseStep 29446847 = 44170271) B44170271
theorem B18604201 : Blo 714321 18604201 := bstep (se 2 (by rfl) ⟨6976575, by rfl⟩ : syracuseStep 18604201 = 13953151) B13953151
theorem B1073375 : Blo 714321 1073375 := bstep (se 1 (by rfl) ⟨805031, by rfl⟩ : syracuseStep 1073375 = 1610063) B1610063
theorem B1073435 : Blo 714321 1073435 := bstep (se 1 (by rfl) ⟨805076, by rfl⟩ : syracuseStep 1073435 = 1610153) B1610153
theorem B9169361 : Blo 714321 9169361 := bstep (se 2 (by rfl) ⟨3438510, by rfl⟩ : syracuseStep 9169361 = 6877021) B6877021
theorem B24805601 : Blo 714321 24805601 := bstep (se 2 (by rfl) ⟨9302100, by rfl⟩ : syracuseStep 24805601 = 18604201) B18604201
theorem B2720749 : Blo 714321 2720749 := bstep (se 3 (by rfl) ⟨510140, by rfl⟩ : syracuseStep 2720749 = 1020281) B1020281
theorem B2034571 : Blo 714321 2034571 := bstep (se 1 (by rfl) ⟨1525928, by rfl⟩ : syracuseStep 2034571 = 3051857) B3051857
theorem B19631231 : Blo 714321 19631231 := bstep (se 1 (by rfl) ⟨14723423, by rfl⟩ : syracuseStep 19631231 = 29446847) B29446847
theorem B1357823 : Blo 714321 1357823 := bstep (se 1 (by rfl) ⟨1018367, by rfl⟩ : syracuseStep 1357823 = 2036735) B2036735
theorem B1360147 : Blo 714321 1360147 := bstep (se 1 (by rfl) ⟨1020110, by rfl⟩ : syracuseStep 1360147 = 2040221) B2040221
theorem B6112907 : Blo 714321 6112907 := bstep (se 1 (by rfl) ⟨4584680, by rfl⟩ : syracuseStep 6112907 = 9169361) B9169361
theorem B3065627 : Blo 714321 3065627 := bstep (se 1 (by rfl) ⟨2299220, by rfl⟩ : syracuseStep 3065627 = 4598441) B4598441
theorem B5167313 : Blo 714321 5167313 := bstep (se 2 (by rfl) ⟨1937742, by rfl⟩ : syracuseStep 5167313 = 3875485) B3875485
theorem B2909855 : Blo 714321 2909855 := bstep (se 1 (by rfl) ⟨2182391, by rfl⟩ : syracuseStep 2909855 = 4364783) B4364783
theorem B2714431 : Blo 714321 2714431 := bstep (se 1 (by rfl) ⟨2035823, by rfl⟩ : syracuseStep 2714431 = 4071647) B4071647
theorem B715583 : Blo 714321 715583 := bstep (se 1 (by rfl) ⟨536687, by rfl⟩ : syracuseStep 715583 = 1073375) B1073375
theorem B715623 : Blo 714321 715623 := bstep (se 1 (by rfl) ⟨536717, by rfl⟩ : syracuseStep 715623 = 1073435) B1073435
theorem B2583497 : Blo 714321 2583497 := bstep (se 2 (by rfl) ⟨968811, by rfl⟩ : syracuseStep 2583497 = 1937623) B1937623
theorem B3444875 : Blo 714321 3444875 := bstep (se 1 (by rfl) ⟨2583656, by rfl⟩ : syracuseStep 3444875 = 5167313) B5167313
theorem B1813529 : Blo 714321 1813529 := bstep (se 2 (by rfl) ⟨680073, by rfl⟩ : syracuseStep 1813529 = 1360147) B1360147
theorem B4075271 : Blo 714321 4075271 := bstep (se 1 (by rfl) ⟨3056453, by rfl⟩ : syracuseStep 4075271 = 6112907) B6112907
theorem B13087487 : Blo 714321 13087487 := bstep (se 1 (by rfl) ⟨9815615, by rfl⟩ : syracuseStep 13087487 = 19631231) B19631231
theorem B3619241 : Blo 714321 3619241 := bstep (se 2 (by rfl) ⟨1357215, by rfl⟩ : syracuseStep 3619241 = 2714431) B2714431
theorem B8175005 : Blo 714321 8175005 := bstep (se 3 (by rfl) ⟨1532813, by rfl⟩ : syracuseStep 8175005 = 3065627) B3065627
theorem B3620861 : Blo 714321 3620861 := bstep (se 3 (by rfl) ⟨678911, by rfl⟩ : syracuseStep 3620861 = 1357823) B1357823
theorem B1722331 : Blo 714321 1722331 := bstep (se 1 (by rfl) ⟨1291748, by rfl⟩ : syracuseStep 1722331 = 2583497) B2583497
theorem B16537067 : Blo 714321 16537067 := bstep (se 1 (by rfl) ⟨12402800, by rfl⟩ : syracuseStep 16537067 = 24805601) B24805601
theorem B3627665 : Blo 714321 3627665 := bstep (se 2 (by rfl) ⟨1360374, by rfl⟩ : syracuseStep 3627665 = 2720749) B2720749
theorem B2712761 : Blo 714321 2712761 := bstep (se 2 (by rfl) ⟨1017285, by rfl⟩ : syracuseStep 2712761 = 2034571) B2034571
theorem B7759613 : Blo 714321 7759613 := bstep (se 3 (by rfl) ⟨1454927, by rfl⟩ : syracuseStep 7759613 = 2909855) B2909855
theorem B2296441 : Blo 714321 2296441 := bstep (se 2 (by rfl) ⟨861165, by rfl⟩ : syracuseStep 2296441 = 1722331) B1722331
theorem B2296583 : Blo 714321 2296583 := bstep (se 1 (by rfl) ⟨1722437, by rfl⟩ : syracuseStep 2296583 = 3444875) B3444875
theorem B1808507 : Blo 714321 1808507 := bstep (se 1 (by rfl) ⟨1356380, by rfl⟩ : syracuseStep 1808507 = 2712761) B2712761
theorem B8724991 : Blo 714321 8724991 := bstep (se 1 (by rfl) ⟨6543743, by rfl⟩ : syracuseStep 8724991 = 13087487) B13087487
theorem B5450003 : Blo 714321 5450003 := bstep (se 1 (by rfl) ⟨4087502, by rfl⟩ : syracuseStep 5450003 = 8175005) B8175005
theorem B11024711 : Blo 714321 11024711 := bstep (se 1 (by rfl) ⟨8268533, by rfl⟩ : syracuseStep 11024711 = 16537067) B16537067
theorem B2412827 : Blo 714321 2412827 := bstep (se 1 (by rfl) ⟨1809620, by rfl⟩ : syracuseStep 2412827 = 3619241) B3619241
theorem B2413907 : Blo 714321 2413907 := bstep (se 1 (by rfl) ⟨1810430, by rfl⟩ : syracuseStep 2413907 = 3620861) B3620861
theorem B2418443 : Blo 714321 2418443 := bstep (se 1 (by rfl) ⟨1813832, by rfl⟩ : syracuseStep 2418443 = 3627665) B3627665
theorem B5173075 : Blo 714321 5173075 := bstep (se 1 (by rfl) ⟨3879806, by rfl⟩ : syracuseStep 5173075 = 7759613) B7759613
theorem B1209019 : Blo 714321 1209019 := bstep (se 1 (by rfl) ⟨906764, by rfl⟩ : syracuseStep 1209019 = 1813529) B1813529
theorem B2716847 : Blo 714321 2716847 := bstep (se 1 (by rfl) ⟨2037635, by rfl⟩ : syracuseStep 2716847 = 4075271) B4075271
theorem B11633321 : Blo 714321 11633321 := bstep (se 2 (by rfl) ⟨4362495, by rfl⟩ : syracuseStep 11633321 = 8724991) B8724991
theorem B1608551 : Blo 714321 1608551 := bstep (se 1 (by rfl) ⟨1206413, by rfl⟩ : syracuseStep 1608551 = 2412827) B2412827
theorem B1609271 : Blo 714321 1609271 := bstep (se 1 (by rfl) ⟨1206953, by rfl⟩ : syracuseStep 1609271 = 2413907) B2413907
theorem B1612025 : Blo 714321 1612025 := bstep (se 2 (by rfl) ⟨604509, by rfl⟩ : syracuseStep 1612025 = 1209019) B1209019
theorem B1612295 : Blo 714321 1612295 := bstep (se 1 (by rfl) ⟨1209221, by rfl⟩ : syracuseStep 1612295 = 2418443) B2418443
theorem B1811231 : Blo 714321 1811231 := bstep (se 1 (by rfl) ⟨1358423, by rfl⟩ : syracuseStep 1811231 = 2716847) B2716847
theorem B7349807 : Blo 714321 7349807 := bstep (se 1 (by rfl) ⟨5512355, by rfl⟩ : syracuseStep 7349807 = 11024711) B11024711
theorem B3061921 : Blo 714321 3061921 := bstep (se 2 (by rfl) ⟨1148220, by rfl⟩ : syracuseStep 3061921 = 2296441) B2296441
theorem B6897433 : Blo 714321 6897433 := bstep (se 2 (by rfl) ⟨2586537, by rfl⟩ : syracuseStep 6897433 = 5173075) B5173075
theorem B1531055 : Blo 714321 1531055 := bstep (se 1 (by rfl) ⟨1148291, by rfl⟩ : syracuseStep 1531055 = 2296583) B2296583
theorem B1205671 : Blo 714321 1205671 := bstep (se 1 (by rfl) ⟨904253, by rfl⟩ : syracuseStep 1205671 = 1808507) B1808507
theorem B3633335 : Blo 714321 3633335 := bstep (se 1 (by rfl) ⟨2725001, by rfl⟩ : syracuseStep 3633335 = 5450003) B5450003
theorem B1607561 : Blo 714321 1607561 := bstep (se 2 (by rfl) ⟨602835, by rfl⟩ : syracuseStep 1607561 = 1205671) B1205671
theorem B1020703 : Blo 714321 1020703 := bstep (se 1 (by rfl) ⟨765527, by rfl⟩ : syracuseStep 1020703 = 1531055) B1531055
theorem B4899871 : Blo 714321 4899871 := bstep (se 1 (by rfl) ⟨3674903, by rfl⟩ : syracuseStep 4899871 = 7349807) B7349807
theorem B4082561 : Blo 714321 4082561 := bstep (se 2 (by rfl) ⟨1530960, by rfl⟩ : syracuseStep 4082561 = 3061921) B3061921
theorem B9196577 : Blo 714321 9196577 := bstep (se 2 (by rfl) ⟨3448716, by rfl⟩ : syracuseStep 9196577 = 6897433) B6897433
theorem B7755547 : Blo 714321 7755547 := bstep (se 1 (by rfl) ⟨5816660, by rfl⟩ : syracuseStep 7755547 = 11633321) B11633321
theorem B1072367 : Blo 714321 1072367 := bstep (se 1 (by rfl) ⟨804275, by rfl⟩ : syracuseStep 1072367 = 1608551) B1608551
theorem B1072847 : Blo 714321 1072847 := bstep (se 1 (by rfl) ⟨804635, by rfl⟩ : syracuseStep 1072847 = 1609271) B1609271
theorem B1074683 : Blo 714321 1074683 := bstep (se 1 (by rfl) ⟨806012, by rfl⟩ : syracuseStep 1074683 = 1612025) B1612025
theorem B1074863 : Blo 714321 1074863 := bstep (se 1 (by rfl) ⟨806147, by rfl⟩ : syracuseStep 1074863 = 1612295) B1612295
theorem B1207487 : Blo 714321 1207487 := bstep (se 1 (by rfl) ⟨905615, by rfl⟩ : syracuseStep 1207487 = 1811231) B1811231
theorem B2422223 : Blo 714321 2422223 := bstep (se 1 (by rfl) ⟨1816667, by rfl⟩ : syracuseStep 2422223 = 3633335) B3633335
theorem B2721707 : Blo 714321 2721707 := bstep (se 1 (by rfl) ⟨2041280, by rfl⟩ : syracuseStep 2721707 = 4082561) B4082561
theorem B6131051 : Blo 714321 6131051 := bstep (se 1 (by rfl) ⟨4598288, by rfl⟩ : syracuseStep 6131051 = 9196577) B9196577
theorem B1614815 : Blo 714321 1614815 := bstep (se 1 (by rfl) ⟨1211111, by rfl⟩ : syracuseStep 1614815 = 2422223) B2422223
theorem B26132645 : Blo 714321 26132645 := bstep (se 4 (by rfl) ⟨2449935, by rfl⟩ : syracuseStep 26132645 = 4899871) B4899871
theorem B1360937 : Blo 714321 1360937 := bstep (se 2 (by rfl) ⟨510351, by rfl⟩ : syracuseStep 1360937 = 1020703) B1020703
theorem B804991 : Blo 714321 804991 := bstep (se 1 (by rfl) ⟨603743, by rfl⟩ : syracuseStep 804991 = 1207487) B1207487
theorem B10340729 : Blo 714321 10340729 := bstep (se 2 (by rfl) ⟨3877773, by rfl⟩ : syracuseStep 10340729 = 7755547) B7755547
theorem B1071707 : Blo 714321 1071707 := bstep (se 1 (by rfl) ⟨803780, by rfl⟩ : syracuseStep 1071707 = 1607561) B1607561
theorem B714911 : Blo 714321 714911 := bstep (se 1 (by rfl) ⟨536183, by rfl⟩ : syracuseStep 714911 = 1072367) B1072367
theorem B715231 : Blo 714321 715231 := bstep (se 1 (by rfl) ⟨536423, by rfl⟩ : syracuseStep 715231 = 1072847) B1072847
theorem B716455 : Blo 714321 716455 := bstep (se 1 (by rfl) ⟨537341, by rfl⟩ : syracuseStep 716455 = 1074683) B1074683
theorem B716575 : Blo 714321 716575 := bstep (se 1 (by rfl) ⟨537431, by rfl⟩ : syracuseStep 716575 = 1074863) B1074863
theorem B1814471 : Blo 714321 1814471 := bstep (se 1 (by rfl) ⟨1360853, by rfl⟩ : syracuseStep 1814471 = 2721707) B2721707
theorem B6893819 : Blo 714321 6893819 := bstep (se 1 (by rfl) ⟨5170364, by rfl⟩ : syracuseStep 6893819 = 10340729) B10340729
theorem B17421763 : Blo 714321 17421763 := bstep (se 1 (by rfl) ⟨13066322, by rfl⟩ : syracuseStep 17421763 = 26132645) B26132645
theorem B907291 : Blo 714321 907291 := bstep (se 1 (by rfl) ⟨680468, by rfl⟩ : syracuseStep 907291 = 1360937) B1360937
theorem B4087367 : Blo 714321 4087367 := bstep (se 1 (by rfl) ⟨3065525, by rfl⟩ : syracuseStep 4087367 = 6131051) B6131051
theorem B1073321 : Blo 714321 1073321 := bstep (se 2 (by rfl) ⟨402495, by rfl⟩ : syracuseStep 1073321 = 804991) B804991
theorem B714471 : Blo 714321 714471 := bstep (se 1 (by rfl) ⟨535853, by rfl⟩ : syracuseStep 714471 = 1071707) B1071707
theorem B1076543 : Blo 714321 1076543 := bstep (se 1 (by rfl) ⟨807407, by rfl⟩ : syracuseStep 1076543 = 1614815) B1614815
theorem B2724911 : Blo 714321 2724911 := bstep (se 1 (by rfl) ⟨2043683, by rfl⟩ : syracuseStep 2724911 = 4087367) B4087367
theorem B4595879 : Blo 714321 4595879 := bstep (se 1 (by rfl) ⟨3446909, by rfl⟩ : syracuseStep 4595879 = 6893819) B6893819
theorem B715547 : Blo 714321 715547 := bstep (se 1 (by rfl) ⟨536660, by rfl⟩ : syracuseStep 715547 = 1073321) B1073321
theorem B23229017 : Blo 714321 23229017 := bstep (se 2 (by rfl) ⟨8710881, by rfl⟩ : syracuseStep 23229017 = 17421763) B17421763
theorem B717695 : Blo 714321 717695 := bstep (se 1 (by rfl) ⟨538271, by rfl⟩ : syracuseStep 717695 = 1076543) B1076543
theorem B1209647 : Blo 714321 1209647 := bstep (se 1 (by rfl) ⟨907235, by rfl⟩ : syracuseStep 1209647 = 1814471) B1814471
theorem B1209721 : Blo 714321 1209721 := bstep (se 2 (by rfl) ⟨453645, by rfl⟩ : syracuseStep 1209721 = 907291) B907291
theorem B1612961 : Blo 714321 1612961 := bstep (se 2 (by rfl) ⟨604860, by rfl⟩ : syracuseStep 1612961 = 1209721) B1209721
theorem B1816607 : Blo 714321 1816607 := bstep (se 1 (by rfl) ⟨1362455, by rfl⟩ : syracuseStep 1816607 = 2724911) B2724911
theorem B3063919 : Blo 714321 3063919 := bstep (se 1 (by rfl) ⟨2297939, by rfl⟩ : syracuseStep 3063919 = 4595879) B4595879
theorem B15486011 : Blo 714321 15486011 := bstep (se 1 (by rfl) ⟨11614508, by rfl⟩ : syracuseStep 15486011 = 23229017) B23229017
theorem B806431 : Blo 714321 806431 := bstep (se 1 (by rfl) ⟨604823, by rfl⟩ : syracuseStep 806431 = 1209647) B1209647
theorem B10324007 : Blo 714321 10324007 := bstep (se 1 (by rfl) ⟨7743005, by rfl⟩ : syracuseStep 10324007 = 15486011) B15486011
theorem B4085225 : Blo 714321 4085225 := bstep (se 2 (by rfl) ⟨1531959, by rfl⟩ : syracuseStep 4085225 = 3063919) B3063919
theorem B1075241 : Blo 714321 1075241 := bstep (se 2 (by rfl) ⟨403215, by rfl⟩ : syracuseStep 1075241 = 806431) B806431
theorem B1075307 : Blo 714321 1075307 := bstep (se 1 (by rfl) ⟨806480, by rfl⟩ : syracuseStep 1075307 = 1612961) B1612961
theorem B1211071 : Blo 714321 1211071 := bstep (se 1 (by rfl) ⟨908303, by rfl⟩ : syracuseStep 1211071 = 1816607) B1816607
theorem B6882671 : Blo 714321 6882671 := bstep (se 1 (by rfl) ⟨5162003, by rfl⟩ : syracuseStep 6882671 = 10324007) B10324007
theorem B2723483 : Blo 714321 2723483 := bstep (se 1 (by rfl) ⟨2042612, by rfl⟩ : syracuseStep 2723483 = 4085225) B4085225
theorem B1614761 : Blo 714321 1614761 := bstep (se 2 (by rfl) ⟨605535, by rfl⟩ : syracuseStep 1614761 = 1211071) B1211071
theorem B716827 : Blo 714321 716827 := bstep (se 1 (by rfl) ⟨537620, by rfl⟩ : syracuseStep 716827 = 1075241) B1075241
theorem B716871 : Blo 714321 716871 := bstep (se 1 (by rfl) ⟨537653, by rfl⟩ : syracuseStep 716871 = 1075307) B1075307
theorem B4588447 : Blo 714321 4588447 := bstep (se 1 (by rfl) ⟨3441335, by rfl⟩ : syracuseStep 4588447 = 6882671) B6882671
theorem B1815655 : Blo 714321 1815655 := bstep (se 1 (by rfl) ⟨1361741, by rfl⟩ : syracuseStep 1815655 = 2723483) B2723483
theorem B1076507 : Blo 714321 1076507 := bstep (se 1 (by rfl) ⟨807380, by rfl⟩ : syracuseStep 1076507 = 1614761) B1614761
theorem B6117929 : Blo 714321 6117929 := bstep (se 2 (by rfl) ⟨2294223, by rfl⟩ : syracuseStep 6117929 = 4588447) B4588447
theorem B2420873 : Blo 714321 2420873 := bstep (se 2 (by rfl) ⟨907827, by rfl⟩ : syracuseStep 2420873 = 1815655) B1815655
theorem B717671 : Blo 714321 717671 := bstep (se 1 (by rfl) ⟨538253, by rfl⟩ : syracuseStep 717671 = 1076507) B1076507
theorem B1613915 : Blo 714321 1613915 := bstep (se 1 (by rfl) ⟨1210436, by rfl⟩ : syracuseStep 1613915 = 2420873) B2420873
theorem B4078619 : Blo 714321 4078619 := bstep (se 1 (by rfl) ⟨3058964, by rfl⟩ : syracuseStep 4078619 = 6117929) B6117929
theorem B1075943 : Blo 714321 1075943 := bstep (se 1 (by rfl) ⟨806957, by rfl⟩ : syracuseStep 1075943 = 1613915) B1613915
theorem B2719079 : Blo 714321 2719079 := bstep (se 1 (by rfl) ⟨2039309, by rfl⟩ : syracuseStep 2719079 = 4078619) B4078619
theorem B1812719 : Blo 714321 1812719 := bstep (se 1 (by rfl) ⟨1359539, by rfl⟩ : syracuseStep 1812719 = 2719079) B2719079
theorem B717295 : Blo 714321 717295 := bstep (se 1 (by rfl) ⟨537971, by rfl⟩ : syracuseStep 717295 = 1075943) B1075943
theorem B1208479 : Blo 714321 1208479 := bstep (se 1 (by rfl) ⟨906359, by rfl⟩ : syracuseStep 1208479 = 1812719) B1812719
theorem B1611305 : Blo 714321 1611305 := bstep (se 2 (by rfl) ⟨604239, by rfl⟩ : syracuseStep 1611305 = 1208479) B1208479
theorem B1074203 : Blo 714321 1074203 := bstep (se 1 (by rfl) ⟨805652, by rfl⟩ : syracuseStep 1074203 = 1611305) B1611305
theorem B716135 : Blo 714321 716135 := bstep (se 1 (by rfl) ⟨537101, by rfl⟩ : syracuseStep 716135 = 1074203) B1074203

theorem C0 (j : ℕ) (h1 : 178580 ≤ j) (h2 : j ≤ 179279) : Blo 714321 (4 * j + 3) := by
  interval_cases j
  · exact B714323
  · exact B714327
  · exact B714331
  · exact B714335
  · exact B714339
  · exact B714343
  · exact B714347
  · exact B714351
  · exact B714355
  · exact B714359
  · exact B714363
  · exact B714367
  · exact B714371
  · exact B714375
  · exact B714379
  · exact B714383
  · exact B714387
  · exact B714391
  · exact B714395
  · exact B714399
  · exact B714403
  · exact B714407
  · exact B714411
  · exact B714415
  · exact B714419
  · exact B714423
  · exact B714427
  · exact B714431
  · exact B714435
  · exact B714439
  · exact B714443
  · exact B714447
  · exact B714451
  · exact B714455
  · exact B714459
  · exact B714463
  · exact B714467
  · exact B714471
  · exact B714475
  · exact B714479
  · exact B714483
  · exact B714487
  · exact B714491
  · exact B714495
  · exact B714499
  · exact B714503
  · exact B714507
  · exact B714511
  · exact B714515
  · exact B714519
  · exact B714523
  · exact B714527
  · exact B714531
  · exact B714535
  · exact B714539
  · exact B714543
  · exact B714547
  · exact B714551
  · exact B714555
  · exact B714559
  · exact B714563
  · exact B714567
  · exact B714571
  · exact B714575
  · exact B714579
  · exact B714583
  · exact B714587
  · exact B714591
  · exact B714595
  · exact B714599
  · exact B714603
  · exact B714607
  · exact B714611
  · exact B714615
  · exact B714619
  · exact B714623
  · exact B714627
  · exact B714631
  · exact B714635
  · exact B714639
  · exact B714643
  · exact B714647
  · exact B714651
  · exact B714655
  · exact B714659
  · exact B714663
  · exact B714667
  · exact B714671
  · exact B714675
  · exact B714679
  · exact B714683
  · exact B714687
  · exact B714691
  · exact B714695
  · exact B714699
  · exact B714703
  · exact B714707
  · exact B714711
  · exact B714715
  · exact B714719
  · exact B714723
  · exact B714727
  · exact B714731
  · exact B714735
  · exact B714739
  · exact B714743
  · exact B714747
  · exact B714751
  · exact B714755
  · exact B714759
  · exact B714763
  · exact B714767
  · exact B714771
  · exact B714775
  · exact B714779
  · exact B714783
  · exact B714787
  · exact B714791
  · exact B714795
  · exact B714799
  · exact B714803
  · exact B714807
  · exact B714811
  · exact B714815
  · exact B714819
  · exact B714823
  · exact B714827
  · exact B714831
  · exact B714835
  · exact B714839
  · exact B714843
  · exact B714847
  · exact B714851
  · exact B714855
  · exact B714859
  · exact B714863
  · exact B714867
  · exact B714871
  · exact B714875
  · exact B714879
  · exact B714883
  · exact B714887
  · exact B714891
  · exact B714895
  · exact B714899
  · exact B714903
  · exact B714907
  · exact B714911
  · exact B714915
  · exact B714919
  · exact B714923
  · exact B714927
  · exact B714931
  · exact B714935
  · exact B714939
  · exact B714943
  · exact B714947
  · exact B714951
  · exact B714955
  · exact B714959
  · exact B714963
  · exact B714967
  · exact B714971
  · exact B714975
  · exact B714979
  · exact B714983
  · exact B714987
  · exact B714991
  · exact B714995
  · exact B714999
  · exact B715003
  · exact B715007
  · exact B715011
  · exact B715015
  · exact B715019
  · exact B715023
  · exact B715027
  · exact B715031
  · exact B715035
  · exact B715039
  · exact B715043
  · exact B715047
  · exact B715051
  · exact B715055
  · exact B715059
  · exact B715063
  · exact B715067
  · exact B715071
  · exact B715075
  · exact B715079
  · exact B715083
  · exact B715087
  · exact B715091
  · exact B715095
  · exact B715099
  · exact B715103
  · exact B715107
  · exact B715111
  · exact B715115
  · exact B715119
  · exact B715123
  · exact B715127
  · exact B715131
  · exact B715135
  · exact B715139
  · exact B715143
  · exact B715147
  · exact B715151
  · exact B715155
  · exact B715159
  · exact B715163
  · exact B715167
  · exact B715171
  · exact B715175
  · exact B715179
  · exact B715183
  · exact B715187
  · exact B715191
  · exact B715195
  · exact B715199
  · exact B715203
  · exact B715207
  · exact B715211
  · exact B715215
  · exact B715219
  · exact B715223
  · exact B715227
  · exact B715231
  · exact B715235
  · exact B715239
  · exact B715243
  · exact B715247
  · exact B715251
  · exact B715255
  · exact B715259
  · exact B715263
  · exact B715267
  · exact B715271
  · exact B715275
  · exact B715279
  · exact B715283
  · exact B715287
  · exact B715291
  · exact B715295
  · exact B715299
  · exact B715303
  · exact B715307
  · exact B715311
  · exact B715315
  · exact B715319
  · exact B715323
  · exact B715327
  · exact B715331
  · exact B715335
  · exact B715339
  · exact B715343
  · exact B715347
  · exact B715351
  · exact B715355
  · exact B715359
  · exact B715363
  · exact B715367
  · exact B715371
  · exact B715375
  · exact B715379
  · exact B715383
  · exact B715387
  · exact B715391
  · exact B715395
  · exact B715399
  · exact B715403
  · exact B715407
  · exact B715411
  · exact B715415
  · exact B715419
  · exact B715423
  · exact B715427
  · exact B715431
  · exact B715435
  · exact B715439
  · exact B715443
  · exact B715447
  · exact B715451
  · exact B715455
  · exact B715459
  · exact B715463
  · exact B715467
  · exact B715471
  · exact B715475
  · exact B715479
  · exact B715483
  · exact B715487
  · exact B715491
  · exact B715495
  · exact B715499
  · exact B715503
  · exact B715507
  · exact B715511
  · exact B715515
  · exact B715519
  · exact B715523
  · exact B715527
  · exact B715531
  · exact B715535
  · exact B715539
  · exact B715543
  · exact B715547
  · exact B715551
  · exact B715555
  · exact B715559
  · exact B715563
  · exact B715567
  · exact B715571
  · exact B715575
  · exact B715579
  · exact B715583
  · exact B715587
  · exact B715591
  · exact B715595
  · exact B715599
  · exact B715603
  · exact B715607
  · exact B715611
  · exact B715615
  · exact B715619
  · exact B715623
  · exact B715627
  · exact B715631
  · exact B715635
  · exact B715639
  · exact B715643
  · exact B715647
  · exact B715651
  · exact B715655
  · exact B715659
  · exact B715663
  · exact B715667
  · exact B715671
  · exact B715675
  · exact B715679
  · exact B715683
  · exact B715687
  · exact B715691
  · exact B715695
  · exact B715699
  · exact B715703
  · exact B715707
  · exact B715711
  · exact B715715
  · exact B715719
  · exact B715723
  · exact B715727
  · exact B715731
  · exact B715735
  · exact B715739
  · exact B715743
  · exact B715747
  · exact B715751
  · exact B715755
  · exact B715759
  · exact B715763
  · exact B715767
  · exact B715771
  · exact B715775
  · exact B715779
  · exact B715783
  · exact B715787
  · exact B715791
  · exact B715795
  · exact B715799
  · exact B715803
  · exact B715807
  · exact B715811
  · exact B715815
  · exact B715819
  · exact B715823
  · exact B715827
  · exact B715831
  · exact B715835
  · exact B715839
  · exact B715843
  · exact B715847
  · exact B715851
  · exact B715855
  · exact B715859
  · exact B715863
  · exact B715867
  · exact B715871
  · exact B715875
  · exact B715879
  · exact B715883
  · exact B715887
  · exact B715891
  · exact B715895
  · exact B715899
  · exact B715903
  · exact B715907
  · exact B715911
  · exact B715915
  · exact B715919
  · exact B715923
  · exact B715927
  · exact B715931
  · exact B715935
  · exact B715939
  · exact B715943
  · exact B715947
  · exact B715951
  · exact B715955
  · exact B715959
  · exact B715963
  · exact B715967
  · exact B715971
  · exact B715975
  · exact B715979
  · exact B715983
  · exact B715987
  · exact B715991
  · exact B715995
  · exact B715999
  · exact B716003
  · exact B716007
  · exact B716011
  · exact B716015
  · exact B716019
  · exact B716023
  · exact B716027
  · exact B716031
  · exact B716035
  · exact B716039
  · exact B716043
  · exact B716047
  · exact B716051
  · exact B716055
  · exact B716059
  · exact B716063
  · exact B716067
  · exact B716071
  · exact B716075
  · exact B716079
  · exact B716083
  · exact B716087
  · exact B716091
  · exact B716095
  · exact B716099
  · exact B716103
  · exact B716107
  · exact B716111
  · exact B716115
  · exact B716119
  · exact B716123
  · exact B716127
  · exact B716131
  · exact B716135
  · exact B716139
  · exact B716143
  · exact B716147
  · exact B716151
  · exact B716155
  · exact B716159
  · exact B716163
  · exact B716167
  · exact B716171
  · exact B716175
  · exact B716179
  · exact B716183
  · exact B716187
  · exact B716191
  · exact B716195
  · exact B716199
  · exact B716203
  · exact B716207
  · exact B716211
  · exact B716215
  · exact B716219
  · exact B716223
  · exact B716227
  · exact B716231
  · exact B716235
  · exact B716239
  · exact B716243
  · exact B716247
  · exact B716251
  · exact B716255
  · exact B716259
  · exact B716263
  · exact B716267
  · exact B716271
  · exact B716275
  · exact B716279
  · exact B716283
  · exact B716287
  · exact B716291
  · exact B716295
  · exact B716299
  · exact B716303
  · exact B716307
  · exact B716311
  · exact B716315
  · exact B716319
  · exact B716323
  · exact B716327
  · exact B716331
  · exact B716335
  · exact B716339
  · exact B716343
  · exact B716347
  · exact B716351
  · exact B716355
  · exact B716359
  · exact B716363
  · exact B716367
  · exact B716371
  · exact B716375
  · exact B716379
  · exact B716383
  · exact B716387
  · exact B716391
  · exact B716395
  · exact B716399
  · exact B716403
  · exact B716407
  · exact B716411
  · exact B716415
  · exact B716419
  · exact B716423
  · exact B716427
  · exact B716431
  · exact B716435
  · exact B716439
  · exact B716443
  · exact B716447
  · exact B716451
  · exact B716455
  · exact B716459
  · exact B716463
  · exact B716467
  · exact B716471
  · exact B716475
  · exact B716479
  · exact B716483
  · exact B716487
  · exact B716491
  · exact B716495
  · exact B716499
  · exact B716503
  · exact B716507
  · exact B716511
  · exact B716515
  · exact B716519
  · exact B716523
  · exact B716527
  · exact B716531
  · exact B716535
  · exact B716539
  · exact B716543
  · exact B716547
  · exact B716551
  · exact B716555
  · exact B716559
  · exact B716563
  · exact B716567
  · exact B716571
  · exact B716575
  · exact B716579
  · exact B716583
  · exact B716587
  · exact B716591
  · exact B716595
  · exact B716599
  · exact B716603
  · exact B716607
  · exact B716611
  · exact B716615
  · exact B716619
  · exact B716623
  · exact B716627
  · exact B716631
  · exact B716635
  · exact B716639
  · exact B716643
  · exact B716647
  · exact B716651
  · exact B716655
  · exact B716659
  · exact B716663
  · exact B716667
  · exact B716671
  · exact B716675
  · exact B716679
  · exact B716683
  · exact B716687
  · exact B716691
  · exact B716695
  · exact B716699
  · exact B716703
  · exact B716707
  · exact B716711
  · exact B716715
  · exact B716719
  · exact B716723
  · exact B716727
  · exact B716731
  · exact B716735
  · exact B716739
  · exact B716743
  · exact B716747
  · exact B716751
  · exact B716755
  · exact B716759
  · exact B716763
  · exact B716767
  · exact B716771
  · exact B716775
  · exact B716779
  · exact B716783
  · exact B716787
  · exact B716791
  · exact B716795
  · exact B716799
  · exact B716803
  · exact B716807
  · exact B716811
  · exact B716815
  · exact B716819
  · exact B716823
  · exact B716827
  · exact B716831
  · exact B716835
  · exact B716839
  · exact B716843
  · exact B716847
  · exact B716851
  · exact B716855
  · exact B716859
  · exact B716863
  · exact B716867
  · exact B716871
  · exact B716875
  · exact B716879
  · exact B716883
  · exact B716887
  · exact B716891
  · exact B716895
  · exact B716899
  · exact B716903
  · exact B716907
  · exact B716911
  · exact B716915
  · exact B716919
  · exact B716923
  · exact B716927
  · exact B716931
  · exact B716935
  · exact B716939
  · exact B716943
  · exact B716947
  · exact B716951
  · exact B716955
  · exact B716959
  · exact B716963
  · exact B716967
  · exact B716971
  · exact B716975
  · exact B716979
  · exact B716983
  · exact B716987
  · exact B716991
  · exact B716995
  · exact B716999
  · exact B717003
  · exact B717007
  · exact B717011
  · exact B717015
  · exact B717019
  · exact B717023
  · exact B717027
  · exact B717031
  · exact B717035
  · exact B717039
  · exact B717043
  · exact B717047
  · exact B717051
  · exact B717055
  · exact B717059
  · exact B717063
  · exact B717067
  · exact B717071
  · exact B717075
  · exact B717079
  · exact B717083
  · exact B717087
  · exact B717091
  · exact B717095
  · exact B717099
  · exact B717103
  · exact B717107
  · exact B717111
  · exact B717115
  · exact B717119

theorem C1 (j : ℕ) (h1 : 179280 ≤ j) (h2 : j ≤ 179579) : Blo 714321 (4 * j + 3) := by
  interval_cases j
  · exact B717123
  · exact B717127
  · exact B717131
  · exact B717135
  · exact B717139
  · exact B717143
  · exact B717147
  · exact B717151
  · exact B717155
  · exact B717159
  · exact B717163
  · exact B717167
  · exact B717171
  · exact B717175
  · exact B717179
  · exact B717183
  · exact B717187
  · exact B717191
  · exact B717195
  · exact B717199
  · exact B717203
  · exact B717207
  · exact B717211
  · exact B717215
  · exact B717219
  · exact B717223
  · exact B717227
  · exact B717231
  · exact B717235
  · exact B717239
  · exact B717243
  · exact B717247
  · exact B717251
  · exact B717255
  · exact B717259
  · exact B717263
  · exact B717267
  · exact B717271
  · exact B717275
  · exact B717279
  · exact B717283
  · exact B717287
  · exact B717291
  · exact B717295
  · exact B717299
  · exact B717303
  · exact B717307
  · exact B717311
  · exact B717315
  · exact B717319
  · exact B717323
  · exact B717327
  · exact B717331
  · exact B717335
  · exact B717339
  · exact B717343
  · exact B717347
  · exact B717351
  · exact B717355
  · exact B717359
  · exact B717363
  · exact B717367
  · exact B717371
  · exact B717375
  · exact B717379
  · exact B717383
  · exact B717387
  · exact B717391
  · exact B717395
  · exact B717399
  · exact B717403
  · exact B717407
  · exact B717411
  · exact B717415
  · exact B717419
  · exact B717423
  · exact B717427
  · exact B717431
  · exact B717435
  · exact B717439
  · exact B717443
  · exact B717447
  · exact B717451
  · exact B717455
  · exact B717459
  · exact B717463
  · exact B717467
  · exact B717471
  · exact B717475
  · exact B717479
  · exact B717483
  · exact B717487
  · exact B717491
  · exact B717495
  · exact B717499
  · exact B717503
  · exact B717507
  · exact B717511
  · exact B717515
  · exact B717519
  · exact B717523
  · exact B717527
  · exact B717531
  · exact B717535
  · exact B717539
  · exact B717543
  · exact B717547
  · exact B717551
  · exact B717555
  · exact B717559
  · exact B717563
  · exact B717567
  · exact B717571
  · exact B717575
  · exact B717579
  · exact B717583
  · exact B717587
  · exact B717591
  · exact B717595
  · exact B717599
  · exact B717603
  · exact B717607
  · exact B717611
  · exact B717615
  · exact B717619
  · exact B717623
  · exact B717627
  · exact B717631
  · exact B717635
  · exact B717639
  · exact B717643
  · exact B717647
  · exact B717651
  · exact B717655
  · exact B717659
  · exact B717663
  · exact B717667
  · exact B717671
  · exact B717675
  · exact B717679
  · exact B717683
  · exact B717687
  · exact B717691
  · exact B717695
  · exact B717699
  · exact B717703
  · exact B717707
  · exact B717711
  · exact B717715
  · exact B717719
  · exact B717723
  · exact B717727
  · exact B717731
  · exact B717735
  · exact B717739
  · exact B717743
  · exact B717747
  · exact B717751
  · exact B717755
  · exact B717759
  · exact B717763
  · exact B717767
  · exact B717771
  · exact B717775
  · exact B717779
  · exact B717783
  · exact B717787
  · exact B717791
  · exact B717795
  · exact B717799
  · exact B717803
  · exact B717807
  · exact B717811
  · exact B717815
  · exact B717819
  · exact B717823
  · exact B717827
  · exact B717831
  · exact B717835
  · exact B717839
  · exact B717843
  · exact B717847
  · exact B717851
  · exact B717855
  · exact B717859
  · exact B717863
  · exact B717867
  · exact B717871
  · exact B717875
  · exact B717879
  · exact B717883
  · exact B717887
  · exact B717891
  · exact B717895
  · exact B717899
  · exact B717903
  · exact B717907
  · exact B717911
  · exact B717915
  · exact B717919
  · exact B717923
  · exact B717927
  · exact B717931
  · exact B717935
  · exact B717939
  · exact B717943
  · exact B717947
  · exact B717951
  · exact B717955
  · exact B717959
  · exact B717963
  · exact B717967
  · exact B717971
  · exact B717975
  · exact B717979
  · exact B717983
  · exact B717987
  · exact B717991
  · exact B717995
  · exact B717999
  · exact B718003
  · exact B718007
  · exact B718011
  · exact B718015
  · exact B718019
  · exact B718023
  · exact B718027
  · exact B718031
  · exact B718035
  · exact B718039
  · exact B718043
  · exact B718047
  · exact B718051
  · exact B718055
  · exact B718059
  · exact B718063
  · exact B718067
  · exact B718071
  · exact B718075
  · exact B718079
  · exact B718083
  · exact B718087
  · exact B718091
  · exact B718095
  · exact B718099
  · exact B718103
  · exact B718107
  · exact B718111
  · exact B718115
  · exact B718119
  · exact B718123
  · exact B718127
  · exact B718131
  · exact B718135
  · exact B718139
  · exact B718143
  · exact B718147
  · exact B718151
  · exact B718155
  · exact B718159
  · exact B718163
  · exact B718167
  · exact B718171
  · exact B718175
  · exact B718179
  · exact B718183
  · exact B718187
  · exact B718191
  · exact B718195
  · exact B718199
  · exact B718203
  · exact B718207
  · exact B718211
  · exact B718215
  · exact B718219
  · exact B718223
  · exact B718227
  · exact B718231
  · exact B718235
  · exact B718239
  · exact B718243
  · exact B718247
  · exact B718251
  · exact B718255
  · exact B718259
  · exact B718263
  · exact B718267
  · exact B718271
  · exact B718275
  · exact B718279
  · exact B718283
  · exact B718287
  · exact B718291
  · exact B718295
  · exact B718299
  · exact B718303
  · exact B718307
  · exact B718311
  · exact B718315
  · exact B718319

theorem solution (m : ℕ) (hlo : 714321 ≤ m) (hhi : m ≤ 718321) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 178580 ≤ j := by omega
    have hj2 : j ≤ 179579 := by omega
    have hb : Blo 714321 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 179280 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
