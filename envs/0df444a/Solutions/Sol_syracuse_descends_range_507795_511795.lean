-- Prove2me | solution 1 for syracuse_descends_range_507795_511795
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T17:48:17.310636+00:00
-- url     : https://prove2.me/submissions/eb5b3b3a-add2-4e67-b6c4-40dc2e3ef99e

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


theorem B819229 : Blo 507795 819229 := bbase (se 3 (by rfl) ⟨153605, by rfl⟩ : syracuseStep 819229 = 307211) (by norm_num)
theorem B1146941 : Blo 507795 1146941 := bbase (se 3 (by rfl) ⟨215051, by rfl⟩ : syracuseStep 1146941 = 430103) (by norm_num)
theorem B983125 : Blo 507795 983125 := bbase (se 8 (by rfl) ⟨5760, by rfl⟩ : syracuseStep 983125 = 11521) (by norm_num)
theorem B1933429 : Blo 507795 1933429 := bbase (se 5 (by rfl) ⟨90629, by rfl⟩ : syracuseStep 1933429 = 181259) (by norm_num)
theorem B1147013 : Blo 507795 1147013 := bbase (se 4 (by rfl) ⟨107532, by rfl⟩ : syracuseStep 1147013 = 215065) (by norm_num)
theorem B1147085 : Blo 507795 1147085 := bbase (se 3 (by rfl) ⟨215078, by rfl⟩ : syracuseStep 1147085 = 430157) (by norm_num)
theorem B1147157 : Blo 507795 1147157 := bbase (se 6 (by rfl) ⟨26886, by rfl⟩ : syracuseStep 1147157 = 53773) (by norm_num)
theorem B819485 : Blo 507795 819485 := bbase (se 3 (by rfl) ⟨153653, by rfl⟩ : syracuseStep 819485 = 307307) (by norm_num)
theorem B1147229 : Blo 507795 1147229 := bbase (se 3 (by rfl) ⟨215105, by rfl⟩ : syracuseStep 1147229 = 430211) (by norm_num)
theorem B1933733 : Blo 507795 1933733 := bbase (se 4 (by rfl) ⟨181287, by rfl⟩ : syracuseStep 1933733 = 362575) (by norm_num)
theorem B1147301 : Blo 507795 1147301 := bbase (se 4 (by rfl) ⟨107559, by rfl⟩ : syracuseStep 1147301 = 215119) (by norm_num)
theorem B819677 : Blo 507795 819677 := bbase (se 3 (by rfl) ⟨153689, by rfl⟩ : syracuseStep 819677 = 307379) (by norm_num)
theorem B1147373 : Blo 507795 1147373 := bbase (se 3 (by rfl) ⟨215132, by rfl⟩ : syracuseStep 1147373 = 430265) (by norm_num)
theorem B1147445 : Blo 507795 1147445 := bbase (se 5 (by rfl) ⟨53786, by rfl⟩ : syracuseStep 1147445 = 107573) (by norm_num)
theorem B1114717 : Blo 507795 1114717 := bbase (se 3 (by rfl) ⟨209009, by rfl⟩ : syracuseStep 1114717 = 418019) (by norm_num)
theorem B1966693 : Blo 507795 1966693 := bbase (se 4 (by rfl) ⟨184377, by rfl⟩ : syracuseStep 1966693 = 368755) (by norm_num)
theorem B4915829 : Blo 507795 4915829 := bbase (se 5 (by rfl) ⟨230429, by rfl⟩ : syracuseStep 4915829 = 460859) (by norm_num)
theorem B1147517 : Blo 507795 1147517 := bbase (se 3 (by rfl) ⟨215159, by rfl⟩ : syracuseStep 1147517 = 430319) (by norm_num)
theorem B1147589 : Blo 507795 1147589 := bbase (se 4 (by rfl) ⟨107586, by rfl⟩ : syracuseStep 1147589 = 215173) (by norm_num)
theorem B1147661 : Blo 507795 1147661 := bbase (se 3 (by rfl) ⟨215186, by rfl⟩ : syracuseStep 1147661 = 430373) (by norm_num)
theorem B4358933 : Blo 507795 4358933 := bbase (se 6 (by rfl) ⟨102162, by rfl⟩ : syracuseStep 4358933 = 204325) (by norm_num)
theorem B1737557 : Blo 507795 1737557 := bbase (se 9 (by rfl) ⟨5090, by rfl⟩ : syracuseStep 1737557 = 10181) (by norm_num)
theorem B1147733 : Blo 507795 1147733 := bbase (se 9 (by rfl) ⟨3362, by rfl⟩ : syracuseStep 1147733 = 6725) (by norm_num)
theorem B983909 : Blo 507795 983909 := bbase (se 4 (by rfl) ⟨92241, by rfl⟩ : syracuseStep 983909 = 184483) (by norm_num)
theorem B10617749 : Blo 507795 10617749 := bbase (se 6 (by rfl) ⟨248853, by rfl⟩ : syracuseStep 10617749 = 497707) (by norm_num)
theorem B1147805 : Blo 507795 1147805 := bbase (se 3 (by rfl) ⟨215213, by rfl⟩ : syracuseStep 1147805 = 430427) (by norm_num)
theorem B1835941 : Blo 507795 1835941 := bbase (se 4 (by rfl) ⟨172119, by rfl⟩ : syracuseStep 1835941 = 344239) (by norm_num)
theorem B918461 : Blo 507795 918461 := bbase (se 3 (by rfl) ⟨172211, by rfl⟩ : syracuseStep 918461 = 344423) (by norm_num)
theorem B9765845 : Blo 507795 9765845 := bbase (se 7 (by rfl) ⟨114443, by rfl⟩ : syracuseStep 9765845 = 228887) (by norm_num)
theorem B1147877 : Blo 507795 1147877 := bbase (se 4 (by rfl) ⟨107613, by rfl⟩ : syracuseStep 1147877 = 215227) (by norm_num)
theorem B1147949 : Blo 507795 1147949 := bbase (se 3 (by rfl) ⟨215240, by rfl⟩ : syracuseStep 1147949 = 430481) (by norm_num)
theorem B754741 : Blo 507795 754741 := bbase (se 5 (by rfl) ⟨35378, by rfl⟩ : syracuseStep 754741 = 70757) (by norm_num)
theorem B1148021 : Blo 507795 1148021 := bbase (se 5 (by rfl) ⟨53813, by rfl⟩ : syracuseStep 1148021 = 107627) (by norm_num)
theorem B3671189 : Blo 507795 3671189 := bbase (se 6 (by rfl) ⟨86043, by rfl⟩ : syracuseStep 3671189 = 172087) (by norm_num)
theorem B1148093 : Blo 507795 1148093 := bbase (se 3 (by rfl) ⟨215267, by rfl⟩ : syracuseStep 1148093 = 430535) (by norm_num)
theorem B2589893 : Blo 507795 2589893 := bbase (se 4 (by rfl) ⟨242802, by rfl⟩ : syracuseStep 2589893 = 485605) (by norm_num)
theorem B1148165 : Blo 507795 1148165 := bbase (se 4 (by rfl) ⟨107640, by rfl⟩ : syracuseStep 1148165 = 215281) (by norm_num)
theorem B1377605 : Blo 507795 1377605 := bbase (se 4 (by rfl) ⟨129150, by rfl⟩ : syracuseStep 1377605 = 258301) (by norm_num)
theorem B1148237 : Blo 507795 1148237 := bbase (se 3 (by rfl) ⟨215294, by rfl⟩ : syracuseStep 1148237 = 430589) (by norm_num)
theorem B1148309 : Blo 507795 1148309 := bbase (se 6 (by rfl) ⟨26913, by rfl⟩ : syracuseStep 1148309 = 53827) (by norm_num)
theorem B1148381 : Blo 507795 1148381 := bbase (se 3 (by rfl) ⟨215321, by rfl⟩ : syracuseStep 1148381 = 430643) (by norm_num)
theorem B1148453 : Blo 507795 1148453 := bbase (se 4 (by rfl) ⟨107667, by rfl⟩ : syracuseStep 1148453 = 215335) (by norm_num)
theorem B919117 : Blo 507795 919117 := bbase (se 3 (by rfl) ⟨172334, by rfl⟩ : syracuseStep 919117 = 344669) (by norm_num)
theorem B1148525 : Blo 507795 1148525 := bbase (se 3 (by rfl) ⟨215348, by rfl⟩ : syracuseStep 1148525 = 430697) (by norm_num)
theorem B919181 : Blo 507795 919181 := bbase (se 3 (by rfl) ⟨172346, by rfl⟩ : syracuseStep 919181 = 344693) (by norm_num)
theorem B1148597 : Blo 507795 1148597 := bbase (se 5 (by rfl) ⟨53840, by rfl⟩ : syracuseStep 1148597 = 107681) (by norm_num)
theorem B1312453 : Blo 507795 1312453 := bbase (se 4 (by rfl) ⟨123042, by rfl⟩ : syracuseStep 1312453 = 246085) (by norm_num)
theorem B886493 : Blo 507795 886493 := bbase (se 3 (by rfl) ⟨166217, by rfl⟩ : syracuseStep 886493 = 332435) (by norm_num)
theorem B1148669 : Blo 507795 1148669 := bbase (se 3 (by rfl) ⟨215375, by rfl⟩ : syracuseStep 1148669 = 430751) (by norm_num)
theorem B1148741 : Blo 507795 1148741 := bbase (se 4 (by rfl) ⟨107694, by rfl⟩ : syracuseStep 1148741 = 215389) (by norm_num)
theorem B1148813 : Blo 507795 1148813 := bbase (se 3 (by rfl) ⟨215402, by rfl⟩ : syracuseStep 1148813 = 430805) (by norm_num)
theorem B3475349 : Blo 507795 3475349 := bbase (se 6 (by rfl) ⟨81453, by rfl⟩ : syracuseStep 3475349 = 162907) (by norm_num)
theorem B1148885 : Blo 507795 1148885 := bbase (se 7 (by rfl) ⟨13463, by rfl⟩ : syracuseStep 1148885 = 26927) (by norm_num)
theorem B690133 : Blo 507795 690133 := bbase (se 7 (by rfl) ⟨8087, by rfl⟩ : syracuseStep 690133 = 16175) (by norm_num)
theorem B1148957 : Blo 507795 1148957 := bbase (se 3 (by rfl) ⟨215429, by rfl⟩ : syracuseStep 1148957 = 430859) (by norm_num)
theorem B1149029 : Blo 507795 1149029 := bbase (se 4 (by rfl) ⟨107721, by rfl⟩ : syracuseStep 1149029 = 215443) (by norm_num)
theorem B1181821 : Blo 507795 1181821 := bbase (se 3 (by rfl) ⟨221591, by rfl⟩ : syracuseStep 1181821 = 443183) (by norm_num)
theorem B5376149 : Blo 507795 5376149 := bbase (se 6 (by rfl) ⟨126003, by rfl⟩ : syracuseStep 5376149 = 252007) (by norm_num)
theorem B1149101 : Blo 507795 1149101 := bbase (se 3 (by rfl) ⟨215456, by rfl⟩ : syracuseStep 1149101 = 430913) (by norm_num)
theorem B1149173 : Blo 507795 1149173 := bbase (se 5 (by rfl) ⟨53867, by rfl⟩ : syracuseStep 1149173 = 107735) (by norm_num)
theorem B4131125 : Blo 507795 4131125 := bbase (se 5 (by rfl) ⟨193646, by rfl⟩ : syracuseStep 4131125 = 387293) (by norm_num)
theorem B1149245 : Blo 507795 1149245 := bbase (se 3 (by rfl) ⟨215483, by rfl⟩ : syracuseStep 1149245 = 430967) (by norm_num)
theorem B3869045 : Blo 507795 3869045 := bbase (se 5 (by rfl) ⟨181361, by rfl⟩ : syracuseStep 3869045 = 362723) (by norm_num)
theorem B1149317 : Blo 507795 1149317 := bbase (se 4 (by rfl) ⟨107748, by rfl⟩ : syracuseStep 1149317 = 215497) (by norm_num)
theorem B2329013 : Blo 507795 2329013 := bbase (se 5 (by rfl) ⟨109172, by rfl⟩ : syracuseStep 2329013 = 218345) (by norm_num)
theorem B1149389 : Blo 507795 1149389 := bbase (se 3 (by rfl) ⟨215510, by rfl⟩ : syracuseStep 1149389 = 431021) (by norm_num)
theorem B1935845 : Blo 507795 1935845 := bbase (se 4 (by rfl) ⟨181485, by rfl⟩ : syracuseStep 1935845 = 362971) (by norm_num)
theorem B1149461 : Blo 507795 1149461 := bbase (se 6 (by rfl) ⟨26940, by rfl⟩ : syracuseStep 1149461 = 53881) (by norm_num)
theorem B1149533 : Blo 507795 1149533 := bbase (se 3 (by rfl) ⟨215537, by rfl⟩ : syracuseStep 1149533 = 431075) (by norm_num)
theorem B1149605 : Blo 507795 1149605 := bbase (se 4 (by rfl) ⟨107775, by rfl⟩ : syracuseStep 1149605 = 215551) (by norm_num)
theorem B1149677 : Blo 507795 1149677 := bbase (se 3 (by rfl) ⟨215564, by rfl⟩ : syracuseStep 1149677 = 431129) (by norm_num)
theorem B1936133 : Blo 507795 1936133 := bbase (se 4 (by rfl) ⟨181512, by rfl⟩ : syracuseStep 1936133 = 363025) (by norm_num)
theorem B1149749 : Blo 507795 1149749 := bbase (se 5 (by rfl) ⟨53894, by rfl⟩ : syracuseStep 1149749 = 107789) (by norm_num)
theorem B723829 : Blo 507795 723829 := bbase (se 5 (by rfl) ⟨33929, by rfl⟩ : syracuseStep 723829 = 67859) (by norm_num)
theorem B1149821 : Blo 507795 1149821 := bbase (se 3 (by rfl) ⟨215591, by rfl⟩ : syracuseStep 1149821 = 431183) (by norm_num)
theorem B560017 : Blo 507795 560017 := bbase (se 2 (by rfl) ⟨210006, by rfl⟩ : syracuseStep 560017 = 420013) (by norm_num)
theorem B1149893 : Blo 507795 1149893 := bbase (se 4 (by rfl) ⟨107802, by rfl⟩ : syracuseStep 1149893 = 215605) (by norm_num)
theorem B1149965 : Blo 507795 1149965 := bbase (se 3 (by rfl) ⟨215618, by rfl⟩ : syracuseStep 1149965 = 431237) (by norm_num)
theorem B1150037 : Blo 507795 1150037 := bbase (se 8 (by rfl) ⟨6738, by rfl⟩ : syracuseStep 1150037 = 13477) (by norm_num)
theorem B1084565 : Blo 507795 1084565 := bbase (se 6 (by rfl) ⟨25419, by rfl⟩ : syracuseStep 1084565 = 50839) (by norm_num)
theorem B1150109 : Blo 507795 1150109 := bbase (se 3 (by rfl) ⟨215645, by rfl⟩ : syracuseStep 1150109 = 431291) (by norm_num)
theorem B1150181 : Blo 507795 1150181 := bbase (se 4 (by rfl) ⟨107829, by rfl⟩ : syracuseStep 1150181 = 215659) (by norm_num)
theorem B1150253 : Blo 507795 1150253 := bbase (se 3 (by rfl) ⟨215672, by rfl⟩ : syracuseStep 1150253 = 431345) (by norm_num)
theorem B691517 : Blo 507795 691517 := bbase (se 3 (by rfl) ⟨129659, by rfl⟩ : syracuseStep 691517 = 259319) (by norm_num)
theorem B1150325 : Blo 507795 1150325 := bbase (se 5 (by rfl) ⟨53921, by rfl⟩ : syracuseStep 1150325 = 107843) (by norm_num)
theorem B1150397 : Blo 507795 1150397 := bbase (se 3 (by rfl) ⟨215699, by rfl⟩ : syracuseStep 1150397 = 431399) (by norm_num)
theorem B724421 : Blo 507795 724421 := bbase (se 4 (by rfl) ⟨67914, by rfl⟩ : syracuseStep 724421 = 135829) (by norm_num)
theorem B1150469 : Blo 507795 1150469 := bbase (se 4 (by rfl) ⟨107856, by rfl⟩ : syracuseStep 1150469 = 215713) (by norm_num)
theorem B724501 : Blo 507795 724501 := bbase (se 6 (by rfl) ⟨16980, by rfl⟩ : syracuseStep 724501 = 33961) (by norm_num)
theorem B1150541 : Blo 507795 1150541 := bbase (se 3 (by rfl) ⟨215726, by rfl⟩ : syracuseStep 1150541 = 431453) (by norm_num)
theorem B724621 : Blo 507795 724621 := bbase (se 3 (by rfl) ⟨135866, by rfl⟩ : syracuseStep 724621 = 271733) (by norm_num)
theorem B1150613 : Blo 507795 1150613 := bbase (se 6 (by rfl) ⟨26967, by rfl⟩ : syracuseStep 1150613 = 53935) (by norm_num)
theorem B1150685 : Blo 507795 1150685 := bbase (se 3 (by rfl) ⟨215753, by rfl⟩ : syracuseStep 1150685 = 431507) (by norm_num)
theorem B724717 : Blo 507795 724717 := bbase (se 3 (by rfl) ⟨135884, by rfl⟩ : syracuseStep 724717 = 271769) (by norm_num)
theorem B1085197 : Blo 507795 1085197 := bbase (se 3 (by rfl) ⟨203474, by rfl⟩ : syracuseStep 1085197 = 406949) (by norm_num)
theorem B1150757 : Blo 507795 1150757 := bbase (se 4 (by rfl) ⟨107883, by rfl⟩ : syracuseStep 1150757 = 215767) (by norm_num)
theorem B1150829 : Blo 507795 1150829 := bbase (se 3 (by rfl) ⟨215780, by rfl⟩ : syracuseStep 1150829 = 431561) (by norm_num)
theorem B1937317 : Blo 507795 1937317 := bbase (se 4 (by rfl) ⟨181623, by rfl⟩ : syracuseStep 1937317 = 363247) (by norm_num)
theorem B1150901 : Blo 507795 1150901 := bbase (se 5 (by rfl) ⟨53948, by rfl⟩ : syracuseStep 1150901 = 107897) (by norm_num)
theorem B1150973 : Blo 507795 1150973 := bbase (se 3 (by rfl) ⟨215807, by rfl⟩ : syracuseStep 1150973 = 431615) (by norm_num)
theorem B1151045 : Blo 507795 1151045 := bbase (se 4 (by rfl) ⟨107910, by rfl⟩ : syracuseStep 1151045 = 215821) (by norm_num)
theorem B1151117 : Blo 507795 1151117 := bbase (se 3 (by rfl) ⟨215834, by rfl⟩ : syracuseStep 1151117 = 431669) (by norm_num)
theorem B1937621 : Blo 507795 1937621 := bbase (se 7 (by rfl) ⟨22706, by rfl⟩ : syracuseStep 1937621 = 45413) (by norm_num)
theorem B1151189 : Blo 507795 1151189 := bbase (se 7 (by rfl) ⟨13490, by rfl⟩ : syracuseStep 1151189 = 26981) (by norm_num)
theorem B725213 : Blo 507795 725213 := bbase (se 3 (by rfl) ⟨135977, by rfl⟩ : syracuseStep 725213 = 271955) (by norm_num)
theorem B1151261 : Blo 507795 1151261 := bbase (se 3 (by rfl) ⟨215861, by rfl⟩ : syracuseStep 1151261 = 431723) (by norm_num)
theorem B19796309 : Blo 507795 19796309 := bbase (se 10 (by rfl) ⟨28998, by rfl⟩ : syracuseStep 19796309 = 57997) (by norm_num)
theorem B1446245 : Blo 507795 1446245 := bbase (se 4 (by rfl) ⟨135585, by rfl⟩ : syracuseStep 1446245 = 271171) (by norm_num)
theorem B1151333 : Blo 507795 1151333 := bbase (se 4 (by rfl) ⟨107937, by rfl⟩ : syracuseStep 1151333 = 215875) (by norm_num)
theorem B1151405 : Blo 507795 1151405 := bbase (se 3 (by rfl) ⟨215888, by rfl⟩ : syracuseStep 1151405 = 431777) (by norm_num)
theorem B1151477 : Blo 507795 1151477 := bbase (se 5 (by rfl) ⟨53975, by rfl⟩ : syracuseStep 1151477 = 107951) (by norm_num)
theorem B1086085 : Blo 507795 1086085 := bbase (se 4 (by rfl) ⟨101820, by rfl⟩ : syracuseStep 1086085 = 203641) (by norm_num)
theorem B1086205 : Blo 507795 1086205 := bbase (se 3 (by rfl) ⟨203663, by rfl⟩ : syracuseStep 1086205 = 407327) (by norm_num)
theorem B725765 : Blo 507795 725765 := bbase (se 4 (by rfl) ⟨68040, by rfl⟩ : syracuseStep 725765 = 136081) (by norm_num)
theorem B7344917 : Blo 507795 7344917 := bbase (se 6 (by rfl) ⟨172146, by rfl⟩ : syracuseStep 7344917 = 344293) (by norm_num)
theorem B1545013 : Blo 507795 1545013 := bbase (se 5 (by rfl) ⟨72422, by rfl⟩ : syracuseStep 1545013 = 144845) (by norm_num)
theorem B856973 : Blo 507795 856973 := bbase (se 3 (by rfl) ⟨160682, by rfl⟩ : syracuseStep 856973 = 321365) (by norm_num)
theorem B1086461 : Blo 507795 1086461 := bbase (se 3 (by rfl) ⟨203711, by rfl⟩ : syracuseStep 1086461 = 407423) (by norm_num)
theorem B857101 : Blo 507795 857101 := bbase (se 3 (by rfl) ⟨160706, by rfl⟩ : syracuseStep 857101 = 321413) (by norm_num)
theorem B1381445 : Blo 507795 1381445 := bbase (se 4 (by rfl) ⟨129510, by rfl⟩ : syracuseStep 1381445 = 259021) (by norm_num)
theorem B1446997 : Blo 507795 1446997 := bbase (se 8 (by rfl) ⟨8478, by rfl⟩ : syracuseStep 1446997 = 16957) (by norm_num)
theorem B857189 : Blo 507795 857189 := bbase (se 4 (by rfl) ⟨80361, by rfl⟩ : syracuseStep 857189 = 160723) (by norm_num)
theorem B2069621 : Blo 507795 2069621 := bbase (se 5 (by rfl) ⟨97013, by rfl⟩ : syracuseStep 2069621 = 194027) (by norm_num)
theorem B857317 : Blo 507795 857317 := bbase (se 4 (by rfl) ⟨80373, by rfl⟩ : syracuseStep 857317 = 160747) (by norm_num)
theorem B857405 : Blo 507795 857405 := bbase (se 3 (by rfl) ⟨160763, by rfl⟩ : syracuseStep 857405 = 321527) (by norm_num)
theorem B857533 : Blo 507795 857533 := bbase (se 3 (by rfl) ⟨160787, by rfl⟩ : syracuseStep 857533 = 321575) (by norm_num)
theorem B726517 : Blo 507795 726517 := bbase (se 5 (by rfl) ⟨34055, by rfl⟩ : syracuseStep 726517 = 68111) (by norm_num)
theorem B1381877 : Blo 507795 1381877 := bbase (se 5 (by rfl) ⟨64775, by rfl⟩ : syracuseStep 1381877 = 129551) (by norm_num)
theorem B857621 : Blo 507795 857621 := bbase (se 6 (by rfl) ⟨20100, by rfl⟩ : syracuseStep 857621 = 40201) (by norm_num)
theorem B857749 : Blo 507795 857749 := bbase (se 6 (by rfl) ⟨20103, by rfl⟩ : syracuseStep 857749 = 40207) (by norm_num)
theorem B857837 : Blo 507795 857837 := bbase (se 3 (by rfl) ⟨160844, by rfl⟩ : syracuseStep 857837 = 321689) (by norm_num)
theorem B5510933 : Blo 507795 5510933 := bbase (se 6 (by rfl) ⟨129162, by rfl⟩ : syracuseStep 5510933 = 258325) (by norm_num)
theorem B857965 : Blo 507795 857965 := bbase (se 3 (by rfl) ⟨160868, by rfl⟩ : syracuseStep 857965 = 321737) (by norm_num)
theorem B1087349 : Blo 507795 1087349 := bbase (se 5 (by rfl) ⟨50969, by rfl⟩ : syracuseStep 1087349 = 101939) (by norm_num)
theorem B858053 : Blo 507795 858053 := bbase (se 4 (by rfl) ⟨80442, by rfl⟩ : syracuseStep 858053 = 160885) (by norm_num)
theorem B13277141 : Blo 507795 13277141 := bbase (se 7 (by rfl) ⟨155591, by rfl⟩ : syracuseStep 13277141 = 311183) (by norm_num)
theorem B858181 : Blo 507795 858181 := bbase (se 4 (by rfl) ⟨80454, by rfl⟩ : syracuseStep 858181 = 160909) (by norm_num)
theorem B1087589 : Blo 507795 1087589 := bbase (se 4 (by rfl) ⟨101961, by rfl⟩ : syracuseStep 1087589 = 203923) (by norm_num)
theorem B858269 : Blo 507795 858269 := bbase (se 3 (by rfl) ⟨160925, by rfl⟩ : syracuseStep 858269 = 321851) (by norm_num)
theorem B727309 : Blo 507795 727309 := bbase (se 3 (by rfl) ⟨136370, by rfl⟩ : syracuseStep 727309 = 272741) (by norm_num)
theorem B1939733 : Blo 507795 1939733 := bbase (se 6 (by rfl) ⟨45462, by rfl⟩ : syracuseStep 1939733 = 90925) (by norm_num)
theorem B858397 : Blo 507795 858397 := bbase (se 3 (by rfl) ⟨160949, by rfl⟩ : syracuseStep 858397 = 321899) (by norm_num)
theorem B858485 : Blo 507795 858485 := bbase (se 5 (by rfl) ⟨40241, by rfl⟩ : syracuseStep 858485 = 80483) (by norm_num)
theorem B858613 : Blo 507795 858613 := bbase (se 5 (by rfl) ⟨40247, by rfl⟩ : syracuseStep 858613 = 80495) (by norm_num)
theorem B1546789 : Blo 507795 1546789 := bbase (se 4 (by rfl) ⟨145011, by rfl⟩ : syracuseStep 1546789 = 290023) (by norm_num)
theorem B1940021 : Blo 507795 1940021 := bbase (se 5 (by rfl) ⟨90938, by rfl⟩ : syracuseStep 1940021 = 181877) (by norm_num)
theorem B858701 : Blo 507795 858701 := bbase (se 3 (by rfl) ⟨161006, by rfl⟩ : syracuseStep 858701 = 322013) (by norm_num)
theorem B1088093 : Blo 507795 1088093 := bbase (se 3 (by rfl) ⟨204017, by rfl⟩ : syracuseStep 1088093 = 408035) (by norm_num)
theorem B727645 : Blo 507795 727645 := bbase (se 3 (by rfl) ⟨136433, by rfl⟩ : syracuseStep 727645 = 272867) (by norm_num)
theorem B1088101 : Blo 507795 1088101 := bbase (se 4 (by rfl) ⟨102009, by rfl⟩ : syracuseStep 1088101 = 204019) (by norm_num)
theorem B858829 : Blo 507795 858829 := bbase (se 3 (by rfl) ⟨161030, by rfl⟩ : syracuseStep 858829 = 322061) (by norm_num)
theorem B858917 : Blo 507795 858917 := bbase (se 4 (by rfl) ⟨80523, by rfl⟩ : syracuseStep 858917 = 161047) (by norm_num)
theorem B727861 : Blo 507795 727861 := bbase (se 5 (by rfl) ⟨34118, by rfl⟩ : syracuseStep 727861 = 68237) (by norm_num)
theorem B1383269 : Blo 507795 1383269 := bbase (se 4 (by rfl) ⟨129681, by rfl⟩ : syracuseStep 1383269 = 259363) (by norm_num)
theorem B859045 : Blo 507795 859045 := bbase (se 4 (by rfl) ⟨80535, by rfl⟩ : syracuseStep 859045 = 161071) (by norm_num)
theorem B859133 : Blo 507795 859133 := bbase (se 3 (by rfl) ⟨161087, by rfl⟩ : syracuseStep 859133 = 322175) (by norm_num)
theorem B859261 : Blo 507795 859261 := bbase (se 3 (by rfl) ⟨161111, by rfl⟩ : syracuseStep 859261 = 322223) (by norm_num)
theorem B728237 : Blo 507795 728237 := bbase (se 3 (by rfl) ⟨136544, by rfl⟩ : syracuseStep 728237 = 273089) (by norm_num)
theorem B859349 : Blo 507795 859349 := bbase (se 7 (by rfl) ⟨10070, by rfl⟩ : syracuseStep 859349 = 20141) (by norm_num)
theorem B1285429 : Blo 507795 1285429 := bbase (se 5 (by rfl) ⟨60254, by rfl⟩ : syracuseStep 1285429 = 120509) (by norm_num)
theorem B859477 : Blo 507795 859477 := bbase (se 11 (by rfl) ⟨629, by rfl⟩ : syracuseStep 859477 = 1259) (by norm_num)
theorem B1285541 : Blo 507795 1285541 := bbase (se 4 (by rfl) ⟨120519, by rfl⟩ : syracuseStep 1285541 = 241039) (by norm_num)
theorem B859565 : Blo 507795 859565 := bbase (se 3 (by rfl) ⟨161168, by rfl⟩ : syracuseStep 859565 = 322337) (by norm_num)
theorem B2334197 : Blo 507795 2334197 := bbase (se 5 (by rfl) ⟨109415, by rfl⟩ : syracuseStep 2334197 = 218831) (by norm_num)
theorem B859693 : Blo 507795 859693 := bbase (se 3 (by rfl) ⟨161192, by rfl⟩ : syracuseStep 859693 = 322385) (by norm_num)
theorem B1121861 : Blo 507795 1121861 := bbase (se 4 (by rfl) ⟨105174, by rfl⟩ : syracuseStep 1121861 = 210349) (by norm_num)
theorem B1285733 : Blo 507795 1285733 := bbase (se 4 (by rfl) ⟨120537, by rfl⟩ : syracuseStep 1285733 = 241075) (by norm_num)
theorem B859781 : Blo 507795 859781 := bbase (se 4 (by rfl) ⟨80604, by rfl⟩ : syracuseStep 859781 = 161209) (by norm_num)
theorem B1089229 : Blo 507795 1089229 := bbase (se 3 (by rfl) ⟨204230, by rfl⟩ : syracuseStep 1089229 = 408461) (by norm_num)
theorem B1220309 : Blo 507795 1220309 := bbase (se 7 (by rfl) ⟨14300, by rfl⟩ : syracuseStep 1220309 = 28601) (by norm_num)
theorem B1941205 : Blo 507795 1941205 := bbase (se 7 (by rfl) ⟨22748, by rfl⟩ : syracuseStep 1941205 = 45497) (by norm_num)
theorem B2072309 : Blo 507795 2072309 := bbase (se 5 (by rfl) ⟨97139, by rfl⟩ : syracuseStep 2072309 = 194279) (by norm_num)
theorem B859909 : Blo 507795 859909 := bbase (se 4 (by rfl) ⟨80616, by rfl⟩ : syracuseStep 859909 = 161233) (by norm_num)
theorem B4726613 : Blo 507795 4726613 := bbase (se 9 (by rfl) ⟨13847, by rfl⟩ : syracuseStep 4726613 = 27695) (by norm_num)
theorem B761693 : Blo 507795 761693 := bbase (se 3 (by rfl) ⟨142817, by rfl⟩ : syracuseStep 761693 = 285635) (by norm_num)
theorem B859997 : Blo 507795 859997 := bbase (se 3 (by rfl) ⟨161249, by rfl⟩ : syracuseStep 859997 = 322499) (by norm_num)
theorem B761717 : Blo 507795 761717 := bbase (se 5 (by rfl) ⟨35705, by rfl⟩ : syracuseStep 761717 = 71411) (by norm_num)
theorem B1449845 : Blo 507795 1449845 := bbase (se 5 (by rfl) ⟨67961, by rfl⟩ : syracuseStep 1449845 = 135923) (by norm_num)
theorem B761741 : Blo 507795 761741 := bbase (se 3 (by rfl) ⟨142826, by rfl⟩ : syracuseStep 761741 = 285653) (by norm_num)
theorem B1220501 : Blo 507795 1220501 := bbase (se 6 (by rfl) ⟨28605, by rfl⟩ : syracuseStep 1220501 = 57211) (by norm_num)
theorem B761765 : Blo 507795 761765 := bbase (se 4 (by rfl) ⟨71415, by rfl⟩ : syracuseStep 761765 = 142831) (by norm_num)
theorem B761789 : Blo 507795 761789 := bbase (se 3 (by rfl) ⟨142835, by rfl⟩ : syracuseStep 761789 = 285671) (by norm_num)
theorem B1286077 : Blo 507795 1286077 := bbase (se 3 (by rfl) ⟨241139, by rfl⟩ : syracuseStep 1286077 = 482279) (by norm_num)
theorem B761813 : Blo 507795 761813 := bbase (se 7 (by rfl) ⟨8927, by rfl⟩ : syracuseStep 761813 = 17855) (by norm_num)
theorem B860125 : Blo 507795 860125 := bbase (se 3 (by rfl) ⟨161273, by rfl⟩ : syracuseStep 860125 = 322547) (by norm_num)
theorem B761837 : Blo 507795 761837 := bbase (se 3 (by rfl) ⟨142844, by rfl⟩ : syracuseStep 761837 = 285689) (by norm_num)
theorem B1220597 : Blo 507795 1220597 := bbase (se 5 (by rfl) ⟨57215, by rfl⟩ : syracuseStep 1220597 = 114431) (by norm_num)
theorem B761861 : Blo 507795 761861 := bbase (se 4 (by rfl) ⟨71424, by rfl⟩ : syracuseStep 761861 = 142849) (by norm_num)
theorem B1941509 : Blo 507795 1941509 := bbase (se 4 (by rfl) ⟨182016, by rfl⟩ : syracuseStep 1941509 = 364033) (by norm_num)
theorem B761885 : Blo 507795 761885 := bbase (se 3 (by rfl) ⟨142853, by rfl⟩ : syracuseStep 761885 = 285707) (by norm_num)
theorem B1286189 : Blo 507795 1286189 := bbase (se 3 (by rfl) ⟨241160, by rfl⟩ : syracuseStep 1286189 = 482321) (by norm_num)
theorem B761909 : Blo 507795 761909 := bbase (se 5 (by rfl) ⟨35714, by rfl⟩ : syracuseStep 761909 = 71429) (by norm_num)
theorem B860213 : Blo 507795 860213 := bbase (se 5 (by rfl) ⟨40322, by rfl⟩ : syracuseStep 860213 = 80645) (by norm_num)
theorem B1089605 : Blo 507795 1089605 := bbase (se 4 (by rfl) ⟨102150, by rfl⟩ : syracuseStep 1089605 = 204301) (by norm_num)
theorem B761933 : Blo 507795 761933 := bbase (se 3 (by rfl) ⟨142862, by rfl⟩ : syracuseStep 761933 = 285725) (by norm_num)
theorem B761957 : Blo 507795 761957 := bbase (se 4 (by rfl) ⟨71433, by rfl⟩ : syracuseStep 761957 = 142867) (by norm_num)
theorem B761981 : Blo 507795 761981 := bbase (se 3 (by rfl) ⟨142871, by rfl⟩ : syracuseStep 761981 = 285743) (by norm_num)
theorem B762005 : Blo 507795 762005 := bbase (se 6 (by rfl) ⟨17859, by rfl⟩ : syracuseStep 762005 = 35719) (by norm_num)
theorem B762029 : Blo 507795 762029 := bbase (se 3 (by rfl) ⟨142880, by rfl⟩ : syracuseStep 762029 = 285761) (by norm_num)
theorem B860341 : Blo 507795 860341 := bbase (se 5 (by rfl) ⟨40328, by rfl⟩ : syracuseStep 860341 = 80657) (by norm_num)
theorem B762053 : Blo 507795 762053 := bbase (se 4 (by rfl) ⟨71442, by rfl⟩ : syracuseStep 762053 = 142885) (by norm_num)
theorem B762077 : Blo 507795 762077 := bbase (se 3 (by rfl) ⟨142889, by rfl⟩ : syracuseStep 762077 = 285779) (by norm_num)
theorem B1286381 : Blo 507795 1286381 := bbase (se 3 (by rfl) ⟨241196, by rfl⟩ : syracuseStep 1286381 = 482393) (by norm_num)
theorem B762101 : Blo 507795 762101 := bbase (se 5 (by rfl) ⟨35723, by rfl⟩ : syracuseStep 762101 = 71447) (by norm_num)
theorem B762125 : Blo 507795 762125 := bbase (se 3 (by rfl) ⟨142898, by rfl⟩ : syracuseStep 762125 = 285797) (by norm_num)
theorem B860429 : Blo 507795 860429 := bbase (se 3 (by rfl) ⟨161330, by rfl⟩ : syracuseStep 860429 = 322661) (by norm_num)
theorem B762149 : Blo 507795 762149 := bbase (se 4 (by rfl) ⟨71451, by rfl⟩ : syracuseStep 762149 = 142903) (by norm_num)
theorem B762173 : Blo 507795 762173 := bbase (se 3 (by rfl) ⟨142907, by rfl⟩ : syracuseStep 762173 = 285815) (by norm_num)
theorem B762197 : Blo 507795 762197 := bbase (se 10 (by rfl) ⟨1116, by rfl⟩ : syracuseStep 762197 = 2233) (by norm_num)
theorem B762221 : Blo 507795 762221 := bbase (se 3 (by rfl) ⟨142916, by rfl⟩ : syracuseStep 762221 = 285833) (by norm_num)
theorem B762245 : Blo 507795 762245 := bbase (se 4 (by rfl) ⟨71460, by rfl⟩ : syracuseStep 762245 = 142921) (by norm_num)
theorem B860557 : Blo 507795 860557 := bbase (se 3 (by rfl) ⟨161354, by rfl⟩ : syracuseStep 860557 = 322709) (by norm_num)
theorem B762269 : Blo 507795 762269 := bbase (se 3 (by rfl) ⟨142925, by rfl⟩ : syracuseStep 762269 = 285851) (by norm_num)
theorem B762293 : Blo 507795 762293 := bbase (se 5 (by rfl) ⟨35732, by rfl⟩ : syracuseStep 762293 = 71465) (by norm_num)
theorem B762317 : Blo 507795 762317 := bbase (se 3 (by rfl) ⟨142934, by rfl⟩ : syracuseStep 762317 = 285869) (by norm_num)
theorem B762341 : Blo 507795 762341 := bbase (se 4 (by rfl) ⟨71469, by rfl⟩ : syracuseStep 762341 = 142939) (by norm_num)
theorem B860645 : Blo 507795 860645 := bbase (se 4 (by rfl) ⟨80685, by rfl⟩ : syracuseStep 860645 = 161371) (by norm_num)
theorem B762365 : Blo 507795 762365 := bbase (se 3 (by rfl) ⟨142943, by rfl⟩ : syracuseStep 762365 = 285887) (by norm_num)
theorem B762389 : Blo 507795 762389 := bbase (se 6 (by rfl) ⟨17868, by rfl⟩ : syracuseStep 762389 = 35737) (by norm_num)
theorem B762413 : Blo 507795 762413 := bbase (se 3 (by rfl) ⟨142952, by rfl⟩ : syracuseStep 762413 = 285905) (by norm_num)
theorem B762437 : Blo 507795 762437 := bbase (se 4 (by rfl) ⟨71478, by rfl⟩ : syracuseStep 762437 = 142957) (by norm_num)
theorem B1286725 : Blo 507795 1286725 := bbase (se 4 (by rfl) ⟨120630, by rfl⟩ : syracuseStep 1286725 = 241261) (by norm_num)
theorem B5218901 : Blo 507795 5218901 := bbase (se 8 (by rfl) ⟨30579, by rfl⟩ : syracuseStep 5218901 = 61159) (by norm_num)
theorem B762461 : Blo 507795 762461 := bbase (se 3 (by rfl) ⟨142961, by rfl⟩ : syracuseStep 762461 = 285923) (by norm_num)
theorem B860773 : Blo 507795 860773 := bbase (se 4 (by rfl) ⟨80697, by rfl⟩ : syracuseStep 860773 = 161395) (by norm_num)
theorem B762485 : Blo 507795 762485 := bbase (se 5 (by rfl) ⟨35741, by rfl⟩ : syracuseStep 762485 = 71483) (by norm_num)
theorem B762509 : Blo 507795 762509 := bbase (se 3 (by rfl) ⟨142970, by rfl⟩ : syracuseStep 762509 = 285941) (by norm_num)
theorem B762533 : Blo 507795 762533 := bbase (se 4 (by rfl) ⟨71487, by rfl⟩ : syracuseStep 762533 = 142975) (by norm_num)
theorem B1286837 : Blo 507795 1286837 := bbase (se 5 (by rfl) ⟨60320, by rfl⟩ : syracuseStep 1286837 = 120641) (by norm_num)
theorem B2761397 : Blo 507795 2761397 := bbase (se 5 (by rfl) ⟨129440, by rfl⟩ : syracuseStep 2761397 = 258881) (by norm_num)
theorem B762557 : Blo 507795 762557 := bbase (se 3 (by rfl) ⟨142979, by rfl⟩ : syracuseStep 762557 = 285959) (by norm_num)
theorem B860861 : Blo 507795 860861 := bbase (se 3 (by rfl) ⟨161411, by rfl⟩ : syracuseStep 860861 = 322823) (by norm_num)
theorem B762581 : Blo 507795 762581 := bbase (se 7 (by rfl) ⟨8936, by rfl⟩ : syracuseStep 762581 = 17873) (by norm_num)
theorem B762605 : Blo 507795 762605 := bbase (se 3 (by rfl) ⟨142988, by rfl⟩ : syracuseStep 762605 = 285977) (by norm_num)
theorem B762629 : Blo 507795 762629 := bbase (se 4 (by rfl) ⟨71496, by rfl⟩ : syracuseStep 762629 = 142993) (by norm_num)
theorem B828173 : Blo 507795 828173 := bbase (se 3 (by rfl) ⟨155282, by rfl⟩ : syracuseStep 828173 = 310565) (by norm_num)
theorem B762653 : Blo 507795 762653 := bbase (se 3 (by rfl) ⟨142997, by rfl⟩ : syracuseStep 762653 = 285995) (by norm_num)
theorem B762677 : Blo 507795 762677 := bbase (se 5 (by rfl) ⟨35750, by rfl⟩ : syracuseStep 762677 = 71501) (by norm_num)
theorem B860989 : Blo 507795 860989 := bbase (se 3 (by rfl) ⟨161435, by rfl⟩ : syracuseStep 860989 = 322871) (by norm_num)
theorem B762701 : Blo 507795 762701 := bbase (se 3 (by rfl) ⟨143006, by rfl⟩ : syracuseStep 762701 = 286013) (by norm_num)
theorem B762725 : Blo 507795 762725 := bbase (se 4 (by rfl) ⟨71505, by rfl⟩ : syracuseStep 762725 = 143011) (by norm_num)
theorem B1287029 : Blo 507795 1287029 := bbase (se 5 (by rfl) ⟨60329, by rfl⟩ : syracuseStep 1287029 = 120659) (by norm_num)
theorem B762749 : Blo 507795 762749 := bbase (se 3 (by rfl) ⟨143015, by rfl⟩ : syracuseStep 762749 = 286031) (by norm_num)
theorem B664453 : Blo 507795 664453 := bbase (se 4 (by rfl) ⟨62292, by rfl⟩ : syracuseStep 664453 = 124585) (by norm_num)
theorem B762773 : Blo 507795 762773 := bbase (se 6 (by rfl) ⟨17877, by rfl⟩ : syracuseStep 762773 = 35755) (by norm_num)
theorem B861077 : Blo 507795 861077 := bbase (se 6 (by rfl) ⟨20181, by rfl⟩ : syracuseStep 861077 = 40363) (by norm_num)
theorem B762797 : Blo 507795 762797 := bbase (se 3 (by rfl) ⟨143024, by rfl⟩ : syracuseStep 762797 = 286049) (by norm_num)
theorem B762821 : Blo 507795 762821 := bbase (se 4 (by rfl) ⟨71514, by rfl⟩ : syracuseStep 762821 = 143029) (by norm_num)
theorem B4137941 : Blo 507795 4137941 := bbase (se 7 (by rfl) ⟨48491, by rfl⟩ : syracuseStep 4137941 = 96983) (by norm_num)
theorem B762845 : Blo 507795 762845 := bbase (se 3 (by rfl) ⟨143033, by rfl⟩ : syracuseStep 762845 = 286067) (by norm_num)
theorem B762869 : Blo 507795 762869 := bbase (se 5 (by rfl) ⟨35759, by rfl⟩ : syracuseStep 762869 = 71519) (by norm_num)
theorem B762893 : Blo 507795 762893 := bbase (se 3 (by rfl) ⟨143042, by rfl⟩ : syracuseStep 762893 = 286085) (by norm_num)
theorem B1451029 : Blo 507795 1451029 := bbase (se 6 (by rfl) ⟨34008, by rfl⟩ : syracuseStep 1451029 = 68017) (by norm_num)
theorem B861205 : Blo 507795 861205 := bbase (se 6 (by rfl) ⟨20184, by rfl⟩ : syracuseStep 861205 = 40369) (by norm_num)
theorem B762917 : Blo 507795 762917 := bbase (se 4 (by rfl) ⟨71523, by rfl⟩ : syracuseStep 762917 = 143047) (by norm_num)
theorem B762941 : Blo 507795 762941 := bbase (se 3 (by rfl) ⟨143051, by rfl⟩ : syracuseStep 762941 = 286103) (by norm_num)
theorem B762965 : Blo 507795 762965 := bbase (se 8 (by rfl) ⟨4470, by rfl⟩ : syracuseStep 762965 = 8941) (by norm_num)
theorem B762989 : Blo 507795 762989 := bbase (se 3 (by rfl) ⟨143060, by rfl⟩ : syracuseStep 762989 = 286121) (by norm_num)
theorem B861293 : Blo 507795 861293 := bbase (se 3 (by rfl) ⟨161492, by rfl⟩ : syracuseStep 861293 = 322985) (by norm_num)
theorem B763013 : Blo 507795 763013 := bbase (se 4 (by rfl) ⟨71532, by rfl⟩ : syracuseStep 763013 = 143065) (by norm_num)
theorem B763037 : Blo 507795 763037 := bbase (se 3 (by rfl) ⟨143069, by rfl⟩ : syracuseStep 763037 = 286139) (by norm_num)
theorem B763061 : Blo 507795 763061 := bbase (se 5 (by rfl) ⟨35768, by rfl⟩ : syracuseStep 763061 = 71537) (by norm_num)
theorem B1451189 : Blo 507795 1451189 := bbase (se 5 (by rfl) ⟨68024, by rfl⟩ : syracuseStep 1451189 = 136049) (by norm_num)
theorem B1287373 : Blo 507795 1287373 := bbase (se 3 (by rfl) ⟨241382, by rfl⟩ : syracuseStep 1287373 = 482765) (by norm_num)
theorem B763085 : Blo 507795 763085 := bbase (se 3 (by rfl) ⟨143078, by rfl⟩ : syracuseStep 763085 = 286157) (by norm_num)
theorem B763109 : Blo 507795 763109 := bbase (se 4 (by rfl) ⟨71541, by rfl⟩ : syracuseStep 763109 = 143083) (by norm_num)
theorem B861421 : Blo 507795 861421 := bbase (se 3 (by rfl) ⟨161516, by rfl⟩ : syracuseStep 861421 = 323033) (by norm_num)
theorem B763133 : Blo 507795 763133 := bbase (se 3 (by rfl) ⟨143087, by rfl⟩ : syracuseStep 763133 = 286175) (by norm_num)
theorem B763157 : Blo 507795 763157 := bbase (se 6 (by rfl) ⟨17886, by rfl⟩ : syracuseStep 763157 = 35773) (by norm_num)
theorem B763181 : Blo 507795 763181 := bbase (se 3 (by rfl) ⟨143096, by rfl⟩ : syracuseStep 763181 = 286193) (by norm_num)
theorem B1287485 : Blo 507795 1287485 := bbase (se 3 (by rfl) ⟨241403, by rfl⟩ : syracuseStep 1287485 = 482807) (by norm_num)
theorem B763205 : Blo 507795 763205 := bbase (se 4 (by rfl) ⟨71550, by rfl⟩ : syracuseStep 763205 = 143101) (by norm_num)
theorem B861509 : Blo 507795 861509 := bbase (se 4 (by rfl) ⟨80766, by rfl⟩ : syracuseStep 861509 = 161533) (by norm_num)
theorem B763229 : Blo 507795 763229 := bbase (se 3 (by rfl) ⟨143105, by rfl⟩ : syracuseStep 763229 = 286211) (by norm_num)
theorem B763253 : Blo 507795 763253 := bbase (se 5 (by rfl) ⟨35777, by rfl⟩ : syracuseStep 763253 = 71555) (by norm_num)
theorem B763277 : Blo 507795 763277 := bbase (se 3 (by rfl) ⟨143114, by rfl⟩ : syracuseStep 763277 = 286229) (by norm_num)
theorem B763301 : Blo 507795 763301 := bbase (se 4 (by rfl) ⟨71559, by rfl⟩ : syracuseStep 763301 = 143119) (by norm_num)
theorem B1451429 : Blo 507795 1451429 := bbase (se 4 (by rfl) ⟨136071, by rfl⟩ : syracuseStep 1451429 = 272143) (by norm_num)
theorem B763325 : Blo 507795 763325 := bbase (se 3 (by rfl) ⟨143123, by rfl⟩ : syracuseStep 763325 = 286247) (by norm_num)
theorem B861637 : Blo 507795 861637 := bbase (se 4 (by rfl) ⟨80778, by rfl⟩ : syracuseStep 861637 = 161557) (by norm_num)
theorem B763349 : Blo 507795 763349 := bbase (se 7 (by rfl) ⟨8945, by rfl⟩ : syracuseStep 763349 = 17891) (by norm_num)
theorem B763373 : Blo 507795 763373 := bbase (se 3 (by rfl) ⟨143132, by rfl⟩ : syracuseStep 763373 = 286265) (by norm_num)
theorem B1287677 : Blo 507795 1287677 := bbase (se 3 (by rfl) ⟨241439, by rfl⟩ : syracuseStep 1287677 = 482879) (by norm_num)
theorem B763397 : Blo 507795 763397 := bbase (se 4 (by rfl) ⟨71568, by rfl⟩ : syracuseStep 763397 = 143137) (by norm_num)
theorem B763421 : Blo 507795 763421 := bbase (se 3 (by rfl) ⟨143141, by rfl⟩ : syracuseStep 763421 = 286283) (by norm_num)
theorem B861725 : Blo 507795 861725 := bbase (se 3 (by rfl) ⟨161573, by rfl⟩ : syracuseStep 861725 = 323147) (by norm_num)
theorem B763445 : Blo 507795 763445 := bbase (se 5 (by rfl) ⟨35786, by rfl⟩ : syracuseStep 763445 = 71573) (by norm_num)
theorem B763469 : Blo 507795 763469 := bbase (se 3 (by rfl) ⟨143150, by rfl⟩ : syracuseStep 763469 = 286301) (by norm_num)
theorem B763493 : Blo 507795 763493 := bbase (se 4 (by rfl) ⟨71577, by rfl⟩ : syracuseStep 763493 = 143155) (by norm_num)
theorem B1451621 : Blo 507795 1451621 := bbase (se 4 (by rfl) ⟨136089, by rfl⟩ : syracuseStep 1451621 = 272179) (by norm_num)
theorem B763517 : Blo 507795 763517 := bbase (se 3 (by rfl) ⟨143159, by rfl⟩ : syracuseStep 763517 = 286319) (by norm_num)
theorem B763541 : Blo 507795 763541 := bbase (se 6 (by rfl) ⟨17895, by rfl⟩ : syracuseStep 763541 = 35791) (by norm_num)
theorem B861853 : Blo 507795 861853 := bbase (se 3 (by rfl) ⟨161597, by rfl⟩ : syracuseStep 861853 = 323195) (by norm_num)
theorem B2172581 : Blo 507795 2172581 := bbase (se 4 (by rfl) ⟨203679, by rfl⟩ : syracuseStep 2172581 = 407359) (by norm_num)
theorem B763565 : Blo 507795 763565 := bbase (se 3 (by rfl) ⟨143168, by rfl⟩ : syracuseStep 763565 = 286337) (by norm_num)
theorem B1091245 : Blo 507795 1091245 := bbase (se 3 (by rfl) ⟨204608, by rfl⟩ : syracuseStep 1091245 = 409217) (by norm_num)
theorem B763589 : Blo 507795 763589 := bbase (se 4 (by rfl) ⟨71586, by rfl⟩ : syracuseStep 763589 = 143173) (by norm_num)
theorem B763613 : Blo 507795 763613 := bbase (se 3 (by rfl) ⟨143177, by rfl⟩ : syracuseStep 763613 = 286355) (by norm_num)
theorem B763637 : Blo 507795 763637 := bbase (se 5 (by rfl) ⟨35795, by rfl⟩ : syracuseStep 763637 = 71591) (by norm_num)
theorem B861941 : Blo 507795 861941 := bbase (se 5 (by rfl) ⟨40403, by rfl⟩ : syracuseStep 861941 = 80807) (by norm_num)
theorem B763661 : Blo 507795 763661 := bbase (se 3 (by rfl) ⟨143186, by rfl⟩ : syracuseStep 763661 = 286373) (by norm_num)
theorem B763685 : Blo 507795 763685 := bbase (se 4 (by rfl) ⟨71595, by rfl⟩ : syracuseStep 763685 = 143191) (by norm_num)
theorem B763709 : Blo 507795 763709 := bbase (se 3 (by rfl) ⟨143195, by rfl⟩ : syracuseStep 763709 = 286391) (by norm_num)
theorem B1288021 : Blo 507795 1288021 := bbase (se 9 (by rfl) ⟨3773, by rfl⟩ : syracuseStep 1288021 = 7547) (by norm_num)
theorem B763733 : Blo 507795 763733 := bbase (se 9 (by rfl) ⟨2237, by rfl⟩ : syracuseStep 763733 = 4475) (by norm_num)
theorem B763757 : Blo 507795 763757 := bbase (se 3 (by rfl) ⟨143204, by rfl⟩ : syracuseStep 763757 = 286409) (by norm_num)
theorem B862069 : Blo 507795 862069 := bbase (se 5 (by rfl) ⟨40409, by rfl⟩ : syracuseStep 862069 = 80819) (by norm_num)
theorem B763781 : Blo 507795 763781 := bbase (se 4 (by rfl) ⟨71604, by rfl⟩ : syracuseStep 763781 = 143209) (by norm_num)
theorem B2074501 : Blo 507795 2074501 := bbase (se 4 (by rfl) ⟨194484, by rfl⟩ : syracuseStep 2074501 = 388969) (by norm_num)
theorem B2074517 : Blo 507795 2074517 := bbase (se 6 (by rfl) ⟨48621, by rfl⟩ : syracuseStep 2074517 = 97243) (by norm_num)
theorem B763805 : Blo 507795 763805 := bbase (se 3 (by rfl) ⟨143213, by rfl⟩ : syracuseStep 763805 = 286427) (by norm_num)
theorem B763829 : Blo 507795 763829 := bbase (se 5 (by rfl) ⟨35804, by rfl⟩ : syracuseStep 763829 = 71609) (by norm_num)
theorem B1288133 : Blo 507795 1288133 := bbase (se 4 (by rfl) ⟨120762, by rfl⟩ : syracuseStep 1288133 = 241525) (by norm_num)
theorem B763853 : Blo 507795 763853 := bbase (se 3 (by rfl) ⟨143222, by rfl⟩ : syracuseStep 763853 = 286445) (by norm_num)
theorem B862157 : Blo 507795 862157 := bbase (se 3 (by rfl) ⟨161654, by rfl⟩ : syracuseStep 862157 = 323309) (by norm_num)
theorem B3876821 : Blo 507795 3876821 := bbase (se 7 (by rfl) ⟨45431, by rfl⟩ : syracuseStep 3876821 = 90863) (by norm_num)
theorem B763877 : Blo 507795 763877 := bbase (se 4 (by rfl) ⟨71613, by rfl⟩ : syracuseStep 763877 = 143227) (by norm_num)
theorem B763901 : Blo 507795 763901 := bbase (se 3 (by rfl) ⟨143231, by rfl⟩ : syracuseStep 763901 = 286463) (by norm_num)
theorem B763925 : Blo 507795 763925 := bbase (se 6 (by rfl) ⟨17904, by rfl⟩ : syracuseStep 763925 = 35809) (by norm_num)
theorem B763949 : Blo 507795 763949 := bbase (se 3 (by rfl) ⟨143240, by rfl⟩ : syracuseStep 763949 = 286481) (by norm_num)
theorem B1714229 : Blo 507795 1714229 := bbase (se 5 (by rfl) ⟨80354, by rfl⟩ : syracuseStep 1714229 = 160709) (by norm_num)
theorem B763973 : Blo 507795 763973 := bbase (se 4 (by rfl) ⟨71622, by rfl⟩ : syracuseStep 763973 = 143245) (by norm_num)
theorem B862285 : Blo 507795 862285 := bbase (se 3 (by rfl) ⟨161678, by rfl⟩ : syracuseStep 862285 = 323357) (by norm_num)
theorem B763997 : Blo 507795 763997 := bbase (se 3 (by rfl) ⟨143249, by rfl⟩ : syracuseStep 763997 = 286499) (by norm_num)
theorem B829549 : Blo 507795 829549 := bbase (se 3 (by rfl) ⟨155540, by rfl⟩ : syracuseStep 829549 = 311081) (by norm_num)
theorem B764021 : Blo 507795 764021 := bbase (se 5 (by rfl) ⟨35813, by rfl⟩ : syracuseStep 764021 = 71627) (by norm_num)
theorem B1288325 : Blo 507795 1288325 := bbase (se 4 (by rfl) ⟨120780, by rfl⟩ : syracuseStep 1288325 = 241561) (by norm_num)
theorem B764045 : Blo 507795 764045 := bbase (se 3 (by rfl) ⟨143258, by rfl⟩ : syracuseStep 764045 = 286517) (by norm_num)
theorem B764069 : Blo 507795 764069 := bbase (se 4 (by rfl) ⟨71631, by rfl⟩ : syracuseStep 764069 = 143263) (by norm_num)
theorem B862373 : Blo 507795 862373 := bbase (se 4 (by rfl) ⟨80847, by rfl⟩ : syracuseStep 862373 = 161695) (by norm_num)
theorem B3582133 : Blo 507795 3582133 := bbase (se 5 (by rfl) ⟨167912, by rfl⟩ : syracuseStep 3582133 = 335825) (by norm_num)
theorem B764093 : Blo 507795 764093 := bbase (se 3 (by rfl) ⟨143267, by rfl⟩ : syracuseStep 764093 = 286535) (by norm_num)
theorem B764117 : Blo 507795 764117 := bbase (se 7 (by rfl) ⟨8954, by rfl⟩ : syracuseStep 764117 = 17909) (by norm_num)
theorem B764141 : Blo 507795 764141 := bbase (se 3 (by rfl) ⟨143276, by rfl⟩ : syracuseStep 764141 = 286553) (by norm_num)
theorem B1222901 : Blo 507795 1222901 := bbase (se 5 (by rfl) ⟨57323, by rfl⟩ : syracuseStep 1222901 = 114647) (by norm_num)
theorem B764165 : Blo 507795 764165 := bbase (se 4 (by rfl) ⟨71640, by rfl⟩ : syracuseStep 764165 = 143281) (by norm_num)
theorem B764189 : Blo 507795 764189 := bbase (se 3 (by rfl) ⟨143285, by rfl⟩ : syracuseStep 764189 = 286571) (by norm_num)
theorem B862501 : Blo 507795 862501 := bbase (se 4 (by rfl) ⟨80859, by rfl⟩ : syracuseStep 862501 = 161719) (by norm_num)
theorem B764213 : Blo 507795 764213 := bbase (se 5 (by rfl) ⟨35822, by rfl⟩ : syracuseStep 764213 = 71645) (by norm_num)
theorem B764237 : Blo 507795 764237 := bbase (se 3 (by rfl) ⟨143294, by rfl⟩ : syracuseStep 764237 = 286589) (by norm_num)
theorem B764261 : Blo 507795 764261 := bbase (se 4 (by rfl) ⟨71649, by rfl⟩ : syracuseStep 764261 = 143299) (by norm_num)
theorem B1223029 : Blo 507795 1223029 := bbase (se 5 (by rfl) ⟨57329, by rfl⟩ : syracuseStep 1223029 = 114659) (by norm_num)
theorem B764285 : Blo 507795 764285 := bbase (se 3 (by rfl) ⟨143303, by rfl⟩ : syracuseStep 764285 = 286607) (by norm_num)
theorem B862589 : Blo 507795 862589 := bbase (se 3 (by rfl) ⟨161735, by rfl⟩ : syracuseStep 862589 = 323471) (by norm_num)
theorem B764309 : Blo 507795 764309 := bbase (se 6 (by rfl) ⟨17913, by rfl⟩ : syracuseStep 764309 = 35827) (by norm_num)
theorem B764333 : Blo 507795 764333 := bbase (se 3 (by rfl) ⟨143312, by rfl⟩ : syracuseStep 764333 = 286625) (by norm_num)
theorem B764357 : Blo 507795 764357 := bbase (se 4 (by rfl) ⟨71658, by rfl⟩ : syracuseStep 764357 = 143317) (by norm_num)
theorem B1288669 : Blo 507795 1288669 := bbase (se 3 (by rfl) ⟨241625, by rfl⟩ : syracuseStep 1288669 = 483251) (by norm_num)
theorem B764381 : Blo 507795 764381 := bbase (se 3 (by rfl) ⟨143321, by rfl⟩ : syracuseStep 764381 = 286643) (by norm_num)
theorem B1714661 : Blo 507795 1714661 := bbase (se 4 (by rfl) ⟨160749, by rfl⟩ : syracuseStep 1714661 = 321499) (by norm_num)
theorem B764405 : Blo 507795 764405 := bbase (se 5 (by rfl) ⟨35831, by rfl⟩ : syracuseStep 764405 = 71663) (by norm_num)
theorem B862717 : Blo 507795 862717 := bbase (se 3 (by rfl) ⟨161759, by rfl⟩ : syracuseStep 862717 = 323519) (by norm_num)
theorem B764429 : Blo 507795 764429 := bbase (se 3 (by rfl) ⟨143330, by rfl⟩ : syracuseStep 764429 = 286661) (by norm_num)
theorem B764453 : Blo 507795 764453 := bbase (se 4 (by rfl) ⟨71667, by rfl⟩ : syracuseStep 764453 = 143335) (by norm_num)
theorem B1092133 : Blo 507795 1092133 := bbase (se 4 (by rfl) ⟨102387, by rfl⟩ : syracuseStep 1092133 = 204775) (by norm_num)
theorem B764477 : Blo 507795 764477 := bbase (se 3 (by rfl) ⟨143339, by rfl⟩ : syracuseStep 764477 = 286679) (by norm_num)
theorem B1452613 : Blo 507795 1452613 := bbase (se 4 (by rfl) ⟨136182, by rfl⟩ : syracuseStep 1452613 = 272365) (by norm_num)
theorem B1288781 : Blo 507795 1288781 := bbase (se 3 (by rfl) ⟨241646, by rfl⟩ : syracuseStep 1288781 = 483293) (by norm_num)
theorem B764501 : Blo 507795 764501 := bbase (se 8 (by rfl) ⟨4479, by rfl⟩ : syracuseStep 764501 = 8959) (by norm_num)
theorem B862805 : Blo 507795 862805 := bbase (se 8 (by rfl) ⟨5055, by rfl⟩ : syracuseStep 862805 = 10111) (by norm_num)
theorem B764525 : Blo 507795 764525 := bbase (se 3 (by rfl) ⟨143348, by rfl⟩ : syracuseStep 764525 = 286697) (by norm_num)
theorem B764549 : Blo 507795 764549 := bbase (se 4 (by rfl) ⟨71676, by rfl⟩ : syracuseStep 764549 = 143353) (by norm_num)
theorem B764573 : Blo 507795 764573 := bbase (se 3 (by rfl) ⟨143357, by rfl⟩ : syracuseStep 764573 = 286715) (by norm_num)
theorem B764597 : Blo 507795 764597 := bbase (se 5 (by rfl) ⟨35840, by rfl⟩ : syracuseStep 764597 = 71681) (by norm_num)
theorem B1223365 : Blo 507795 1223365 := bbase (se 4 (by rfl) ⟨114690, by rfl⟩ : syracuseStep 1223365 = 229381) (by norm_num)
theorem B764621 : Blo 507795 764621 := bbase (se 3 (by rfl) ⟨143366, by rfl⟩ : syracuseStep 764621 = 286733) (by norm_num)
theorem B862933 : Blo 507795 862933 := bbase (se 7 (by rfl) ⟨10112, by rfl⟩ : syracuseStep 862933 = 20225) (by norm_num)
theorem B764645 : Blo 507795 764645 := bbase (se 4 (by rfl) ⟨71685, by rfl⟩ : syracuseStep 764645 = 143371) (by norm_num)
theorem B764669 : Blo 507795 764669 := bbase (se 3 (by rfl) ⟨143375, by rfl⟩ : syracuseStep 764669 = 286751) (by norm_num)
theorem B1288973 : Blo 507795 1288973 := bbase (se 3 (by rfl) ⟨241682, by rfl⟩ : syracuseStep 1288973 = 483365) (by norm_num)
theorem B764693 : Blo 507795 764693 := bbase (se 6 (by rfl) ⟨17922, by rfl⟩ : syracuseStep 764693 = 35845) (by norm_num)
theorem B764717 : Blo 507795 764717 := bbase (se 3 (by rfl) ⟨143384, by rfl⟩ : syracuseStep 764717 = 286769) (by norm_num)
theorem B863021 : Blo 507795 863021 := bbase (se 3 (by rfl) ⟨161816, by rfl⟩ : syracuseStep 863021 = 323633) (by norm_num)
theorem B764741 : Blo 507795 764741 := bbase (se 4 (by rfl) ⟨71694, by rfl⟩ : syracuseStep 764741 = 143389) (by norm_num)
theorem B764765 : Blo 507795 764765 := bbase (se 3 (by rfl) ⟨143393, by rfl⟩ : syracuseStep 764765 = 286787) (by norm_num)
theorem B764789 : Blo 507795 764789 := bbase (se 5 (by rfl) ⟨35849, by rfl⟩ : syracuseStep 764789 = 71699) (by norm_num)
theorem B764813 : Blo 507795 764813 := bbase (se 3 (by rfl) ⟨143402, by rfl⟩ : syracuseStep 764813 = 286805) (by norm_num)
theorem B1715093 : Blo 507795 1715093 := bbase (se 6 (by rfl) ⟨40197, by rfl⟩ : syracuseStep 1715093 = 80395) (by norm_num)
theorem B764837 : Blo 507795 764837 := bbase (se 4 (by rfl) ⟨71703, by rfl⟩ : syracuseStep 764837 = 143407) (by norm_num)
theorem B863149 : Blo 507795 863149 := bbase (se 3 (by rfl) ⟨161840, by rfl⟩ : syracuseStep 863149 = 323681) (by norm_num)
theorem B764861 : Blo 507795 764861 := bbase (se 3 (by rfl) ⟨143411, by rfl⟩ : syracuseStep 764861 = 286823) (by norm_num)
theorem B764885 : Blo 507795 764885 := bbase (se 7 (by rfl) ⟨8963, by rfl⟩ : syracuseStep 764885 = 17927) (by norm_num)
theorem B764909 : Blo 507795 764909 := bbase (se 3 (by rfl) ⟨143420, by rfl⟩ : syracuseStep 764909 = 286841) (by norm_num)
theorem B764933 : Blo 507795 764933 := bbase (se 4 (by rfl) ⟨71712, by rfl⟩ : syracuseStep 764933 = 143425) (by norm_num)
theorem B863237 : Blo 507795 863237 := bbase (se 4 (by rfl) ⟨80928, by rfl⟩ : syracuseStep 863237 = 161857) (by norm_num)
theorem B1092629 : Blo 507795 1092629 := bbase (se 6 (by rfl) ⟨25608, by rfl⟩ : syracuseStep 1092629 = 51217) (by norm_num)
theorem B764957 : Blo 507795 764957 := bbase (se 3 (by rfl) ⟨143429, by rfl⟩ : syracuseStep 764957 = 286859) (by norm_num)
theorem B764981 : Blo 507795 764981 := bbase (se 5 (by rfl) ⟨35858, by rfl⟩ : syracuseStep 764981 = 71717) (by norm_num)
theorem B765005 : Blo 507795 765005 := bbase (se 3 (by rfl) ⟨143438, by rfl⟩ : syracuseStep 765005 = 286877) (by norm_num)
theorem B1289317 : Blo 507795 1289317 := bbase (se 4 (by rfl) ⟨120873, by rfl⟩ : syracuseStep 1289317 = 241747) (by norm_num)
theorem B765029 : Blo 507795 765029 := bbase (se 4 (by rfl) ⟨71721, by rfl⟩ : syracuseStep 765029 = 143443) (by norm_num)
theorem B765053 : Blo 507795 765053 := bbase (se 3 (by rfl) ⟨143447, by rfl⟩ : syracuseStep 765053 = 286895) (by norm_num)
theorem B863365 : Blo 507795 863365 := bbase (se 4 (by rfl) ⟨80940, by rfl⟩ : syracuseStep 863365 = 161881) (by norm_num)
theorem B765077 : Blo 507795 765077 := bbase (se 6 (by rfl) ⟨17931, by rfl⟩ : syracuseStep 765077 = 35863) (by norm_num)
theorem B765101 : Blo 507795 765101 := bbase (se 3 (by rfl) ⟨143456, by rfl⟩ : syracuseStep 765101 = 286913) (by norm_num)
theorem B765125 : Blo 507795 765125 := bbase (se 4 (by rfl) ⟨71730, by rfl⟩ : syracuseStep 765125 = 143461) (by norm_num)
theorem B1289429 : Blo 507795 1289429 := bbase (se 7 (by rfl) ⟨15110, by rfl⟩ : syracuseStep 1289429 = 30221) (by norm_num)
theorem B765149 : Blo 507795 765149 := bbase (se 3 (by rfl) ⟨143465, by rfl⟩ : syracuseStep 765149 = 286931) (by norm_num)
theorem B863453 : Blo 507795 863453 := bbase (se 3 (by rfl) ⟨161897, by rfl⟩ : syracuseStep 863453 = 323795) (by norm_num)
theorem B765173 : Blo 507795 765173 := bbase (se 5 (by rfl) ⟨35867, by rfl⟩ : syracuseStep 765173 = 71735) (by norm_num)
theorem B765197 : Blo 507795 765197 := bbase (se 3 (by rfl) ⟨143474, by rfl⟩ : syracuseStep 765197 = 286949) (by norm_num)
theorem B765221 : Blo 507795 765221 := bbase (se 4 (by rfl) ⟨71739, by rfl⟩ : syracuseStep 765221 = 143479) (by norm_num)
theorem B1223981 : Blo 507795 1223981 := bbase (se 3 (by rfl) ⟨229496, by rfl⟩ : syracuseStep 1223981 = 458993) (by norm_num)
theorem B3484981 : Blo 507795 3484981 := bbase (se 5 (by rfl) ⟨163358, by rfl⟩ : syracuseStep 3484981 = 326717) (by norm_num)
theorem B4140341 : Blo 507795 4140341 := bbase (se 5 (by rfl) ⟨194078, by rfl⟩ : syracuseStep 4140341 = 388157) (by norm_num)
theorem B765245 : Blo 507795 765245 := bbase (se 3 (by rfl) ⟨143483, by rfl⟩ : syracuseStep 765245 = 286967) (by norm_num)
theorem B1715525 : Blo 507795 1715525 := bbase (se 4 (by rfl) ⟨160830, by rfl⟩ : syracuseStep 1715525 = 321661) (by norm_num)
theorem B765269 : Blo 507795 765269 := bbase (se 11 (by rfl) ⟨560, by rfl⟩ : syracuseStep 765269 = 1121) (by norm_num)
theorem B863581 : Blo 507795 863581 := bbase (se 3 (by rfl) ⟨161921, by rfl⟩ : syracuseStep 863581 = 323843) (by norm_num)
theorem B765293 : Blo 507795 765293 := bbase (se 3 (by rfl) ⟨143492, by rfl⟩ : syracuseStep 765293 = 286985) (by norm_num)
theorem B765317 : Blo 507795 765317 := bbase (se 4 (by rfl) ⟨71748, by rfl⟩ : syracuseStep 765317 = 143497) (by norm_num)
theorem B2174357 : Blo 507795 2174357 := bbase (se 6 (by rfl) ⟨50961, by rfl⟩ : syracuseStep 2174357 = 101923) (by norm_num)
theorem B1289621 : Blo 507795 1289621 := bbase (se 6 (by rfl) ⟨30225, by rfl⟩ : syracuseStep 1289621 = 60451) (by norm_num)
theorem B765341 : Blo 507795 765341 := bbase (se 3 (by rfl) ⟨143501, by rfl⟩ : syracuseStep 765341 = 287003) (by norm_num)
theorem B765365 : Blo 507795 765365 := bbase (se 5 (by rfl) ⟨35876, by rfl⟩ : syracuseStep 765365 = 71753) (by norm_num)
theorem B765389 : Blo 507795 765389 := bbase (se 3 (by rfl) ⟨143510, by rfl⟩ : syracuseStep 765389 = 287021) (by norm_num)
theorem B765413 : Blo 507795 765413 := bbase (se 4 (by rfl) ⟨71757, by rfl⟩ : syracuseStep 765413 = 143515) (by norm_num)
theorem B765437 : Blo 507795 765437 := bbase (se 3 (by rfl) ⟨143519, by rfl⟩ : syracuseStep 765437 = 287039) (by norm_num)
theorem B765461 : Blo 507795 765461 := bbase (se 6 (by rfl) ⟨17940, by rfl⟩ : syracuseStep 765461 = 35881) (by norm_num)
theorem B765485 : Blo 507795 765485 := bbase (se 3 (by rfl) ⟨143528, by rfl⟩ : syracuseStep 765485 = 287057) (by norm_num)
theorem B765509 : Blo 507795 765509 := bbase (se 4 (by rfl) ⟨71766, by rfl⟩ : syracuseStep 765509 = 143533) (by norm_num)
theorem B765533 : Blo 507795 765533 := bbase (se 3 (by rfl) ⟨143537, by rfl⟩ : syracuseStep 765533 = 287075) (by norm_num)
theorem B765557 : Blo 507795 765557 := bbase (se 5 (by rfl) ⟨35885, by rfl⟩ : syracuseStep 765557 = 71771) (by norm_num)
theorem B2174597 : Blo 507795 2174597 := bbase (se 4 (by rfl) ⟨203868, by rfl⟩ : syracuseStep 2174597 = 407737) (by norm_num)
theorem B765581 : Blo 507795 765581 := bbase (se 3 (by rfl) ⟨143546, by rfl⟩ : syracuseStep 765581 = 287093) (by norm_num)
theorem B1453717 : Blo 507795 1453717 := bbase (se 6 (by rfl) ⟨34071, by rfl⟩ : syracuseStep 1453717 = 68143) (by norm_num)
theorem B765605 : Blo 507795 765605 := bbase (se 4 (by rfl) ⟨71775, by rfl⟩ : syracuseStep 765605 = 143551) (by norm_num)
theorem B765629 : Blo 507795 765629 := bbase (se 3 (by rfl) ⟨143555, by rfl⟩ : syracuseStep 765629 = 287111) (by norm_num)
theorem B765653 : Blo 507795 765653 := bbase (se 7 (by rfl) ⟨8972, by rfl⟩ : syracuseStep 765653 = 17945) (by norm_num)
theorem B1224413 : Blo 507795 1224413 := bbase (se 3 (by rfl) ⟨229577, by rfl⟩ : syracuseStep 1224413 = 459155) (by norm_num)
theorem B1289965 : Blo 507795 1289965 := bbase (se 3 (by rfl) ⟨241868, by rfl⟩ : syracuseStep 1289965 = 483737) (by norm_num)
theorem B765677 : Blo 507795 765677 := bbase (se 3 (by rfl) ⟨143564, by rfl⟩ : syracuseStep 765677 = 287129) (by norm_num)
theorem B1715957 : Blo 507795 1715957 := bbase (se 5 (by rfl) ⟨80435, by rfl⟩ : syracuseStep 1715957 = 160871) (by norm_num)
theorem B765701 : Blo 507795 765701 := bbase (se 4 (by rfl) ⟨71784, by rfl⟩ : syracuseStep 765701 = 143569) (by norm_num)
theorem B765725 : Blo 507795 765725 := bbase (se 3 (by rfl) ⟨143573, by rfl⟩ : syracuseStep 765725 = 287147) (by norm_num)
theorem B765749 : Blo 507795 765749 := bbase (se 5 (by rfl) ⟨35894, by rfl⟩ : syracuseStep 765749 = 71789) (by norm_num)
theorem B765773 : Blo 507795 765773 := bbase (se 3 (by rfl) ⟨143582, by rfl⟩ : syracuseStep 765773 = 287165) (by norm_num)
theorem B1290077 : Blo 507795 1290077 := bbase (se 3 (by rfl) ⟨241889, by rfl⟩ : syracuseStep 1290077 = 483779) (by norm_num)
theorem B765797 : Blo 507795 765797 := bbase (se 4 (by rfl) ⟨71793, by rfl⟩ : syracuseStep 765797 = 143587) (by norm_num)
theorem B765821 : Blo 507795 765821 := bbase (se 3 (by rfl) ⟨143591, by rfl⟩ : syracuseStep 765821 = 287183) (by norm_num)
theorem B765845 : Blo 507795 765845 := bbase (se 6 (by rfl) ⟨17949, by rfl⟩ : syracuseStep 765845 = 35899) (by norm_num)
theorem B765869 : Blo 507795 765869 := bbase (se 3 (by rfl) ⟨143600, by rfl⟩ : syracuseStep 765869 = 287201) (by norm_num)
theorem B765893 : Blo 507795 765893 := bbase (se 4 (by rfl) ⟨71802, by rfl⟩ : syracuseStep 765893 = 143605) (by norm_num)
theorem B765917 : Blo 507795 765917 := bbase (se 3 (by rfl) ⟨143609, by rfl⟩ : syracuseStep 765917 = 287219) (by norm_num)
theorem B765941 : Blo 507795 765941 := bbase (se 5 (by rfl) ⟨35903, by rfl⟩ : syracuseStep 765941 = 71807) (by norm_num)
theorem B765965 : Blo 507795 765965 := bbase (se 3 (by rfl) ⟨143618, by rfl⟩ : syracuseStep 765965 = 287237) (by norm_num)
theorem B1290269 : Blo 507795 1290269 := bbase (se 3 (by rfl) ⟨241925, by rfl⟩ : syracuseStep 1290269 = 483851) (by norm_num)
theorem B765989 : Blo 507795 765989 := bbase (se 4 (by rfl) ⟨71811, by rfl⟩ : syracuseStep 765989 = 143623) (by norm_num)
theorem B766013 : Blo 507795 766013 := bbase (se 3 (by rfl) ⟨143627, by rfl⟩ : syracuseStep 766013 = 287255) (by norm_num)
theorem B766037 : Blo 507795 766037 := bbase (se 8 (by rfl) ⟨4488, by rfl⟩ : syracuseStep 766037 = 8977) (by norm_num)
theorem B766061 : Blo 507795 766061 := bbase (se 3 (by rfl) ⟨143636, by rfl⟩ : syracuseStep 766061 = 287273) (by norm_num)
theorem B766085 : Blo 507795 766085 := bbase (se 4 (by rfl) ⟨71820, by rfl⟩ : syracuseStep 766085 = 143641) (by norm_num)
theorem B766109 : Blo 507795 766109 := bbase (se 3 (by rfl) ⟨143645, by rfl⟩ : syracuseStep 766109 = 287291) (by norm_num)
theorem B1716389 : Blo 507795 1716389 := bbase (se 4 (by rfl) ⟨160911, by rfl⟩ : syracuseStep 1716389 = 321823) (by norm_num)
theorem B766133 : Blo 507795 766133 := bbase (se 5 (by rfl) ⟨35912, by rfl⟩ : syracuseStep 766133 = 71825) (by norm_num)
theorem B766157 : Blo 507795 766157 := bbase (se 3 (by rfl) ⟨143654, by rfl⟩ : syracuseStep 766157 = 287309) (by norm_num)
theorem B1323221 : Blo 507795 1323221 := bbase (se 7 (by rfl) ⟨15506, by rfl⟩ : syracuseStep 1323221 = 31013) (by norm_num)
theorem B766181 : Blo 507795 766181 := bbase (se 4 (by rfl) ⟨71829, by rfl⟩ : syracuseStep 766181 = 143659) (by norm_num)
theorem B766205 : Blo 507795 766205 := bbase (se 3 (by rfl) ⟨143663, by rfl⟩ : syracuseStep 766205 = 287327) (by norm_num)
theorem B766229 : Blo 507795 766229 := bbase (se 6 (by rfl) ⟨17958, by rfl⟩ : syracuseStep 766229 = 35917) (by norm_num)
theorem B766253 : Blo 507795 766253 := bbase (se 3 (by rfl) ⟨143672, by rfl⟩ : syracuseStep 766253 = 287345) (by norm_num)
theorem B2896181 : Blo 507795 2896181 := bbase (se 5 (by rfl) ⟨135758, by rfl⟩ : syracuseStep 2896181 = 271517) (by norm_num)
theorem B766277 : Blo 507795 766277 := bbase (se 4 (by rfl) ⟨71838, by rfl⟩ : syracuseStep 766277 = 143677) (by norm_num)
theorem B1225037 : Blo 507795 1225037 := bbase (se 3 (by rfl) ⟨229694, by rfl⟩ : syracuseStep 1225037 = 459389) (by norm_num)
theorem B766301 : Blo 507795 766301 := bbase (se 3 (by rfl) ⟨143681, by rfl⟩ : syracuseStep 766301 = 287363) (by norm_num)
theorem B1290613 : Blo 507795 1290613 := bbase (se 5 (by rfl) ⟨60497, by rfl⟩ : syracuseStep 1290613 = 120995) (by norm_num)
theorem B766325 : Blo 507795 766325 := bbase (se 5 (by rfl) ⟨35921, by rfl⟩ : syracuseStep 766325 = 71843) (by norm_num)
theorem B766349 : Blo 507795 766349 := bbase (se 3 (by rfl) ⟨143690, by rfl⟩ : syracuseStep 766349 = 287381) (by norm_num)
theorem B766373 : Blo 507795 766373 := bbase (se 4 (by rfl) ⟨71847, by rfl⟩ : syracuseStep 766373 = 143695) (by norm_num)
theorem B766397 : Blo 507795 766397 := bbase (se 3 (by rfl) ⟨143699, by rfl⟩ : syracuseStep 766397 = 287399) (by norm_num)
theorem B766421 : Blo 507795 766421 := bbase (se 7 (by rfl) ⟨8981, by rfl⟩ : syracuseStep 766421 = 17963) (by norm_num)
theorem B1290725 : Blo 507795 1290725 := bbase (se 4 (by rfl) ⟨121005, by rfl⟩ : syracuseStep 1290725 = 242011) (by norm_num)
theorem B766445 : Blo 507795 766445 := bbase (se 3 (by rfl) ⟨143708, by rfl⟩ : syracuseStep 766445 = 287417) (by norm_num)
theorem B766469 : Blo 507795 766469 := bbase (se 4 (by rfl) ⟨71856, by rfl⟩ : syracuseStep 766469 = 143713) (by norm_num)
theorem B766493 : Blo 507795 766493 := bbase (se 3 (by rfl) ⟨143717, by rfl⟩ : syracuseStep 766493 = 287435) (by norm_num)
theorem B766517 : Blo 507795 766517 := bbase (se 5 (by rfl) ⟨35930, by rfl⟩ : syracuseStep 766517 = 71861) (by norm_num)
theorem B766541 : Blo 507795 766541 := bbase (se 3 (by rfl) ⟨143726, by rfl⟩ : syracuseStep 766541 = 287453) (by norm_num)
theorem B1716821 : Blo 507795 1716821 := bbase (se 8 (by rfl) ⟨10059, by rfl⟩ : syracuseStep 1716821 = 20119) (by norm_num)
theorem B766565 : Blo 507795 766565 := bbase (se 4 (by rfl) ⟨71865, by rfl⟩ : syracuseStep 766565 = 143731) (by norm_num)
theorem B766589 : Blo 507795 766589 := bbase (se 3 (by rfl) ⟨143735, by rfl⟩ : syracuseStep 766589 = 287471) (by norm_num)
theorem B766613 : Blo 507795 766613 := bbase (se 6 (by rfl) ⟨17967, by rfl⟩ : syracuseStep 766613 = 35935) (by norm_num)
theorem B1290917 : Blo 507795 1290917 := bbase (se 4 (by rfl) ⟨121023, by rfl⟩ : syracuseStep 1290917 = 242047) (by norm_num)
theorem B766637 : Blo 507795 766637 := bbase (se 3 (by rfl) ⟨143744, by rfl⟩ : syracuseStep 766637 = 287489) (by norm_num)
theorem B766661 : Blo 507795 766661 := bbase (se 4 (by rfl) ⟨71874, by rfl⟩ : syracuseStep 766661 = 143749) (by norm_num)
theorem B1159901 : Blo 507795 1159901 := bbase (se 3 (by rfl) ⟨217481, by rfl⟩ : syracuseStep 1159901 = 434963) (by norm_num)
theorem B766685 : Blo 507795 766685 := bbase (se 3 (by rfl) ⟨143753, by rfl⟩ : syracuseStep 766685 = 287507) (by norm_num)
theorem B996085 : Blo 507795 996085 := bbase (se 5 (by rfl) ⟨46691, by rfl⟩ : syracuseStep 996085 = 93383) (by norm_num)
theorem B766709 : Blo 507795 766709 := bbase (se 5 (by rfl) ⟨35939, by rfl⟩ : syracuseStep 766709 = 71879) (by norm_num)
theorem B766733 : Blo 507795 766733 := bbase (se 3 (by rfl) ⟨143762, by rfl⟩ : syracuseStep 766733 = 287525) (by norm_num)
theorem B766757 : Blo 507795 766757 := bbase (se 4 (by rfl) ⟨71883, by rfl⟩ : syracuseStep 766757 = 143767) (by norm_num)
theorem B766781 : Blo 507795 766781 := bbase (se 3 (by rfl) ⟨143771, by rfl⟩ : syracuseStep 766781 = 287543) (by norm_num)
theorem B766805 : Blo 507795 766805 := bbase (se 9 (by rfl) ⟨2246, by rfl⟩ : syracuseStep 766805 = 4493) (by norm_num)
theorem B766829 : Blo 507795 766829 := bbase (se 3 (by rfl) ⟨143780, by rfl⟩ : syracuseStep 766829 = 287561) (by norm_num)
theorem B766853 : Blo 507795 766853 := bbase (se 4 (by rfl) ⟨71892, by rfl⟩ : syracuseStep 766853 = 143785) (by norm_num)
theorem B766877 : Blo 507795 766877 := bbase (se 3 (by rfl) ⟨143789, by rfl⟩ : syracuseStep 766877 = 287579) (by norm_num)
theorem B766901 : Blo 507795 766901 := bbase (se 5 (by rfl) ⟨35948, by rfl⟩ : syracuseStep 766901 = 71897) (by norm_num)
theorem B766925 : Blo 507795 766925 := bbase (se 3 (by rfl) ⟨143798, by rfl⟩ : syracuseStep 766925 = 287597) (by norm_num)
theorem B766949 : Blo 507795 766949 := bbase (se 4 (by rfl) ⟨71901, by rfl⟩ : syracuseStep 766949 = 143803) (by norm_num)
theorem B3257333 : Blo 507795 3257333 := bbase (se 5 (by rfl) ⟨152687, by rfl⟩ : syracuseStep 3257333 = 305375) (by norm_num)
theorem B1291261 : Blo 507795 1291261 := bbase (se 3 (by rfl) ⟨242111, by rfl⟩ : syracuseStep 1291261 = 484223) (by norm_num)
theorem B766973 : Blo 507795 766973 := bbase (se 3 (by rfl) ⟨143807, by rfl⟩ : syracuseStep 766973 = 287615) (by norm_num)
theorem B1717253 : Blo 507795 1717253 := bbase (se 4 (by rfl) ⟨160992, by rfl⟩ : syracuseStep 1717253 = 321985) (by norm_num)
theorem B766997 : Blo 507795 766997 := bbase (se 6 (by rfl) ⟨17976, by rfl⟩ : syracuseStep 766997 = 35953) (by norm_num)
theorem B767021 : Blo 507795 767021 := bbase (se 3 (by rfl) ⟨143816, by rfl⟩ : syracuseStep 767021 = 287633) (by norm_num)
theorem B767045 : Blo 507795 767045 := bbase (se 4 (by rfl) ⟨71910, by rfl⟩ : syracuseStep 767045 = 143821) (by norm_num)
theorem B767069 : Blo 507795 767069 := bbase (se 3 (by rfl) ⟨143825, by rfl⟩ : syracuseStep 767069 = 287651) (by norm_num)
theorem B1291373 : Blo 507795 1291373 := bbase (se 3 (by rfl) ⟨242132, by rfl⟩ : syracuseStep 1291373 = 484265) (by norm_num)
theorem B1455221 : Blo 507795 1455221 := bbase (se 5 (by rfl) ⟨68213, by rfl⟩ : syracuseStep 1455221 = 136427) (by norm_num)
theorem B767093 : Blo 507795 767093 := bbase (se 5 (by rfl) ⟨35957, by rfl⟩ : syracuseStep 767093 = 71915) (by norm_num)
theorem B767117 : Blo 507795 767117 := bbase (se 3 (by rfl) ⟨143834, by rfl⟩ : syracuseStep 767117 = 287669) (by norm_num)
theorem B767141 : Blo 507795 767141 := bbase (se 4 (by rfl) ⟨71919, by rfl⟩ : syracuseStep 767141 = 143839) (by norm_num)
theorem B767165 : Blo 507795 767165 := bbase (se 3 (by rfl) ⟨143843, by rfl⟩ : syracuseStep 767165 = 287687) (by norm_num)
theorem B767189 : Blo 507795 767189 := bbase (se 7 (by rfl) ⟨8990, by rfl⟩ : syracuseStep 767189 = 17981) (by norm_num)
theorem B767213 : Blo 507795 767213 := bbase (se 3 (by rfl) ⟨143852, by rfl⟩ : syracuseStep 767213 = 287705) (by norm_num)
theorem B767237 : Blo 507795 767237 := bbase (se 4 (by rfl) ⟨71928, by rfl⟩ : syracuseStep 767237 = 143857) (by norm_num)
theorem B767261 : Blo 507795 767261 := bbase (se 3 (by rfl) ⟨143861, by rfl⟩ : syracuseStep 767261 = 287723) (by norm_num)
theorem B1291565 : Blo 507795 1291565 := bbase (se 3 (by rfl) ⟨242168, by rfl⟩ : syracuseStep 1291565 = 484337) (by norm_num)
theorem B767285 : Blo 507795 767285 := bbase (se 5 (by rfl) ⟨35966, by rfl⟩ : syracuseStep 767285 = 71933) (by norm_num)
theorem B767309 : Blo 507795 767309 := bbase (se 3 (by rfl) ⟨143870, by rfl⟩ : syracuseStep 767309 = 287741) (by norm_num)
theorem B767333 : Blo 507795 767333 := bbase (se 4 (by rfl) ⟨71937, by rfl⟩ : syracuseStep 767333 = 143875) (by norm_num)
theorem B767357 : Blo 507795 767357 := bbase (se 3 (by rfl) ⟨143879, by rfl⟩ : syracuseStep 767357 = 287759) (by norm_num)
theorem B767381 : Blo 507795 767381 := bbase (se 6 (by rfl) ⟨17985, by rfl⟩ : syracuseStep 767381 = 35971) (by norm_num)
theorem B767405 : Blo 507795 767405 := bbase (se 3 (by rfl) ⟨143888, by rfl⟩ : syracuseStep 767405 = 287777) (by norm_num)
theorem B1717685 : Blo 507795 1717685 := bbase (se 5 (by rfl) ⟨80516, by rfl⟩ : syracuseStep 1717685 = 161033) (by norm_num)
theorem B767429 : Blo 507795 767429 := bbase (se 4 (by rfl) ⟨71946, by rfl⟩ : syracuseStep 767429 = 143893) (by norm_num)
theorem B767453 : Blo 507795 767453 := bbase (se 3 (by rfl) ⟨143897, by rfl⟩ : syracuseStep 767453 = 287795) (by norm_num)
theorem B767477 : Blo 507795 767477 := bbase (se 5 (by rfl) ⟨35975, by rfl⟩ : syracuseStep 767477 = 71951) (by norm_num)
theorem B767501 : Blo 507795 767501 := bbase (se 3 (by rfl) ⟨143906, by rfl⟩ : syracuseStep 767501 = 287813) (by norm_num)
theorem B1553941 : Blo 507795 1553941 := bbase (se 6 (by rfl) ⟨36420, by rfl⟩ : syracuseStep 1553941 = 72841) (by norm_num)
theorem B964133 : Blo 507795 964133 := bbase (se 4 (by rfl) ⟨90387, by rfl⟩ : syracuseStep 964133 = 180775) (by norm_num)
theorem B767525 : Blo 507795 767525 := bbase (se 4 (by rfl) ⟨71955, by rfl⟩ : syracuseStep 767525 = 143911) (by norm_num)
theorem B767549 : Blo 507795 767549 := bbase (se 3 (by rfl) ⟨143915, by rfl⟩ : syracuseStep 767549 = 287831) (by norm_num)
theorem B767573 : Blo 507795 767573 := bbase (se 8 (by rfl) ⟨4497, by rfl⟩ : syracuseStep 767573 = 8995) (by norm_num)
theorem B767597 : Blo 507795 767597 := bbase (se 3 (by rfl) ⟨143924, by rfl⟩ : syracuseStep 767597 = 287849) (by norm_num)
theorem B1291909 : Blo 507795 1291909 := bbase (se 4 (by rfl) ⟨121116, by rfl⟩ : syracuseStep 1291909 = 242233) (by norm_num)
theorem B767621 : Blo 507795 767621 := bbase (se 4 (by rfl) ⟨71964, by rfl⟩ : syracuseStep 767621 = 143929) (by norm_num)
theorem B767645 : Blo 507795 767645 := bbase (se 3 (by rfl) ⟨143933, by rfl⟩ : syracuseStep 767645 = 287867) (by norm_num)
theorem B767669 : Blo 507795 767669 := bbase (se 5 (by rfl) ⟨35984, by rfl⟩ : syracuseStep 767669 = 71969) (by norm_num)
theorem B767693 : Blo 507795 767693 := bbase (se 3 (by rfl) ⟨143942, by rfl⟩ : syracuseStep 767693 = 287885) (by norm_num)
theorem B1292021 : Blo 507795 1292021 := bbase (se 5 (by rfl) ⟨60563, by rfl⟩ : syracuseStep 1292021 = 121127) (by norm_num)
theorem B1718117 : Blo 507795 1718117 := bbase (se 4 (by rfl) ⟨161073, by rfl⟩ : syracuseStep 1718117 = 322147) (by norm_num)
theorem B2176885 : Blo 507795 2176885 := bbase (se 5 (by rfl) ⟨102041, by rfl⟩ : syracuseStep 2176885 = 204083) (by norm_num)
theorem B571297 : Blo 507795 571297 := bbase (se 2 (by rfl) ⟨214236, by rfl⟩ : syracuseStep 571297 = 428473) (by norm_num)
theorem B1292213 : Blo 507795 1292213 := bbase (se 5 (by rfl) ⟨60572, by rfl⟩ : syracuseStep 1292213 = 121145) (by norm_num)
theorem B571333 : Blo 507795 571333 := bbase (se 4 (by rfl) ⟨53562, by rfl⟩ : syracuseStep 571333 = 107125) (by norm_num)
theorem B571369 : Blo 507795 571369 := bbase (se 2 (by rfl) ⟨214263, by rfl⟩ : syracuseStep 571369 = 428527) (by norm_num)
theorem B571405 : Blo 507795 571405 := bbase (se 3 (by rfl) ⟨107138, by rfl⟩ : syracuseStep 571405 = 214277) (by norm_num)
theorem B571441 : Blo 507795 571441 := bbase (se 2 (by rfl) ⟨214290, by rfl⟩ : syracuseStep 571441 = 428581) (by norm_num)
theorem B571477 : Blo 507795 571477 := bbase (se 8 (by rfl) ⟨3348, by rfl⟩ : syracuseStep 571477 = 6697) (by norm_num)
theorem B571513 : Blo 507795 571513 := bbase (se 2 (by rfl) ⟨214317, by rfl⟩ : syracuseStep 571513 = 428635) (by norm_num)
theorem B571549 : Blo 507795 571549 := bbase (se 3 (by rfl) ⟨107165, by rfl⟩ : syracuseStep 571549 = 214331) (by norm_num)
theorem B571585 : Blo 507795 571585 := bbase (se 2 (by rfl) ⟨214344, by rfl⟩ : syracuseStep 571585 = 428689) (by norm_num)
theorem B735437 : Blo 507795 735437 := bbase (se 3 (by rfl) ⟨137894, by rfl⟩ : syracuseStep 735437 = 275789) (by norm_num)
theorem B571621 : Blo 507795 571621 := bbase (se 4 (by rfl) ⟨53589, by rfl⟩ : syracuseStep 571621 = 107179) (by norm_num)
theorem B571657 : Blo 507795 571657 := bbase (se 2 (by rfl) ⟨214371, by rfl⟩ : syracuseStep 571657 = 428743) (by norm_num)
theorem B1292557 : Blo 507795 1292557 := bbase (se 3 (by rfl) ⟨242354, by rfl⟩ : syracuseStep 1292557 = 484709) (by norm_num)
theorem B964885 : Blo 507795 964885 := bbase (se 6 (by rfl) ⟨22614, by rfl⟩ : syracuseStep 964885 = 45229) (by norm_num)
theorem B1718549 : Blo 507795 1718549 := bbase (se 6 (by rfl) ⟨40278, by rfl⟩ : syracuseStep 1718549 = 80557) (by norm_num)
theorem B571693 : Blo 507795 571693 := bbase (se 3 (by rfl) ⟨107192, by rfl⟩ : syracuseStep 571693 = 214385) (by norm_num)
theorem B571729 : Blo 507795 571729 := bbase (se 2 (by rfl) ⟨214398, by rfl⟩ : syracuseStep 571729 = 428797) (by norm_num)
theorem B571765 : Blo 507795 571765 := bbase (se 5 (by rfl) ⟨26801, by rfl⟩ : syracuseStep 571765 = 53603) (by norm_num)
theorem B1292669 : Blo 507795 1292669 := bbase (se 3 (by rfl) ⟨242375, by rfl⟩ : syracuseStep 1292669 = 484751) (by norm_num)
theorem B571801 : Blo 507795 571801 := bbase (se 2 (by rfl) ⟨214425, by rfl⟩ : syracuseStep 571801 = 428851) (by norm_num)
theorem B965029 : Blo 507795 965029 := bbase (se 4 (by rfl) ⟨90471, by rfl⟩ : syracuseStep 965029 = 180943) (by norm_num)
theorem B571837 : Blo 507795 571837 := bbase (se 3 (by rfl) ⟨107219, by rfl⟩ : syracuseStep 571837 = 214439) (by norm_num)
theorem B571873 : Blo 507795 571873 := bbase (se 2 (by rfl) ⟨214452, by rfl⟩ : syracuseStep 571873 = 428905) (by norm_num)
theorem B571909 : Blo 507795 571909 := bbase (se 4 (by rfl) ⟨53616, by rfl⟩ : syracuseStep 571909 = 107233) (by norm_num)
theorem B1161733 : Blo 507795 1161733 := bbase (se 4 (by rfl) ⟨108912, by rfl⟩ : syracuseStep 1161733 = 217825) (by norm_num)
theorem B571945 : Blo 507795 571945 := bbase (se 2 (by rfl) ⟨214479, by rfl⟩ : syracuseStep 571945 = 428959) (by norm_num)
theorem B1161773 : Blo 507795 1161773 := bbase (se 3 (by rfl) ⟨217832, by rfl⟩ : syracuseStep 1161773 = 435665) (by norm_num)
theorem B1292861 : Blo 507795 1292861 := bbase (se 3 (by rfl) ⟨242411, by rfl⟩ : syracuseStep 1292861 = 484823) (by norm_num)
theorem B965189 : Blo 507795 965189 := bbase (se 4 (by rfl) ⟨90486, by rfl⟩ : syracuseStep 965189 = 180973) (by norm_num)
theorem B571981 : Blo 507795 571981 := bbase (se 3 (by rfl) ⟨107246, by rfl⟩ : syracuseStep 571981 = 214493) (by norm_num)
theorem B572017 : Blo 507795 572017 := bbase (se 2 (by rfl) ⟨214506, by rfl⟩ : syracuseStep 572017 = 429013) (by norm_num)
theorem B572053 : Blo 507795 572053 := bbase (se 6 (by rfl) ⟨13407, by rfl⟩ : syracuseStep 572053 = 26815) (by norm_num)
theorem B10074773 : Blo 507795 10074773 := bbase (se 6 (by rfl) ⟨236127, by rfl⟩ : syracuseStep 10074773 = 472255) (by norm_num)
theorem B1555109 : Blo 507795 1555109 := bbase (se 4 (by rfl) ⟨145791, by rfl⟩ : syracuseStep 1555109 = 291583) (by norm_num)
theorem B1456805 : Blo 507795 1456805 := bbase (se 4 (by rfl) ⟨136575, by rfl⟩ : syracuseStep 1456805 = 273151) (by norm_num)
theorem B572089 : Blo 507795 572089 := bbase (se 2 (by rfl) ⟨214533, by rfl⟩ : syracuseStep 572089 = 429067) (by norm_num)
theorem B1718981 : Blo 507795 1718981 := bbase (se 4 (by rfl) ⟨161154, by rfl⟩ : syracuseStep 1718981 = 322309) (by norm_num)
theorem B965333 : Blo 507795 965333 := bbase (se 7 (by rfl) ⟨11312, by rfl⟩ : syracuseStep 965333 = 22625) (by norm_num)
theorem B2243285 : Blo 507795 2243285 := bbase (se 7 (by rfl) ⟨26288, by rfl⟩ : syracuseStep 2243285 = 52577) (by norm_num)
theorem B572125 : Blo 507795 572125 := bbase (se 3 (by rfl) ⟨107273, by rfl⟩ : syracuseStep 572125 = 214547) (by norm_num)
theorem B572161 : Blo 507795 572161 := bbase (se 2 (by rfl) ⟨214560, by rfl⟩ : syracuseStep 572161 = 429121) (by norm_num)
theorem B1555205 : Blo 507795 1555205 := bbase (se 4 (by rfl) ⟨145800, by rfl⟩ : syracuseStep 1555205 = 291601) (by norm_num)
theorem B572197 : Blo 507795 572197 := bbase (se 4 (by rfl) ⟨53643, by rfl⟩ : syracuseStep 572197 = 107287) (by norm_num)
theorem B572233 : Blo 507795 572233 := bbase (se 2 (by rfl) ⟨214587, by rfl⟩ : syracuseStep 572233 = 429175) (by norm_num)
theorem B572269 : Blo 507795 572269 := bbase (se 3 (by rfl) ⟨107300, by rfl⟩ : syracuseStep 572269 = 214601) (by norm_num)
theorem B572305 : Blo 507795 572305 := bbase (se 2 (by rfl) ⟨214614, by rfl⟩ : syracuseStep 572305 = 429229) (by norm_num)
theorem B4897685 : Blo 507795 4897685 := bbase (se 6 (by rfl) ⟨114789, by rfl⟩ : syracuseStep 4897685 = 229579) (by norm_num)
theorem B1293205 : Blo 507795 1293205 := bbase (se 6 (by rfl) ⟨30309, by rfl⟩ : syracuseStep 1293205 = 60619) (by norm_num)
theorem B572341 : Blo 507795 572341 := bbase (se 5 (by rfl) ⟨26828, by rfl⟩ : syracuseStep 572341 = 53657) (by norm_num)
theorem B572377 : Blo 507795 572377 := bbase (se 2 (by rfl) ⟨214641, by rfl⟩ : syracuseStep 572377 = 429283) (by norm_num)
theorem B965621 : Blo 507795 965621 := bbase (se 5 (by rfl) ⟨45263, by rfl⟩ : syracuseStep 965621 = 90527) (by norm_num)
theorem B572413 : Blo 507795 572413 := bbase (se 3 (by rfl) ⟨107327, by rfl⟩ : syracuseStep 572413 = 214655) (by norm_num)
theorem B1293317 : Blo 507795 1293317 := bbase (se 4 (by rfl) ⟨121248, by rfl⟩ : syracuseStep 1293317 = 242497) (by norm_num)
theorem B572449 : Blo 507795 572449 := bbase (se 2 (by rfl) ⟨214668, by rfl⟩ : syracuseStep 572449 = 429337) (by norm_num)
theorem B572485 : Blo 507795 572485 := bbase (se 4 (by rfl) ⟨53670, by rfl⟩ : syracuseStep 572485 = 107341) (by norm_num)
theorem B572521 : Blo 507795 572521 := bbase (se 2 (by rfl) ⟨214695, by rfl⟩ : syracuseStep 572521 = 429391) (by norm_num)
theorem B1719413 : Blo 507795 1719413 := bbase (se 5 (by rfl) ⟨80597, by rfl⟩ : syracuseStep 1719413 = 161195) (by norm_num)
theorem B965773 : Blo 507795 965773 := bbase (se 3 (by rfl) ⟨181082, by rfl⟩ : syracuseStep 965773 = 362165) (by norm_num)
theorem B572557 : Blo 507795 572557 := bbase (se 3 (by rfl) ⟨107354, by rfl⟩ : syracuseStep 572557 = 214709) (by norm_num)
theorem B572593 : Blo 507795 572593 := bbase (se 2 (by rfl) ⟨214722, by rfl⟩ : syracuseStep 572593 = 429445) (by norm_num)
theorem B1293509 : Blo 507795 1293509 := bbase (se 4 (by rfl) ⟨121266, by rfl⟩ : syracuseStep 1293509 = 242533) (by norm_num)
theorem B572629 : Blo 507795 572629 := bbase (se 7 (by rfl) ⟨6710, by rfl⟩ : syracuseStep 572629 = 13421) (by norm_num)
theorem B1227997 : Blo 507795 1227997 := bbase (se 3 (by rfl) ⟨230249, by rfl⟩ : syracuseStep 1227997 = 460499) (by norm_num)
theorem B572665 : Blo 507795 572665 := bbase (se 2 (by rfl) ⟨214749, by rfl⟩ : syracuseStep 572665 = 429499) (by norm_num)
theorem B933125 : Blo 507795 933125 := bbase (se 4 (by rfl) ⟨87480, by rfl⟩ : syracuseStep 933125 = 174961) (by norm_num)
theorem B572701 : Blo 507795 572701 := bbase (se 3 (by rfl) ⟨107381, by rfl⟩ : syracuseStep 572701 = 214763) (by norm_num)
theorem B572737 : Blo 507795 572737 := bbase (se 2 (by rfl) ⟨214776, by rfl⟩ : syracuseStep 572737 = 429553) (by norm_num)
theorem B2178373 : Blo 507795 2178373 := bbase (se 4 (by rfl) ⟨204222, by rfl⟩ : syracuseStep 2178373 = 408445) (by norm_num)
theorem B2178389 : Blo 507795 2178389 := bbase (se 11 (by rfl) ⟨1595, by rfl⟩ : syracuseStep 2178389 = 3191) (by norm_num)
theorem B572773 : Blo 507795 572773 := bbase (se 4 (by rfl) ⟨53697, by rfl⟩ : syracuseStep 572773 = 107395) (by norm_num)
theorem B572809 : Blo 507795 572809 := bbase (se 2 (by rfl) ⟨214803, by rfl⟩ : syracuseStep 572809 = 429607) (by norm_num)
theorem B1228189 : Blo 507795 1228189 := bbase (se 3 (by rfl) ⟨230285, by rfl⟩ : syracuseStep 1228189 = 460571) (by norm_num)
theorem B572845 : Blo 507795 572845 := bbase (se 3 (by rfl) ⟨107408, by rfl⟩ : syracuseStep 572845 = 214817) (by norm_num)
theorem B966077 : Blo 507795 966077 := bbase (se 3 (by rfl) ⟨181139, by rfl⟩ : syracuseStep 966077 = 362279) (by norm_num)
theorem B1228229 : Blo 507795 1228229 := bbase (se 4 (by rfl) ⟨115146, by rfl⟩ : syracuseStep 1228229 = 230293) (by norm_num)
theorem B572881 : Blo 507795 572881 := bbase (se 2 (by rfl) ⟨214830, by rfl⟩ : syracuseStep 572881 = 429661) (by norm_num)
theorem B2571749 : Blo 507795 2571749 := bbase (se 4 (by rfl) ⟨241101, by rfl⟩ : syracuseStep 2571749 = 482203) (by norm_num)
theorem B572917 : Blo 507795 572917 := bbase (se 5 (by rfl) ⟨26855, by rfl⟩ : syracuseStep 572917 = 53711) (by norm_num)
theorem B572953 : Blo 507795 572953 := bbase (se 2 (by rfl) ⟨214857, by rfl⟩ : syracuseStep 572953 = 429715) (by norm_num)
theorem B1293853 : Blo 507795 1293853 := bbase (se 3 (by rfl) ⟨242597, by rfl⟩ : syracuseStep 1293853 = 485195) (by norm_num)
theorem B1719845 : Blo 507795 1719845 := bbase (se 4 (by rfl) ⟨161235, by rfl⟩ : syracuseStep 1719845 = 322471) (by norm_num)
theorem B572989 : Blo 507795 572989 := bbase (se 3 (by rfl) ⟨107435, by rfl⟩ : syracuseStep 572989 = 214871) (by norm_num)
theorem B573025 : Blo 507795 573025 := bbase (se 2 (by rfl) ⟨214884, by rfl⟩ : syracuseStep 573025 = 429769) (by norm_num)
theorem B573061 : Blo 507795 573061 := bbase (se 4 (by rfl) ⟨53724, by rfl⟩ : syracuseStep 573061 = 107449) (by norm_num)
theorem B1293965 : Blo 507795 1293965 := bbase (se 3 (by rfl) ⟨242618, by rfl⟩ : syracuseStep 1293965 = 485237) (by norm_num)
theorem B573097 : Blo 507795 573097 := bbase (se 2 (by rfl) ⟨214911, by rfl⟩ : syracuseStep 573097 = 429823) (by norm_num)
theorem B573133 : Blo 507795 573133 := bbase (se 3 (by rfl) ⟨107462, by rfl⟩ : syracuseStep 573133 = 214925) (by norm_num)
theorem B1228517 : Blo 507795 1228517 := bbase (se 4 (by rfl) ⟨115173, by rfl⟩ : syracuseStep 1228517 = 230347) (by norm_num)
theorem B573169 : Blo 507795 573169 := bbase (se 2 (by rfl) ⟨214938, by rfl⟩ : syracuseStep 573169 = 429877) (by norm_num)
theorem B573205 : Blo 507795 573205 := bbase (se 6 (by rfl) ⟨13434, by rfl⟩ : syracuseStep 573205 = 26869) (by norm_num)
theorem B573241 : Blo 507795 573241 := bbase (se 2 (by rfl) ⟨214965, by rfl⟩ : syracuseStep 573241 = 429931) (by norm_num)
theorem B1294157 : Blo 507795 1294157 := bbase (se 3 (by rfl) ⟨242654, by rfl⟩ : syracuseStep 1294157 = 485309) (by norm_num)
theorem B573277 : Blo 507795 573277 := bbase (se 3 (by rfl) ⟨107489, by rfl⟩ : syracuseStep 573277 = 214979) (by norm_num)
theorem B573313 : Blo 507795 573313 := bbase (se 2 (by rfl) ⟨214992, by rfl⟩ : syracuseStep 573313 = 429985) (by norm_num)
theorem B573349 : Blo 507795 573349 := bbase (se 4 (by rfl) ⟨53751, by rfl⟩ : syracuseStep 573349 = 107503) (by norm_num)
theorem B573385 : Blo 507795 573385 := bbase (se 2 (by rfl) ⟨215019, by rfl⟩ : syracuseStep 573385 = 430039) (by norm_num)
theorem B1720277 : Blo 507795 1720277 := bbase (se 7 (by rfl) ⟨20159, by rfl⟩ : syracuseStep 1720277 = 40319) (by norm_num)
theorem B573421 : Blo 507795 573421 := bbase (se 3 (by rfl) ⟨107516, by rfl⟩ : syracuseStep 573421 = 215033) (by norm_num)
theorem B573457 : Blo 507795 573457 := bbase (se 2 (by rfl) ⟨215046, by rfl⟩ : syracuseStep 573457 = 430093) (by norm_num)
theorem B573493 : Blo 507795 573493 := bbase (se 5 (by rfl) ⟨26882, by rfl⟩ : syracuseStep 573493 = 53765) (by norm_num)
theorem B573529 : Blo 507795 573529 := bbase (se 2 (by rfl) ⟨215073, by rfl⟩ : syracuseStep 573529 = 430147) (by norm_num)
theorem B573565 : Blo 507795 573565 := bbase (se 3 (by rfl) ⟨107543, by rfl⟩ : syracuseStep 573565 = 215087) (by norm_num)
theorem B573601 : Blo 507795 573601 := bbase (se 2 (by rfl) ⟨215100, by rfl⟩ : syracuseStep 573601 = 430201) (by norm_num)
theorem B1294501 : Blo 507795 1294501 := bbase (se 4 (by rfl) ⟨121359, by rfl⟩ : syracuseStep 1294501 = 242719) (by norm_num)
theorem B966829 : Blo 507795 966829 := bbase (se 3 (by rfl) ⟨181280, by rfl⟩ : syracuseStep 966829 = 362561) (by norm_num)
theorem B573637 : Blo 507795 573637 := bbase (se 4 (by rfl) ⟨53778, by rfl⟩ : syracuseStep 573637 = 107557) (by norm_num)
theorem B573673 : Blo 507795 573673 := bbase (se 2 (by rfl) ⟨215127, by rfl⟩ : syracuseStep 573673 = 430255) (by norm_num)
theorem B573709 : Blo 507795 573709 := bbase (se 3 (by rfl) ⟨107570, by rfl⟩ : syracuseStep 573709 = 215141) (by norm_num)
theorem B1294613 : Blo 507795 1294613 := bbase (se 6 (by rfl) ⟨30342, by rfl⟩ : syracuseStep 1294613 = 60685) (by norm_num)
theorem B573745 : Blo 507795 573745 := bbase (se 2 (by rfl) ⟨215154, by rfl⟩ : syracuseStep 573745 = 430309) (by norm_num)
theorem B966973 : Blo 507795 966973 := bbase (se 3 (by rfl) ⟨181307, by rfl⟩ : syracuseStep 966973 = 362615) (by norm_num)
theorem B9290069 : Blo 507795 9290069 := bbase (se 10 (by rfl) ⟨13608, by rfl⟩ : syracuseStep 9290069 = 27217) (by norm_num)
theorem B573781 : Blo 507795 573781 := bbase (se 10 (by rfl) ⟨840, by rfl⟩ : syracuseStep 573781 = 1681) (by norm_num)
theorem B573817 : Blo 507795 573817 := bbase (se 2 (by rfl) ⟨215181, by rfl⟩ : syracuseStep 573817 = 430363) (by norm_num)
theorem B1720709 : Blo 507795 1720709 := bbase (se 4 (by rfl) ⟨161316, by rfl⟩ : syracuseStep 1720709 = 322633) (by norm_num)
theorem B573853 : Blo 507795 573853 := bbase (se 3 (by rfl) ⟨107597, by rfl⟩ : syracuseStep 573853 = 215195) (by norm_num)
theorem B573889 : Blo 507795 573889 := bbase (se 2 (by rfl) ⟨215208, by rfl⟩ : syracuseStep 573889 = 430417) (by norm_num)
theorem B1294805 : Blo 507795 1294805 := bbase (se 7 (by rfl) ⟨15173, by rfl⟩ : syracuseStep 1294805 = 30347) (by norm_num)
theorem B967133 : Blo 507795 967133 := bbase (se 3 (by rfl) ⟨181337, by rfl⟩ : syracuseStep 967133 = 362675) (by norm_num)
theorem B573925 : Blo 507795 573925 := bbase (se 4 (by rfl) ⟨53805, by rfl⟩ : syracuseStep 573925 = 107611) (by norm_num)
theorem B573961 : Blo 507795 573961 := bbase (se 2 (by rfl) ⟨215235, by rfl⟩ : syracuseStep 573961 = 430471) (by norm_num)
theorem B573997 : Blo 507795 573997 := bbase (se 3 (by rfl) ⟨107624, by rfl⟩ : syracuseStep 573997 = 215249) (by norm_num)
theorem B574033 : Blo 507795 574033 := bbase (se 2 (by rfl) ⟨215262, by rfl⟩ : syracuseStep 574033 = 430525) (by norm_num)
theorem B967277 : Blo 507795 967277 := bbase (se 3 (by rfl) ⟨181364, by rfl⟩ : syracuseStep 967277 = 362729) (by norm_num)
theorem B574069 : Blo 507795 574069 := bbase (se 5 (by rfl) ⟨26909, by rfl⟩ : syracuseStep 574069 = 53819) (by norm_num)
theorem B574105 : Blo 507795 574105 := bbase (se 2 (by rfl) ⟨215289, by rfl⟩ : syracuseStep 574105 = 430579) (by norm_num)
theorem B574141 : Blo 507795 574141 := bbase (se 3 (by rfl) ⟨107651, by rfl⟩ : syracuseStep 574141 = 215303) (by norm_num)
theorem B574177 : Blo 507795 574177 := bbase (se 2 (by rfl) ⟨215316, by rfl⟩ : syracuseStep 574177 = 430633) (by norm_num)
theorem B2573045 : Blo 507795 2573045 := bbase (se 5 (by rfl) ⟨120611, by rfl⟩ : syracuseStep 2573045 = 241223) (by norm_num)
theorem B574213 : Blo 507795 574213 := bbase (se 4 (by rfl) ⟨53832, by rfl⟩ : syracuseStep 574213 = 107665) (by norm_num)
theorem B574249 : Blo 507795 574249 := bbase (se 2 (by rfl) ⟨215343, by rfl⟩ : syracuseStep 574249 = 430687) (by norm_num)
theorem B1295149 : Blo 507795 1295149 := bbase (se 3 (by rfl) ⟨242840, by rfl⟩ : syracuseStep 1295149 = 485681) (by norm_num)
theorem B1721141 : Blo 507795 1721141 := bbase (se 5 (by rfl) ⟨80678, by rfl⟩ : syracuseStep 1721141 = 161357) (by norm_num)
theorem B3687221 : Blo 507795 3687221 := bbase (se 5 (by rfl) ⟨172838, by rfl⟩ : syracuseStep 3687221 = 345677) (by norm_num)
theorem B574285 : Blo 507795 574285 := bbase (se 3 (by rfl) ⟨107678, by rfl⟩ : syracuseStep 574285 = 215357) (by norm_num)
theorem B574321 : Blo 507795 574321 := bbase (se 2 (by rfl) ⟨215370, by rfl⟩ : syracuseStep 574321 = 430741) (by norm_num)
theorem B967565 : Blo 507795 967565 := bbase (se 3 (by rfl) ⟨181418, by rfl⟩ : syracuseStep 967565 = 362837) (by norm_num)
theorem B574357 : Blo 507795 574357 := bbase (se 6 (by rfl) ⟨13461, by rfl⟩ : syracuseStep 574357 = 26923) (by norm_num)
theorem B1295261 : Blo 507795 1295261 := bbase (se 3 (by rfl) ⟨242861, by rfl⟩ : syracuseStep 1295261 = 485723) (by norm_num)
theorem B574393 : Blo 507795 574393 := bbase (se 2 (by rfl) ⟨215397, by rfl⟩ : syracuseStep 574393 = 430795) (by norm_num)
theorem B574429 : Blo 507795 574429 := bbase (se 3 (by rfl) ⟨107705, by rfl⟩ : syracuseStep 574429 = 215411) (by norm_num)
theorem B574465 : Blo 507795 574465 := bbase (se 2 (by rfl) ⟨215424, by rfl⟩ : syracuseStep 574465 = 430849) (by norm_num)
theorem B1033253 : Blo 507795 1033253 := bbase (se 4 (by rfl) ⟨96867, by rfl⟩ : syracuseStep 1033253 = 193735) (by norm_num)
theorem B967717 : Blo 507795 967717 := bbase (se 4 (by rfl) ⟨90723, by rfl⟩ : syracuseStep 967717 = 181447) (by norm_num)
theorem B574501 : Blo 507795 574501 := bbase (se 4 (by rfl) ⟨53859, by rfl⟩ : syracuseStep 574501 = 107719) (by norm_num)
theorem B574537 : Blo 507795 574537 := bbase (se 2 (by rfl) ⟨215451, by rfl⟩ : syracuseStep 574537 = 430903) (by norm_num)
theorem B1295453 : Blo 507795 1295453 := bbase (se 3 (by rfl) ⟨242897, by rfl⟩ : syracuseStep 1295453 = 485795) (by norm_num)
theorem B574573 : Blo 507795 574573 := bbase (se 3 (by rfl) ⟨107732, by rfl⟩ : syracuseStep 574573 = 215465) (by norm_num)
theorem B574609 : Blo 507795 574609 := bbase (se 2 (by rfl) ⟨215478, by rfl⟩ : syracuseStep 574609 = 430957) (by norm_num)
theorem B574645 : Blo 507795 574645 := bbase (se 5 (by rfl) ⟨26936, by rfl⟩ : syracuseStep 574645 = 53873) (by norm_num)
theorem B574681 : Blo 507795 574681 := bbase (se 2 (by rfl) ⟨215505, by rfl⟩ : syracuseStep 574681 = 431011) (by norm_num)
theorem B1721573 : Blo 507795 1721573 := bbase (se 4 (by rfl) ⟨161397, by rfl⟩ : syracuseStep 1721573 = 322795) (by norm_num)
theorem B574717 : Blo 507795 574717 := bbase (se 3 (by rfl) ⟨107759, by rfl⟩ : syracuseStep 574717 = 215519) (by norm_num)
theorem B574753 : Blo 507795 574753 := bbase (se 2 (by rfl) ⟨215532, by rfl⟩ : syracuseStep 574753 = 431065) (by norm_num)
theorem B574789 : Blo 507795 574789 := bbase (se 4 (by rfl) ⟨53886, by rfl⟩ : syracuseStep 574789 = 107773) (by norm_num)
theorem B968021 : Blo 507795 968021 := bbase (se 12 (by rfl) ⟨354, by rfl⟩ : syracuseStep 968021 = 709) (by norm_num)
theorem B574825 : Blo 507795 574825 := bbase (se 2 (by rfl) ⟨215559, by rfl⟩ : syracuseStep 574825 = 431119) (by norm_num)
theorem B574861 : Blo 507795 574861 := bbase (se 3 (by rfl) ⟨107786, by rfl⟩ : syracuseStep 574861 = 215573) (by norm_num)
theorem B574897 : Blo 507795 574897 := bbase (se 2 (by rfl) ⟨215586, by rfl⟩ : syracuseStep 574897 = 431173) (by norm_num)
theorem B574933 : Blo 507795 574933 := bbase (se 7 (by rfl) ⟨6737, by rfl⟩ : syracuseStep 574933 = 13475) (by norm_num)
theorem B574969 : Blo 507795 574969 := bbase (se 2 (by rfl) ⟨215613, by rfl⟩ : syracuseStep 574969 = 431227) (by norm_num)
theorem B575005 : Blo 507795 575005 := bbase (se 3 (by rfl) ⟨107813, by rfl⟩ : syracuseStep 575005 = 215627) (by norm_num)
theorem B2180645 : Blo 507795 2180645 := bbase (se 4 (by rfl) ⟨204435, by rfl⟩ : syracuseStep 2180645 = 408871) (by norm_num)
theorem B869933 : Blo 507795 869933 := bbase (se 3 (by rfl) ⟨163112, by rfl⟩ : syracuseStep 869933 = 326225) (by norm_num)
theorem B3884597 : Blo 507795 3884597 := bbase (se 5 (by rfl) ⟨182090, by rfl⟩ : syracuseStep 3884597 = 364181) (by norm_num)
theorem B575041 : Blo 507795 575041 := bbase (se 2 (by rfl) ⟨215640, by rfl⟩ : syracuseStep 575041 = 431281) (by norm_num)
theorem B1033813 : Blo 507795 1033813 := bbase (se 8 (by rfl) ⟨6057, by rfl⟩ : syracuseStep 1033813 = 12115) (by norm_num)
theorem B575077 : Blo 507795 575077 := bbase (se 4 (by rfl) ⟨53913, by rfl⟩ : syracuseStep 575077 = 107827) (by norm_num)
theorem B575113 : Blo 507795 575113 := bbase (se 2 (by rfl) ⟨215667, by rfl⟩ : syracuseStep 575113 = 431335) (by norm_num)
theorem B1722005 : Blo 507795 1722005 := bbase (se 6 (by rfl) ⟨40359, by rfl⟩ : syracuseStep 1722005 = 80719) (by norm_num)
theorem B575149 : Blo 507795 575149 := bbase (se 3 (by rfl) ⟨107840, by rfl⟩ : syracuseStep 575149 = 215681) (by norm_num)
theorem B575185 : Blo 507795 575185 := bbase (se 2 (by rfl) ⟨215694, by rfl⟩ : syracuseStep 575185 = 431389) (by norm_num)
theorem B575221 : Blo 507795 575221 := bbase (se 5 (by rfl) ⟨26963, by rfl⟩ : syracuseStep 575221 = 53927) (by norm_num)
theorem B575257 : Blo 507795 575257 := bbase (se 2 (by rfl) ⟨215721, by rfl⟩ : syracuseStep 575257 = 431443) (by norm_num)
theorem B575293 : Blo 507795 575293 := bbase (se 3 (by rfl) ⟨107867, by rfl⟩ : syracuseStep 575293 = 215735) (by norm_num)
theorem B870221 : Blo 507795 870221 := bbase (se 3 (by rfl) ⟨163166, by rfl⟩ : syracuseStep 870221 = 326333) (by norm_num)
theorem B575329 : Blo 507795 575329 := bbase (se 2 (by rfl) ⟨215748, by rfl⟩ : syracuseStep 575329 = 431497) (by norm_num)
theorem B542581 : Blo 507795 542581 := bbase (se 5 (by rfl) ⟨25433, by rfl⟩ : syracuseStep 542581 = 50867) (by norm_num)
theorem B575365 : Blo 507795 575365 := bbase (se 4 (by rfl) ⟨53940, by rfl⟩ : syracuseStep 575365 = 107881) (by norm_num)
theorem B575401 : Blo 507795 575401 := bbase (se 2 (by rfl) ⟨215775, by rfl⟩ : syracuseStep 575401 = 431551) (by norm_num)
theorem B575437 : Blo 507795 575437 := bbase (se 3 (by rfl) ⟨107894, by rfl⟩ : syracuseStep 575437 = 215789) (by norm_num)
theorem B542701 : Blo 507795 542701 := bbase (se 3 (by rfl) ⟨101756, by rfl⟩ : syracuseStep 542701 = 203513) (by norm_num)
theorem B575473 : Blo 507795 575473 := bbase (se 2 (by rfl) ⟨215802, by rfl⟩ : syracuseStep 575473 = 431605) (by norm_num)
theorem B2574341 : Blo 507795 2574341 := bbase (se 4 (by rfl) ⟨241344, by rfl⟩ : syracuseStep 2574341 = 482689) (by norm_num)
theorem B575509 : Blo 507795 575509 := bbase (se 6 (by rfl) ⟨13488, by rfl⟩ : syracuseStep 575509 = 26977) (by norm_num)
theorem B575545 : Blo 507795 575545 := bbase (se 2 (by rfl) ⟨215829, by rfl⟩ : syracuseStep 575545 = 431659) (by norm_num)
theorem B968773 : Blo 507795 968773 := bbase (se 4 (by rfl) ⟨90822, by rfl⟩ : syracuseStep 968773 = 181645) (by norm_num)
theorem B1722437 : Blo 507795 1722437 := bbase (se 4 (by rfl) ⟨161478, by rfl⟩ : syracuseStep 1722437 = 322957) (by norm_num)
theorem B575581 : Blo 507795 575581 := bbase (se 3 (by rfl) ⟨107921, by rfl⟩ : syracuseStep 575581 = 215843) (by norm_num)
theorem B575617 : Blo 507795 575617 := bbase (se 2 (by rfl) ⟨215856, by rfl⟩ : syracuseStep 575617 = 431713) (by norm_num)
theorem B575653 : Blo 507795 575653 := bbase (se 4 (by rfl) ⟨53967, by rfl⟩ : syracuseStep 575653 = 107935) (by norm_num)
theorem B575689 : Blo 507795 575689 := bbase (se 2 (by rfl) ⟨215883, by rfl⟩ : syracuseStep 575689 = 431767) (by norm_num)
theorem B968917 : Blo 507795 968917 := bbase (se 7 (by rfl) ⟨11354, by rfl⟩ : syracuseStep 968917 = 22709) (by norm_num)
theorem B772325 : Blo 507795 772325 := bbase (se 4 (by rfl) ⟨72405, by rfl⟩ : syracuseStep 772325 = 144811) (by norm_num)
theorem B542953 : Blo 507795 542953 := bbase (se 2 (by rfl) ⟨203607, by rfl⟩ : syracuseStep 542953 = 407215) (by norm_num)
theorem B542957 : Blo 507795 542957 := bbase (se 3 (by rfl) ⟨101804, by rfl⟩ : syracuseStep 542957 = 203609) (by norm_num)
theorem B575725 : Blo 507795 575725 := bbase (se 3 (by rfl) ⟨107948, by rfl⟩ : syracuseStep 575725 = 215897) (by norm_num)
theorem B575761 : Blo 507795 575761 := bbase (se 2 (by rfl) ⟨215910, by rfl⟩ : syracuseStep 575761 = 431821) (by norm_num)
theorem B969077 : Blo 507795 969077 := bbase (se 5 (by rfl) ⟨45425, by rfl⟩ : syracuseStep 969077 = 90851) (by norm_num)
theorem B1722869 : Blo 507795 1722869 := bbase (se 5 (by rfl) ⟨80759, by rfl⟩ : syracuseStep 1722869 = 161519) (by norm_num)
theorem B969221 : Blo 507795 969221 := bbase (se 4 (by rfl) ⟨90864, by rfl⟩ : syracuseStep 969221 = 181729) (by norm_num)
theorem B3263125 : Blo 507795 3263125 := bbase (se 6 (by rfl) ⟨76479, by rfl⟩ : syracuseStep 3263125 = 152959) (by norm_num)
theorem B543521 : Blo 507795 543521 := bbase (se 2 (by rfl) ⟨203820, by rfl⟩ : syracuseStep 543521 = 407641) (by norm_num)
theorem B969509 : Blo 507795 969509 := bbase (se 4 (by rfl) ⟨90891, by rfl⟩ : syracuseStep 969509 = 181783) (by norm_num)
theorem B773029 : Blo 507795 773029 := bbase (se 4 (by rfl) ⟨72471, by rfl⟩ : syracuseStep 773029 = 144943) (by norm_num)
theorem B1723301 : Blo 507795 1723301 := bbase (se 4 (by rfl) ⟨161559, by rfl⟩ : syracuseStep 1723301 = 323119) (by norm_num)
theorem B969661 : Blo 507795 969661 := bbase (se 3 (by rfl) ⟨181811, by rfl⟩ : syracuseStep 969661 = 363623) (by norm_num)
theorem B543709 : Blo 507795 543709 := bbase (se 3 (by rfl) ⟨101945, by rfl⟩ : syracuseStep 543709 = 203891) (by norm_num)
theorem B969965 : Blo 507795 969965 := bbase (se 3 (by rfl) ⟨181868, by rfl⟩ : syracuseStep 969965 = 363737) (by norm_num)
theorem B2575637 : Blo 507795 2575637 := bbase (se 6 (by rfl) ⟨60366, by rfl⟩ : syracuseStep 2575637 = 120733) (by norm_num)
theorem B1723733 : Blo 507795 1723733 := bbase (se 11 (by rfl) ⟨1262, by rfl⟩ : syracuseStep 1723733 = 2525) (by norm_num)
theorem B1035605 : Blo 507795 1035605 := bbase (se 11 (by rfl) ⟨758, by rfl⟩ : syracuseStep 1035605 = 1517) (by norm_num)
theorem B871973 : Blo 507795 871973 := bbase (se 4 (by rfl) ⟨81747, by rfl⟩ : syracuseStep 871973 = 163495) (by norm_num)
theorem B1166989 : Blo 507795 1166989 := bbase (se 3 (by rfl) ⟨218810, by rfl⟩ : syracuseStep 1166989 = 437621) (by norm_num)
theorem B642745 : Blo 507795 642745 := bbase (se 2 (by rfl) ⟨241029, by rfl⟩ : syracuseStep 642745 = 482059) (by norm_num)
theorem B1724165 : Blo 507795 1724165 := bbase (se 4 (by rfl) ⟨161640, by rfl⟩ : syracuseStep 1724165 = 323281) (by norm_num)
theorem B544529 : Blo 507795 544529 := bbase (se 2 (by rfl) ⟨204198, by rfl⟩ : syracuseStep 544529 = 408397) (by norm_num)
theorem B642917 : Blo 507795 642917 := bbase (se 4 (by rfl) ⟨60273, by rfl⟩ : syracuseStep 642917 = 120547) (by norm_num)
theorem B642973 : Blo 507795 642973 := bbase (se 3 (by rfl) ⟨120557, by rfl⟩ : syracuseStep 642973 = 241115) (by norm_num)
theorem B970717 : Blo 507795 970717 := bbase (se 3 (by rfl) ⟨182009, by rfl⟩ : syracuseStep 970717 = 364019) (by norm_num)
theorem B2543605 : Blo 507795 2543605 := bbase (se 5 (by rfl) ⟨119231, by rfl⟩ : syracuseStep 2543605 = 238463) (by norm_num)
theorem B643069 : Blo 507795 643069 := bbase (se 3 (by rfl) ⟨120575, by rfl⟩ : syracuseStep 643069 = 241151) (by norm_num)
theorem B970861 : Blo 507795 970861 := bbase (se 3 (by rfl) ⟨182036, by rfl⟩ : syracuseStep 970861 = 364073) (by norm_num)
theorem B2445461 : Blo 507795 2445461 := bbase (se 6 (by rfl) ⟨57315, by rfl⟩ : syracuseStep 2445461 = 114631) (by norm_num)
theorem B643241 : Blo 507795 643241 := bbase (se 2 (by rfl) ⟨241215, by rfl⟩ : syracuseStep 643241 = 482431) (by norm_num)
theorem B2904245 : Blo 507795 2904245 := bbase (se 5 (by rfl) ⟨136136, by rfl⟩ : syracuseStep 2904245 = 272273) (by norm_num)
theorem B1724597 : Blo 507795 1724597 := bbase (se 5 (by rfl) ⟨80840, by rfl⟩ : syracuseStep 1724597 = 161681) (by norm_num)
theorem B544973 : Blo 507795 544973 := bbase (se 3 (by rfl) ⟨102182, by rfl⟩ : syracuseStep 544973 = 204365) (by norm_num)
theorem B643297 : Blo 507795 643297 := bbase (se 2 (by rfl) ⟨241236, by rfl⟩ : syracuseStep 643297 = 482473) (by norm_num)
theorem B971021 : Blo 507795 971021 := bbase (se 3 (by rfl) ⟨182066, by rfl⟩ : syracuseStep 971021 = 364133) (by norm_num)
theorem B643393 : Blo 507795 643393 := bbase (se 2 (by rfl) ⟨241272, by rfl⟩ : syracuseStep 643393 = 482545) (by norm_num)
theorem B610669 : Blo 507795 610669 := bbase (se 3 (by rfl) ⟨114500, by rfl⟩ : syracuseStep 610669 = 229001) (by norm_num)
theorem B610673 : Blo 507795 610673 := bbase (se 2 (by rfl) ⟨229002, by rfl⟩ : syracuseStep 610673 = 458005) (by norm_num)
theorem B971165 : Blo 507795 971165 := bbase (se 3 (by rfl) ⟨182093, by rfl⟩ : syracuseStep 971165 = 364187) (by norm_num)
theorem B545221 : Blo 507795 545221 := bbase (se 4 (by rfl) ⟨51114, by rfl⟩ : syracuseStep 545221 = 102229) (by norm_num)
theorem B643565 : Blo 507795 643565 := bbase (se 3 (by rfl) ⟨120668, by rfl⟩ : syracuseStep 643565 = 241337) (by norm_num)
theorem B643621 : Blo 507795 643621 := bbase (se 4 (by rfl) ⟨60339, by rfl⟩ : syracuseStep 643621 = 120679) (by norm_num)
theorem B2576933 : Blo 507795 2576933 := bbase (se 4 (by rfl) ⟨241587, by rfl⟩ : syracuseStep 2576933 = 483175) (by norm_num)
theorem B1725029 : Blo 507795 1725029 := bbase (se 4 (by rfl) ⟨161721, by rfl⟩ : syracuseStep 1725029 = 323443) (by norm_num)
theorem B643717 : Blo 507795 643717 := bbase (se 4 (by rfl) ⟨60348, by rfl⟩ : syracuseStep 643717 = 120697) (by norm_num)
theorem B971453 : Blo 507795 971453 := bbase (se 3 (by rfl) ⟨182147, by rfl⟩ : syracuseStep 971453 = 364295) (by norm_num)
theorem B1626821 : Blo 507795 1626821 := bbase (se 4 (by rfl) ⟨152514, by rfl⟩ : syracuseStep 1626821 = 305029) (by norm_num)
theorem B840389 : Blo 507795 840389 := bbase (se 4 (by rfl) ⟨78786, by rfl⟩ : syracuseStep 840389 = 157573) (by norm_num)
theorem B643889 : Blo 507795 643889 := bbase (se 2 (by rfl) ⟨241458, by rfl⟩ : syracuseStep 643889 = 482917) (by norm_num)
theorem B971605 : Blo 507795 971605 := bbase (se 9 (by rfl) ⟨2846, by rfl⟩ : syracuseStep 971605 = 5693) (by norm_num)
theorem B611173 : Blo 507795 611173 := bbase (se 4 (by rfl) ⟨57297, by rfl⟩ : syracuseStep 611173 = 114595) (by norm_num)
theorem B643945 : Blo 507795 643945 := bbase (se 2 (by rfl) ⟨241479, by rfl⟩ : syracuseStep 643945 = 482959) (by norm_num)
theorem B545653 : Blo 507795 545653 := bbase (se 5 (by rfl) ⟨25577, by rfl⟩ : syracuseStep 545653 = 51155) (by norm_num)
theorem B545725 : Blo 507795 545725 := bbase (se 3 (by rfl) ⟨102323, by rfl⟩ : syracuseStep 545725 = 204647) (by norm_num)
theorem B644041 : Blo 507795 644041 := bbase (se 2 (by rfl) ⟨241515, by rfl⟩ : syracuseStep 644041 = 483031) (by norm_num)
theorem B775117 : Blo 507795 775117 := bbase (se 3 (by rfl) ⟨145334, by rfl⟩ : syracuseStep 775117 = 290669) (by norm_num)
theorem B1725461 : Blo 507795 1725461 := bbase (se 6 (by rfl) ⟨40440, by rfl⟩ : syracuseStep 1725461 = 80881) (by norm_num)
theorem B644213 : Blo 507795 644213 := bbase (se 5 (by rfl) ⟨30197, by rfl⟩ : syracuseStep 644213 = 60395) (by norm_num)
theorem B644269 : Blo 507795 644269 := bbase (se 3 (by rfl) ⟨120800, by rfl⟩ : syracuseStep 644269 = 241601) (by norm_num)
theorem B1660085 : Blo 507795 1660085 := bbase (se 5 (by rfl) ⟨77816, by rfl⟩ : syracuseStep 1660085 = 155633) (by norm_num)
theorem B611557 : Blo 507795 611557 := bbase (se 4 (by rfl) ⟨57333, by rfl⟩ : syracuseStep 611557 = 114667) (by norm_num)
theorem B644365 : Blo 507795 644365 := bbase (se 3 (by rfl) ⟨120818, by rfl⟩ : syracuseStep 644365 = 241637) (by norm_num)
theorem B546097 : Blo 507795 546097 := bbase (se 2 (by rfl) ⟨204786, by rfl⟩ : syracuseStep 546097 = 409573) (by norm_num)
theorem B2905429 : Blo 507795 2905429 := bbase (se 16 (by rfl) ⟨66, by rfl⟩ : syracuseStep 2905429 = 133) (by norm_num)
theorem B644537 : Blo 507795 644537 := bbase (se 2 (by rfl) ⟨241701, by rfl⟩ : syracuseStep 644537 = 483403) (by norm_num)
theorem B1725893 : Blo 507795 1725893 := bbase (se 4 (by rfl) ⟨161802, by rfl⟩ : syracuseStep 1725893 = 323605) (by norm_num)
theorem B2184677 : Blo 507795 2184677 := bbase (se 4 (by rfl) ⟨204813, by rfl⟩ : syracuseStep 2184677 = 409627) (by norm_num)
theorem B644593 : Blo 507795 644593 := bbase (se 2 (by rfl) ⟨241722, by rfl⟩ : syracuseStep 644593 = 483445) (by norm_num)
theorem B874037 : Blo 507795 874037 := bbase (se 5 (by rfl) ⟨40970, by rfl⟩ : syracuseStep 874037 = 81941) (by norm_num)
theorem B644689 : Blo 507795 644689 := bbase (se 2 (by rfl) ⟨241758, by rfl⟩ : syracuseStep 644689 = 483517) (by norm_num)
theorem B546473 : Blo 507795 546473 := bbase (se 2 (by rfl) ⟨204927, by rfl⟩ : syracuseStep 546473 = 409855) (by norm_num)
theorem B612049 : Blo 507795 612049 := bbase (se 2 (by rfl) ⟨229518, by rfl⟩ : syracuseStep 612049 = 459037) (by norm_num)
theorem B644861 : Blo 507795 644861 := bbase (se 3 (by rfl) ⟨120911, by rfl⟩ : syracuseStep 644861 = 241823) (by norm_num)
theorem B2578229 : Blo 507795 2578229 := bbase (se 5 (by rfl) ⟨120854, by rfl⟩ : syracuseStep 2578229 = 241709) (by norm_num)
theorem B644917 : Blo 507795 644917 := bbase (se 5 (by rfl) ⟨30230, by rfl⟩ : syracuseStep 644917 = 60461) (by norm_num)
theorem B1726325 : Blo 507795 1726325 := bbase (se 5 (by rfl) ⟨80921, by rfl⟩ : syracuseStep 1726325 = 161843) (by norm_num)
theorem B645013 : Blo 507795 645013 := bbase (se 6 (by rfl) ⟨15117, by rfl⟩ : syracuseStep 645013 = 30235) (by norm_num)
theorem B5789717 : Blo 507795 5789717 := bbase (se 6 (by rfl) ⟨135696, by rfl⟩ : syracuseStep 5789717 = 271393) (by norm_num)
theorem B645185 : Blo 507795 645185 := bbase (se 2 (by rfl) ⟨241944, by rfl⟩ : syracuseStep 645185 = 483889) (by norm_num)
theorem B612461 : Blo 507795 612461 := bbase (se 3 (by rfl) ⟨114836, by rfl⟩ : syracuseStep 612461 = 229673) (by norm_num)
theorem B645241 : Blo 507795 645241 := bbase (se 2 (by rfl) ⟨241965, by rfl⟩ : syracuseStep 645241 = 483931) (by norm_num)
theorem B645337 : Blo 507795 645337 := bbase (se 2 (by rfl) ⟨242001, by rfl⟩ : syracuseStep 645337 = 484003) (by norm_num)
theorem B776461 : Blo 507795 776461 := bbase (se 3 (by rfl) ⟨145586, by rfl⟩ : syracuseStep 776461 = 291173) (by norm_num)
theorem B1726757 : Blo 507795 1726757 := bbase (se 4 (by rfl) ⟨161883, by rfl⟩ : syracuseStep 1726757 = 323767) (by norm_num)
theorem B612721 : Blo 507795 612721 := bbase (se 2 (by rfl) ⟨229770, by rfl⟩ : syracuseStep 612721 = 459541) (by norm_num)
theorem B645509 : Blo 507795 645509 := bbase (se 4 (by rfl) ⟨60516, by rfl⟩ : syracuseStep 645509 = 121033) (by norm_num)
theorem B645565 : Blo 507795 645565 := bbase (se 3 (by rfl) ⟨121043, by rfl⟩ : syracuseStep 645565 = 242087) (by norm_num)
theorem B1628693 : Blo 507795 1628693 := bbase (se 6 (by rfl) ⟨38172, by rfl⟩ : syracuseStep 1628693 = 76345) (by norm_num)
theorem B645661 : Blo 507795 645661 := bbase (se 3 (by rfl) ⟨121061, by rfl⟩ : syracuseStep 645661 = 242123) (by norm_num)
theorem B612913 : Blo 507795 612913 := bbase (se 2 (by rfl) ⟨229842, by rfl⟩ : syracuseStep 612913 = 459685) (by norm_num)
theorem B612937 : Blo 507795 612937 := bbase (se 2 (by rfl) ⟨229851, by rfl⟩ : syracuseStep 612937 = 459703) (by norm_num)
theorem B612941 : Blo 507795 612941 := bbase (se 3 (by rfl) ⟨114926, by rfl⟩ : syracuseStep 612941 = 229853) (by norm_num)
theorem B645833 : Blo 507795 645833 := bbase (se 2 (by rfl) ⟨242187, by rfl⟩ : syracuseStep 645833 = 484375) (by norm_num)
theorem B514769 : Blo 507795 514769 := bbase (se 2 (by rfl) ⟨193038, by rfl⟩ : syracuseStep 514769 = 386077) (by norm_num)
theorem B1727189 : Blo 507795 1727189 := bbase (se 7 (by rfl) ⟨20240, by rfl⟩ : syracuseStep 1727189 = 40481) (by norm_num)
theorem B645889 : Blo 507795 645889 := bbase (se 2 (by rfl) ⟨242208, by rfl⟩ : syracuseStep 645889 = 484417) (by norm_num)
theorem B875269 : Blo 507795 875269 := bbase (se 4 (by rfl) ⟨82056, by rfl⟩ : syracuseStep 875269 = 164113) (by norm_num)
theorem B645985 : Blo 507795 645985 := bbase (se 2 (by rfl) ⟨242244, by rfl⟩ : syracuseStep 645985 = 484489) (by norm_num)
theorem B1858405 : Blo 507795 1858405 := bbase (se 4 (by rfl) ⟨174225, by rfl⟩ : syracuseStep 1858405 = 348451) (by norm_num)
theorem B514993 : Blo 507795 514993 := bbase (se 2 (by rfl) ⟨193122, by rfl⟩ : syracuseStep 514993 = 386245) (by norm_num)
theorem B646157 : Blo 507795 646157 := bbase (se 3 (by rfl) ⟨121154, by rfl⟩ : syracuseStep 646157 = 242309) (by norm_num)
theorem B580645 : Blo 507795 580645 := bbase (se 4 (by rfl) ⟨54435, by rfl⟩ : syracuseStep 580645 = 108871) (by norm_num)
theorem B1956917 : Blo 507795 1956917 := bbase (se 5 (by rfl) ⟨91730, by rfl⟩ : syracuseStep 1956917 = 183461) (by norm_num)
theorem B613441 : Blo 507795 613441 := bbase (se 2 (by rfl) ⟨230040, by rfl⟩ : syracuseStep 613441 = 460081) (by norm_num)
theorem B2579525 : Blo 507795 2579525 := bbase (se 4 (by rfl) ⟨241830, by rfl⟩ : syracuseStep 2579525 = 483661) (by norm_num)
theorem B646213 : Blo 507795 646213 := bbase (se 4 (by rfl) ⟨60582, by rfl⟩ : syracuseStep 646213 = 121165) (by norm_num)
theorem B613537 : Blo 507795 613537 := bbase (se 2 (by rfl) ⟨230076, by rfl⟩ : syracuseStep 613537 = 460153) (by norm_num)
theorem B646309 : Blo 507795 646309 := bbase (se 4 (by rfl) ⟨60591, by rfl⟩ : syracuseStep 646309 = 121183) (by norm_num)
theorem B6544597 : Blo 507795 6544597 := bbase (se 7 (by rfl) ⟨76694, by rfl⟩ : syracuseStep 6544597 = 153389) (by norm_num)
theorem B2907413 : Blo 507795 2907413 := bbase (se 6 (by rfl) ⟨68142, by rfl⟩ : syracuseStep 2907413 = 136285) (by norm_num)
theorem B646481 : Blo 507795 646481 := bbase (se 2 (by rfl) ⟨242430, by rfl⟩ : syracuseStep 646481 = 484861) (by norm_num)
theorem B646537 : Blo 507795 646537 := bbase (se 2 (by rfl) ⟨242451, by rfl⟩ : syracuseStep 646537 = 484903) (by norm_num)
theorem B646633 : Blo 507795 646633 := bbase (se 2 (by rfl) ⟨242487, by rfl⟩ : syracuseStep 646633 = 484975) (by norm_num)
theorem B646805 : Blo 507795 646805 := bbase (se 6 (by rfl) ⟨15159, by rfl⟩ : syracuseStep 646805 = 30319) (by norm_num)
theorem B646861 : Blo 507795 646861 := bbase (se 3 (by rfl) ⟨121286, by rfl⟩ : syracuseStep 646861 = 242573) (by norm_num)
theorem B646957 : Blo 507795 646957 := bbase (se 3 (by rfl) ⟨121304, by rfl⟩ : syracuseStep 646957 = 242609) (by norm_num)
theorem B2318213 : Blo 507795 2318213 := bbase (se 4 (by rfl) ⟨217332, by rfl⟩ : syracuseStep 2318213 = 434665) (by norm_num)
theorem B778133 : Blo 507795 778133 := bbase (se 6 (by rfl) ⟨18237, by rfl⟩ : syracuseStep 778133 = 36475) (by norm_num)
theorem B647129 : Blo 507795 647129 := bbase (se 2 (by rfl) ⟨242673, by rfl⟩ : syracuseStep 647129 = 485347) (by norm_num)
theorem B647185 : Blo 507795 647185 := bbase (se 2 (by rfl) ⟨242694, by rfl⟩ : syracuseStep 647185 = 485389) (by norm_num)
theorem B647281 : Blo 507795 647281 := bbase (se 2 (by rfl) ⟨242730, by rfl⟩ : syracuseStep 647281 = 485461) (by norm_num)
theorem B614513 : Blo 507795 614513 := bbase (se 2 (by rfl) ⟨230442, by rfl⟩ : syracuseStep 614513 = 460885) (by norm_num)
theorem B2384005 : Blo 507795 2384005 := bbase (se 4 (by rfl) ⟨223500, by rfl⟩ : syracuseStep 2384005 = 447001) (by norm_num)
theorem B647453 : Blo 507795 647453 := bbase (se 3 (by rfl) ⟨121397, by rfl⟩ : syracuseStep 647453 = 242795) (by norm_num)
theorem B2580821 : Blo 507795 2580821 := bbase (se 10 (by rfl) ⟨3780, by rfl⟩ : syracuseStep 2580821 = 7561) (by norm_num)
theorem B647509 : Blo 507795 647509 := bbase (se 10 (by rfl) ⟨948, by rfl⟩ : syracuseStep 647509 = 1897) (by norm_num)
theorem B647605 : Blo 507795 647605 := bbase (se 5 (by rfl) ⟨30356, by rfl⟩ : syracuseStep 647605 = 60713) (by norm_num)
theorem B582437 : Blo 507795 582437 := bbase (se 4 (by rfl) ⟨54603, by rfl⟩ : syracuseStep 582437 = 109207) (by norm_num)
theorem B3269429 : Blo 507795 3269429 := bbase (se 5 (by rfl) ⟨153254, by rfl⟩ : syracuseStep 3269429 = 306509) (by norm_num)
theorem B1631461 : Blo 507795 1631461 := bbase (se 4 (by rfl) ⟨152949, by rfl⟩ : syracuseStep 1631461 = 305899) (by norm_num)
theorem B1107277 : Blo 507795 1107277 := bbase (se 3 (by rfl) ⟨207614, by rfl⟩ : syracuseStep 1107277 = 415229) (by norm_num)
theorem B2909621 : Blo 507795 2909621 := bbase (se 5 (by rfl) ⟨136388, by rfl⟩ : syracuseStep 2909621 = 272777) (by norm_num)
theorem B517685 : Blo 507795 517685 := bbase (se 5 (by rfl) ⟨24266, by rfl⟩ : syracuseStep 517685 = 48533) (by norm_num)
theorem B550469 : Blo 507795 550469 := bbase (se 4 (by rfl) ⟨51606, by rfl⟩ : syracuseStep 550469 = 103213) (by norm_num)
theorem B517717 : Blo 507795 517717 := bbase (se 8 (by rfl) ⟨3033, by rfl⟩ : syracuseStep 517717 = 6067) (by norm_num)
theorem B2582117 : Blo 507795 2582117 := bbase (se 4 (by rfl) ⟨242073, by rfl⟩ : syracuseStep 2582117 = 484147) (by norm_num)
theorem B1107589 : Blo 507795 1107589 := bbase (se 4 (by rfl) ⟨103836, by rfl⟩ : syracuseStep 1107589 = 207673) (by norm_num)
theorem B550885 : Blo 507795 550885 := bbase (se 4 (by rfl) ⟨51645, by rfl⟩ : syracuseStep 550885 = 103291) (by norm_num)
theorem B1304981 : Blo 507795 1304981 := bbase (se 6 (by rfl) ⟨30585, by rfl⟩ : syracuseStep 1304981 = 61171) (by norm_num)
theorem B1305085 : Blo 507795 1305085 := bbase (se 3 (by rfl) ⟨244703, by rfl⟩ : syracuseStep 1305085 = 489407) (by norm_num)
theorem B3861269 : Blo 507795 3861269 := bbase (se 6 (by rfl) ⟨90498, by rfl⟩ : syracuseStep 3861269 = 180997) (by norm_num)
theorem B2583413 : Blo 507795 2583413 := bbase (se 5 (by rfl) ⟨121097, by rfl⟩ : syracuseStep 2583413 = 242195) (by norm_num)
theorem B1928069 : Blo 507795 1928069 := bbase (se 4 (by rfl) ⟨180756, by rfl⟩ : syracuseStep 1928069 = 361513) (by norm_num)
theorem B2747317 : Blo 507795 2747317 := bbase (se 5 (by rfl) ⟨128780, by rfl⟩ : syracuseStep 2747317 = 257561) (by norm_num)
theorem B2452517 : Blo 507795 2452517 := bbase (se 4 (by rfl) ⟨229923, by rfl⟩ : syracuseStep 2452517 = 459847) (by norm_num)
theorem B551993 : Blo 507795 551993 := bbase (se 2 (by rfl) ⟨206997, by rfl⟩ : syracuseStep 551993 = 413995) (by norm_num)
theorem B814141 : Blo 507795 814141 := bbase (se 3 (by rfl) ⟨152651, by rfl⟩ : syracuseStep 814141 = 305303) (by norm_num)
theorem B1928357 : Blo 507795 1928357 := bbase (se 4 (by rfl) ⟨180783, by rfl⟩ : syracuseStep 1928357 = 361567) (by norm_num)
theorem B1469765 : Blo 507795 1469765 := bbase (se 4 (by rfl) ⟨137790, by rfl⟩ : syracuseStep 1469765 = 275581) (by norm_num)
theorem B814789 : Blo 507795 814789 := bbase (se 4 (by rfl) ⟨76386, by rfl⟩ : syracuseStep 814789 = 152773) (by norm_num)
theorem B1142549 : Blo 507795 1142549 := bbase (se 6 (by rfl) ⟨26778, by rfl⟩ : syracuseStep 1142549 = 53557) (by norm_num)
theorem B1142621 : Blo 507795 1142621 := bbase (se 3 (by rfl) ⟨214241, by rfl⟩ : syracuseStep 1142621 = 428483) (by norm_num)
theorem B1699717 : Blo 507795 1699717 := bbase (se 4 (by rfl) ⟨159348, by rfl⟩ : syracuseStep 1699717 = 318697) (by norm_num)
theorem B1142693 : Blo 507795 1142693 := bbase (se 4 (by rfl) ⟨107127, by rfl⟩ : syracuseStep 1142693 = 214255) (by norm_num)
theorem B1830853 : Blo 507795 1830853 := bbase (se 4 (by rfl) ⟨171642, by rfl⟩ : syracuseStep 1830853 = 343285) (by norm_num)
theorem B2060245 : Blo 507795 2060245 := bbase (se 7 (by rfl) ⟨24143, by rfl⟩ : syracuseStep 2060245 = 48287) (by norm_num)
theorem B1142765 : Blo 507795 1142765 := bbase (se 3 (by rfl) ⟨214268, by rfl⟩ : syracuseStep 1142765 = 428537) (by norm_num)
theorem B2060309 : Blo 507795 2060309 := bbase (se 6 (by rfl) ⟨48288, by rfl⟩ : syracuseStep 2060309 = 96577) (by norm_num)
theorem B1142837 : Blo 507795 1142837 := bbase (se 5 (by rfl) ⟨53570, by rfl⟩ : syracuseStep 1142837 = 107141) (by norm_num)
theorem B1634357 : Blo 507795 1634357 := bbase (se 5 (by rfl) ⟨76610, by rfl⟩ : syracuseStep 1634357 = 153221) (by norm_num)
theorem B1142909 : Blo 507795 1142909 := bbase (se 3 (by rfl) ⟨214295, by rfl⟩ : syracuseStep 1142909 = 428591) (by norm_num)
theorem B2584709 : Blo 507795 2584709 := bbase (se 4 (by rfl) ⟨242316, by rfl⟩ : syracuseStep 2584709 = 484633) (by norm_num)
theorem B1142981 : Blo 507795 1142981 := bbase (se 4 (by rfl) ⟨107154, by rfl⟩ : syracuseStep 1142981 = 214309) (by norm_num)
theorem B1143053 : Blo 507795 1143053 := bbase (se 3 (by rfl) ⟨214322, by rfl⟩ : syracuseStep 1143053 = 428645) (by norm_num)
theorem B1929541 : Blo 507795 1929541 := bbase (se 4 (by rfl) ⟨180894, by rfl⟩ : syracuseStep 1929541 = 361789) (by norm_num)
theorem B5566805 : Blo 507795 5566805 := bbase (se 10 (by rfl) ⟨8154, by rfl⟩ : syracuseStep 5566805 = 16309) (by norm_num)
theorem B1143125 : Blo 507795 1143125 := bbase (se 10 (by rfl) ⟨1674, by rfl⟩ : syracuseStep 1143125 = 3349) (by norm_num)
theorem B1143197 : Blo 507795 1143197 := bbase (se 3 (by rfl) ⟨214349, by rfl⟩ : syracuseStep 1143197 = 428699) (by norm_num)
theorem B1143269 : Blo 507795 1143269 := bbase (se 4 (by rfl) ⟨107181, by rfl⟩ : syracuseStep 1143269 = 214363) (by norm_num)
theorem B1143341 : Blo 507795 1143341 := bbase (se 3 (by rfl) ⟨214376, by rfl⟩ : syracuseStep 1143341 = 428753) (by norm_num)
theorem B815717 : Blo 507795 815717 := bbase (se 4 (by rfl) ⟨76473, by rfl⟩ : syracuseStep 815717 = 152947) (by norm_num)
theorem B1143413 : Blo 507795 1143413 := bbase (se 5 (by rfl) ⟨53597, by rfl⟩ : syracuseStep 1143413 = 107195) (by norm_num)
theorem B1929845 : Blo 507795 1929845 := bbase (se 5 (by rfl) ⟨90461, by rfl⟩ : syracuseStep 1929845 = 180923) (by norm_num)
theorem B1143485 : Blo 507795 1143485 := bbase (se 3 (by rfl) ⟨214403, by rfl⟩ : syracuseStep 1143485 = 428807) (by norm_num)
theorem B1143557 : Blo 507795 1143557 := bbase (se 4 (by rfl) ⟨107208, by rfl⟩ : syracuseStep 1143557 = 214417) (by norm_num)
theorem B1143629 : Blo 507795 1143629 := bbase (se 3 (by rfl) ⟨214430, by rfl⟩ : syracuseStep 1143629 = 428861) (by norm_num)
theorem B1143701 : Blo 507795 1143701 := bbase (se 6 (by rfl) ⟨26805, by rfl⟩ : syracuseStep 1143701 = 53611) (by norm_num)
theorem B4125653 : Blo 507795 4125653 := bbase (se 7 (by rfl) ⟨48347, by rfl⟩ : syracuseStep 4125653 = 96695) (by norm_num)
theorem B1143773 : Blo 507795 1143773 := bbase (se 3 (by rfl) ⟨214457, by rfl⟩ : syracuseStep 1143773 = 428915) (by norm_num)
theorem B553969 : Blo 507795 553969 := bbase (se 2 (by rfl) ⟨207738, by rfl⟩ : syracuseStep 553969 = 415477) (by norm_num)
theorem B3109877 : Blo 507795 3109877 := bbase (se 5 (by rfl) ⟨145775, by rfl⟩ : syracuseStep 3109877 = 291551) (by norm_num)
theorem B2454533 : Blo 507795 2454533 := bbase (se 4 (by rfl) ⟨230112, by rfl⟩ : syracuseStep 2454533 = 460225) (by norm_num)
theorem B1143845 : Blo 507795 1143845 := bbase (se 4 (by rfl) ⟨107235, by rfl⟩ : syracuseStep 1143845 = 214471) (by norm_num)
theorem B816173 : Blo 507795 816173 := bbase (se 3 (by rfl) ⟨153032, by rfl⟩ : syracuseStep 816173 = 306065) (by norm_num)
theorem B1373237 : Blo 507795 1373237 := bbase (se 5 (by rfl) ⟨64370, by rfl⟩ : syracuseStep 1373237 = 128741) (by norm_num)
theorem B1143917 : Blo 507795 1143917 := bbase (se 3 (by rfl) ⟨214484, by rfl⟩ : syracuseStep 1143917 = 428969) (by norm_num)
theorem B1143989 : Blo 507795 1143989 := bbase (se 5 (by rfl) ⟨53624, by rfl⟩ : syracuseStep 1143989 = 107249) (by norm_num)
theorem B2454725 : Blo 507795 2454725 := bbase (se 4 (by rfl) ⟨230130, by rfl⟩ : syracuseStep 2454725 = 460261) (by norm_num)
theorem B1471733 : Blo 507795 1471733 := bbase (se 5 (by rfl) ⟨68987, by rfl⟩ : syracuseStep 1471733 = 137975) (by norm_num)
theorem B1144061 : Blo 507795 1144061 := bbase (se 3 (by rfl) ⟨214511, by rfl⟩ : syracuseStep 1144061 = 429023) (by norm_num)
theorem B1144133 : Blo 507795 1144133 := bbase (se 4 (by rfl) ⟨107262, by rfl⟩ : syracuseStep 1144133 = 214525) (by norm_num)
theorem B1373573 : Blo 507795 1373573 := bbase (se 4 (by rfl) ⟨128772, by rfl⟩ : syracuseStep 1373573 = 257545) (by norm_num)
theorem B1144205 : Blo 507795 1144205 := bbase (se 3 (by rfl) ⟨214538, by rfl⟩ : syracuseStep 1144205 = 429077) (by norm_num)
theorem B2586005 : Blo 507795 2586005 := bbase (se 6 (by rfl) ⟨60609, by rfl⟩ : syracuseStep 2586005 = 121219) (by norm_num)
theorem B1144277 : Blo 507795 1144277 := bbase (se 7 (by rfl) ⟨13409, by rfl⟩ : syracuseStep 1144277 = 26819) (by norm_num)
theorem B1144349 : Blo 507795 1144349 := bbase (se 3 (by rfl) ⟨214565, by rfl⟩ : syracuseStep 1144349 = 429131) (by norm_num)
theorem B1144421 : Blo 507795 1144421 := bbase (se 4 (by rfl) ⟨107289, by rfl⟩ : syracuseStep 1144421 = 214579) (by norm_num)
theorem B882301 : Blo 507795 882301 := bbase (se 3 (by rfl) ⟨165431, by rfl⟩ : syracuseStep 882301 = 330863) (by norm_num)
theorem B1144493 : Blo 507795 1144493 := bbase (se 3 (by rfl) ⟨214592, by rfl⟩ : syracuseStep 1144493 = 429185) (by norm_num)
theorem B6190805 : Blo 507795 6190805 := bbase (se 7 (by rfl) ⟨72548, by rfl⟩ : syracuseStep 6190805 = 145097) (by norm_num)
theorem B1144565 : Blo 507795 1144565 := bbase (se 5 (by rfl) ⟨53651, by rfl⟩ : syracuseStep 1144565 = 107303) (by norm_num)
theorem B1144637 : Blo 507795 1144637 := bbase (se 3 (by rfl) ⟨214619, by rfl⟩ : syracuseStep 1144637 = 429239) (by norm_num)
theorem B4355957 : Blo 507795 4355957 := bbase (se 5 (by rfl) ⟨204185, by rfl⟩ : syracuseStep 4355957 = 408371) (by norm_num)
theorem B1144709 : Blo 507795 1144709 := bbase (se 4 (by rfl) ⟨107316, by rfl⟩ : syracuseStep 1144709 = 214633) (by norm_num)
theorem B1046405 : Blo 507795 1046405 := bbase (se 4 (by rfl) ⟨98100, by rfl⟩ : syracuseStep 1046405 = 196201) (by norm_num)
theorem B1374101 : Blo 507795 1374101 := bbase (se 6 (by rfl) ⟨32205, by rfl⟩ : syracuseStep 1374101 = 64411) (by norm_num)
theorem B1144781 : Blo 507795 1144781 := bbase (se 3 (by rfl) ⟨214646, by rfl⟩ : syracuseStep 1144781 = 429293) (by norm_num)
theorem B1144853 : Blo 507795 1144853 := bbase (se 6 (by rfl) ⟨26832, by rfl⟩ : syracuseStep 1144853 = 53665) (by norm_num)
theorem B981029 : Blo 507795 981029 := bbase (se 4 (by rfl) ⟨91971, by rfl⟩ : syracuseStep 981029 = 183943) (by norm_num)
theorem B1144925 : Blo 507795 1144925 := bbase (se 3 (by rfl) ⟨214673, by rfl⟩ : syracuseStep 1144925 = 429347) (by norm_num)
theorem B1144997 : Blo 507795 1144997 := bbase (se 4 (by rfl) ⟨107343, by rfl⟩ : syracuseStep 1144997 = 214687) (by norm_num)
theorem B1964245 : Blo 507795 1964245 := bbase (se 7 (by rfl) ⟨23018, by rfl⟩ : syracuseStep 1964245 = 46037) (by norm_num)
theorem B1145069 : Blo 507795 1145069 := bbase (se 3 (by rfl) ⟨214700, by rfl⟩ : syracuseStep 1145069 = 429401) (by norm_num)
theorem B6715669 : Blo 507795 6715669 := bbase (se 6 (by rfl) ⟨157398, by rfl⟩ : syracuseStep 6715669 = 314797) (by norm_num)
theorem B1145141 : Blo 507795 1145141 := bbase (se 5 (by rfl) ⟨53678, by rfl⟩ : syracuseStep 1145141 = 107357) (by norm_num)
theorem B1145213 : Blo 507795 1145213 := bbase (se 3 (by rfl) ⟨214727, by rfl⟩ : syracuseStep 1145213 = 429455) (by norm_num)
theorem B817589 : Blo 507795 817589 := bbase (se 5 (by rfl) ⟨38324, by rfl⟩ : syracuseStep 817589 = 76649) (by norm_num)
theorem B1145285 : Blo 507795 1145285 := bbase (se 4 (by rfl) ⟨107370, by rfl⟩ : syracuseStep 1145285 = 214741) (by norm_num)
theorem B981445 : Blo 507795 981445 := bbase (se 4 (by rfl) ⟨92010, by rfl⟩ : syracuseStep 981445 = 184021) (by norm_num)
theorem B1145357 : Blo 507795 1145357 := bbase (se 3 (by rfl) ⟨214754, by rfl⟩ : syracuseStep 1145357 = 429509) (by norm_num)
theorem B1145429 : Blo 507795 1145429 := bbase (se 8 (by rfl) ⟨6711, by rfl⟩ : syracuseStep 1145429 = 13423) (by norm_num)
theorem B817813 : Blo 507795 817813 := bbase (se 6 (by rfl) ⟨19167, by rfl⟩ : syracuseStep 817813 = 38335) (by norm_num)
theorem B1145501 : Blo 507795 1145501 := bbase (se 3 (by rfl) ⟨214781, by rfl⟩ : syracuseStep 1145501 = 429563) (by norm_num)
theorem B2587301 : Blo 507795 2587301 := bbase (se 4 (by rfl) ⟨242559, by rfl⟩ : syracuseStep 2587301 = 485119) (by norm_num)
theorem B1931957 : Blo 507795 1931957 := bbase (se 5 (by rfl) ⟨90560, by rfl⟩ : syracuseStep 1931957 = 181121) (by norm_num)
theorem B1145573 : Blo 507795 1145573 := bbase (se 4 (by rfl) ⟨107397, by rfl⟩ : syracuseStep 1145573 = 214795) (by norm_num)
theorem B1833749 : Blo 507795 1833749 := bbase (se 6 (by rfl) ⟨42978, by rfl⟩ : syracuseStep 1833749 = 85957) (by norm_num)
theorem B1178389 : Blo 507795 1178389 := bbase (se 6 (by rfl) ⟨27618, by rfl⟩ : syracuseStep 1178389 = 55237) (by norm_num)
theorem B1145645 : Blo 507795 1145645 := bbase (se 3 (by rfl) ⟨214808, by rfl⟩ : syracuseStep 1145645 = 429617) (by norm_num)
theorem B1145717 : Blo 507795 1145717 := bbase (se 5 (by rfl) ⟨53705, by rfl⟩ : syracuseStep 1145717 = 107411) (by norm_num)
theorem B8682389 : Blo 507795 8682389 := bbase (se 6 (by rfl) ⟨203493, by rfl⟩ : syracuseStep 8682389 = 406987) (by norm_num)
theorem B1473461 : Blo 507795 1473461 := bbase (se 5 (by rfl) ⟨69068, by rfl⟩ : syracuseStep 1473461 = 138137) (by norm_num)
theorem B1145789 : Blo 507795 1145789 := bbase (se 3 (by rfl) ⟨214835, by rfl⟩ : syracuseStep 1145789 = 429671) (by norm_num)
theorem B1932245 : Blo 507795 1932245 := bbase (se 7 (by rfl) ⟨22643, by rfl⟩ : syracuseStep 1932245 = 45287) (by norm_num)
theorem B7076821 : Blo 507795 7076821 := bbase (se 7 (by rfl) ⟨82931, by rfl⟩ : syracuseStep 7076821 = 165863) (by norm_num)
theorem B1309661 : Blo 507795 1309661 := bbase (se 3 (by rfl) ⟨245561, by rfl⟩ : syracuseStep 1309661 = 491123) (by norm_num)
theorem B1145861 : Blo 507795 1145861 := bbase (se 4 (by rfl) ⟨107424, by rfl⟩ : syracuseStep 1145861 = 214849) (by norm_num)
theorem B851005 : Blo 507795 851005 := bbase (se 3 (by rfl) ⟨159563, by rfl⟩ : syracuseStep 851005 = 319127) (by norm_num)
theorem B1145933 : Blo 507795 1145933 := bbase (se 3 (by rfl) ⟨214862, by rfl⟩ : syracuseStep 1145933 = 429725) (by norm_num)
theorem B1637509 : Blo 507795 1637509 := bbase (se 4 (by rfl) ⟨153516, by rfl⟩ : syracuseStep 1637509 = 307033) (by norm_num)
theorem B1146005 : Blo 507795 1146005 := bbase (se 6 (by rfl) ⟨26859, by rfl⟩ : syracuseStep 1146005 = 53719) (by norm_num)
theorem B1146077 : Blo 507795 1146077 := bbase (se 3 (by rfl) ⟨214889, by rfl⟩ : syracuseStep 1146077 = 429779) (by norm_num)
theorem B2456821 : Blo 507795 2456821 := bbase (se 5 (by rfl) ⟨115163, by rfl⟩ : syracuseStep 2456821 = 230327) (by norm_num)
theorem B982277 : Blo 507795 982277 := bbase (se 4 (by rfl) ⟨92088, by rfl⟩ : syracuseStep 982277 = 184177) (by norm_num)
theorem B1146149 : Blo 507795 1146149 := bbase (se 4 (by rfl) ⟨107451, by rfl⟩ : syracuseStep 1146149 = 214903) (by norm_num)
theorem B1146221 : Blo 507795 1146221 := bbase (se 3 (by rfl) ⟨214916, by rfl⟩ : syracuseStep 1146221 = 429833) (by norm_num)
theorem B1146293 : Blo 507795 1146293 := bbase (se 5 (by rfl) ⟨53732, by rfl⟩ : syracuseStep 1146293 = 107465) (by norm_num)
theorem B916933 : Blo 507795 916933 := bbase (se 4 (by rfl) ⟨85962, by rfl⟩ : syracuseStep 916933 = 171925) (by norm_num)
theorem B4128245 : Blo 507795 4128245 := bbase (se 5 (by rfl) ⟨193511, by rfl⟩ : syracuseStep 4128245 = 387023) (by norm_num)
theorem B1146365 : Blo 507795 1146365 := bbase (se 3 (by rfl) ⟨214943, by rfl⟩ : syracuseStep 1146365 = 429887) (by norm_num)
theorem B1146437 : Blo 507795 1146437 := bbase (se 4 (by rfl) ⟨107478, by rfl⟩ : syracuseStep 1146437 = 214957) (by norm_num)
theorem B917077 : Blo 507795 917077 := bbase (se 8 (by rfl) ⟨5373, by rfl⟩ : syracuseStep 917077 = 10747) (by norm_num)
theorem B1146509 : Blo 507795 1146509 := bbase (se 3 (by rfl) ⟨214970, by rfl⟩ : syracuseStep 1146509 = 429941) (by norm_num)
theorem B2752181 : Blo 507795 2752181 := bbase (se 5 (by rfl) ⟨129008, by rfl⟩ : syracuseStep 2752181 = 258017) (by norm_num)
theorem B1146581 : Blo 507795 1146581 := bbase (se 7 (by rfl) ⟨13436, by rfl⟩ : syracuseStep 1146581 = 26873) (by norm_num)
theorem B917237 : Blo 507795 917237 := bbase (se 5 (by rfl) ⟨42995, by rfl⟩ : syracuseStep 917237 = 85991) (by norm_num)
theorem B1146653 : Blo 507795 1146653 := bbase (se 3 (by rfl) ⟨214997, by rfl⟩ : syracuseStep 1146653 = 429995) (by norm_num)
theorem B917293 : Blo 507795 917293 := bbase (se 3 (by rfl) ⟨171992, by rfl⟩ : syracuseStep 917293 = 343985) (by norm_num)
theorem B655169 : Blo 507795 655169 := bbase (se 2 (by rfl) ⟨245688, by rfl⟩ : syracuseStep 655169 = 491377) (by norm_num)
theorem B1146725 : Blo 507795 1146725 := bbase (se 4 (by rfl) ⟨107505, by rfl⟩ : syracuseStep 1146725 = 215011) (by norm_num)
theorem B1146797 : Blo 507795 1146797 := bbase (se 3 (by rfl) ⟨215024, by rfl⟩ : syracuseStep 1146797 = 430049) (by norm_num)
theorem B2588597 : Blo 507795 2588597 := bbase (se 5 (by rfl) ⟨121340, by rfl⟩ : syracuseStep 2588597 = 242681) (by norm_num)
theorem B1146869 : Blo 507795 1146869 := bbase (se 5 (by rfl) ⟨53759, by rfl⟩ : syracuseStep 1146869 = 107519) (by norm_num)
theorem B1310833 : Blo 507795 1310833 := bstep (se 2 (by rfl) ⟨491562, by rfl⟩ : syracuseStep 1310833 = 983125) B983125
theorem B3178673 : Blo 507795 3178673 := bstep (se 2 (by rfl) ⟨1192002, by rfl⟩ : syracuseStep 3178673 = 2384005) B2384005
theorem B6193379 : Blo 507795 6193379 := bstep (se 1 (by rfl) ⟨4645034, by rfl⟩ : syracuseStep 6193379 = 9290069) B9290069
theorem B1147121 : Blo 507795 1147121 := bstep (se 2 (by rfl) ⟨430170, by rfl⟩ : syracuseStep 1147121 = 860341) B860341
theorem B1147139 : Blo 507795 1147139 := bstep (se 1 (by rfl) ⟨860354, by rfl⟩ : syracuseStep 1147139 = 1720709) B1720709
theorem B1638701 : Blo 507795 1638701 := bstep (se 3 (by rfl) ⟨307256, by rfl⟩ : syracuseStep 1638701 = 614513) B614513
theorem B1147409 : Blo 507795 1147409 := bstep (se 2 (by rfl) ⟨430278, by rfl⟩ : syracuseStep 1147409 = 860557) B860557
theorem B1147427 : Blo 507795 1147427 := bstep (se 1 (by rfl) ⟨860570, by rfl⟩ : syracuseStep 1147427 = 1721141) B1721141
theorem B2458147 : Blo 507795 2458147 := bstep (se 1 (by rfl) ⟨1843610, by rfl⟩ : syracuseStep 2458147 = 3687221) B3687221
theorem B655939 : Blo 507795 655939 := bstep (se 1 (by rfl) ⟨491954, by rfl⟩ : syracuseStep 655939 = 983909) B983909
theorem B1933901 : Blo 507795 1933901 := bstep (se 3 (by rfl) ⟨362606, by rfl⟩ : syracuseStep 1933901 = 725213) B725213
theorem B7078499 : Blo 507795 7078499 := bstep (se 1 (by rfl) ⟨5308874, by rfl⟩ : syracuseStep 7078499 = 10617749) B10617749
theorem B688835 : Blo 507795 688835 := bstep (se 1 (by rfl) ⟨516626, by rfl⟩ : syracuseStep 688835 = 1033253) B1033253
theorem B1147697 : Blo 507795 1147697 := bstep (se 2 (by rfl) ⟨430386, by rfl⟩ : syracuseStep 1147697 = 860773) B860773
theorem B2622257 : Blo 507795 2622257 := bstep (se 2 (by rfl) ⟨983346, by rfl⟩ : syracuseStep 2622257 = 1966693) B1966693
theorem B1147715 : Blo 507795 1147715 := bstep (se 1 (by rfl) ⟨860786, by rfl⟩ : syracuseStep 1147715 = 1721573) B1721573
theorem B19104709 : Blo 507795 19104709 := bstep (se 4 (by rfl) ⟨1791066, by rfl⟩ : syracuseStep 19104709 = 3582133) B3582133
theorem B2589731 : Blo 507795 2589731 := bstep (se 1 (by rfl) ⟨1942298, by rfl⟩ : syracuseStep 2589731 = 3884597) B3884597
theorem B1147985 : Blo 507795 1147985 := bstep (se 2 (by rfl) ⟨430494, by rfl⟩ : syracuseStep 1147985 = 860989) B860989
theorem B1148003 : Blo 507795 1148003 := bstep (se 1 (by rfl) ⟨861002, by rfl⟩ : syracuseStep 1148003 = 1722005) B1722005
theorem B590995 : Blo 507795 590995 := bstep (se 1 (by rfl) ⟨443246, by rfl⟩ : syracuseStep 590995 = 886493) B886493
theorem B885937 : Blo 507795 885937 := bstep (se 2 (by rfl) ⟨332226, by rfl⟩ : syracuseStep 885937 = 664453) B664453
theorem B1934705 : Blo 507795 1934705 := bstep (se 2 (by rfl) ⟨725514, by rfl⟩ : syracuseStep 1934705 = 1451029) B1451029
theorem B1148273 : Blo 507795 1148273 := bstep (se 2 (by rfl) ⟨430602, by rfl⟩ : syracuseStep 1148273 = 861205) B861205
theorem B1148291 : Blo 507795 1148291 := bstep (se 1 (by rfl) ⟨861218, by rfl⟩ : syracuseStep 1148291 = 1722437) B1722437
theorem B2754083 : Blo 507795 2754083 := bstep (se 1 (by rfl) ⟨2065562, by rfl⟩ : syracuseStep 2754083 = 4131125) B4131125
theorem B13108877 : Blo 507795 13108877 := bstep (se 3 (by rfl) ⟨2457914, by rfl⟩ : syracuseStep 13108877 = 4915829) B4915829
theorem B1148561 : Blo 507795 1148561 := bstep (se 2 (by rfl) ⟨430710, by rfl⟩ : syracuseStep 1148561 = 861421) B861421
theorem B1148579 : Blo 507795 1148579 := bstep (se 1 (by rfl) ⟨861434, by rfl⟩ : syracuseStep 1148579 = 1722869) B1722869
theorem B2590541 : Blo 507795 2590541 := bstep (se 3 (by rfl) ⟨485726, by rfl⟩ : syracuseStep 2590541 = 971453) B971453
theorem B1148849 : Blo 507795 1148849 := bstep (se 2 (by rfl) ⟨430818, by rfl⟩ : syracuseStep 1148849 = 861637) B861637
theorem B1148867 : Blo 507795 1148867 := bstep (se 1 (by rfl) ⟨861650, by rfl⟩ : syracuseStep 1148867 = 1723301) B1723301
theorem B1935373 : Blo 507795 1935373 := bstep (se 3 (by rfl) ⟨362882, by rfl⟩ : syracuseStep 1935373 = 725765) B725765
theorem B723043 : Blo 507795 723043 := bstep (se 1 (by rfl) ⟨542282, by rfl⟩ : syracuseStep 723043 = 1084565) B1084565
theorem B690289 : Blo 507795 690289 := bstep (se 2 (by rfl) ⟨258858, by rfl⟩ : syracuseStep 690289 = 517717) B517717
theorem B1476785 : Blo 507795 1476785 := bstep (se 2 (by rfl) ⟨553794, by rfl⟩ : syracuseStep 1476785 = 1107589) B1107589
theorem B1149137 : Blo 507795 1149137 := bstep (se 2 (by rfl) ⟨430926, by rfl⟩ : syracuseStep 1149137 = 861853) B861853
theorem B1149155 : Blo 507795 1149155 := bstep (se 1 (by rfl) ⟨861866, by rfl⟩ : syracuseStep 1149155 = 1723733) B1723733
theorem B1149425 : Blo 507795 1149425 := bstep (se 2 (by rfl) ⟨431034, by rfl⟩ : syracuseStep 1149425 = 862069) B862069
theorem B1149443 : Blo 507795 1149443 := bstep (se 1 (by rfl) ⟨862082, by rfl⟩ : syracuseStep 1149443 = 1724165) B1724165
theorem B920177 : Blo 507795 920177 := bstep (se 2 (by rfl) ⟨345066, by rfl⟩ : syracuseStep 920177 = 690133) B690133
theorem B723601 : Blo 507795 723601 := bstep (se 2 (by rfl) ⟨271350, by rfl⟩ : syracuseStep 723601 = 542701) B542701
theorem B1149713 : Blo 507795 1149713 := bstep (se 2 (by rfl) ⟨431142, by rfl⟩ : syracuseStep 1149713 = 862285) B862285
theorem B1149731 : Blo 507795 1149731 := bstep (se 1 (by rfl) ⟨862298, by rfl⟩ : syracuseStep 1149731 = 1724597) B1724597
theorem B1936163 : Blo 507795 1936163 := bstep (se 1 (by rfl) ⟨1452122, by rfl⟩ : syracuseStep 1936163 = 2904245) B2904245
theorem B1150001 : Blo 507795 1150001 := bstep (se 2 (by rfl) ⟨431250, by rfl⟩ : syracuseStep 1150001 = 862501) B862501
theorem B1150019 : Blo 507795 1150019 := bstep (se 1 (by rfl) ⟨862514, by rfl⟩ : syracuseStep 1150019 = 1725029) B1725029
theorem B1084547 : Blo 507795 1084547 := bstep (se 1 (by rfl) ⟨813410, by rfl⟩ : syracuseStep 1084547 = 1626821) B1626821
theorem B1740113 : Blo 507795 1740113 := bstep (se 2 (by rfl) ⟨652542, by rfl⟩ : syracuseStep 1740113 = 1305085) B1305085
theorem B1150289 : Blo 507795 1150289 := bstep (se 2 (by rfl) ⟨431358, by rfl⟩ : syracuseStep 1150289 = 862717) B862717
theorem B724307 : Blo 507795 724307 := bstep (se 1 (by rfl) ⟨543230, by rfl⟩ : syracuseStep 724307 = 1086461) B1086461
theorem B1150307 : Blo 507795 1150307 := bstep (se 1 (by rfl) ⟨862730, by rfl⟩ : syracuseStep 1150307 = 1725461) B1725461
theorem B920963 : Blo 507795 920963 := bstep (se 1 (by rfl) ⟨690722, by rfl⟩ : syracuseStep 920963 = 1381445) B1381445
theorem B1379747 : Blo 507795 1379747 := bstep (se 1 (by rfl) ⟨1034810, by rfl⟩ : syracuseStep 1379747 = 2069621) B2069621
theorem B1936817 : Blo 507795 1936817 := bstep (se 2 (by rfl) ⟨726306, by rfl⟩ : syracuseStep 1936817 = 1452613) B1452613
theorem B3673613 : Blo 507795 3673613 := bstep (se 3 (by rfl) ⟨688802, by rfl⟩ : syracuseStep 3673613 = 1377605) B1377605
theorem B1150577 : Blo 507795 1150577 := bstep (se 2 (by rfl) ⟨431466, by rfl⟩ : syracuseStep 1150577 = 862933) B862933
theorem B1150595 : Blo 507795 1150595 := bstep (se 1 (by rfl) ⟨862946, by rfl⟩ : syracuseStep 1150595 = 1725893) B1725893
theorem B921251 : Blo 507795 921251 := bstep (se 1 (by rfl) ⟨690938, by rfl⟩ : syracuseStep 921251 = 1381877) B1381877
theorem B3673955 : Blo 507795 3673955 := bstep (se 1 (by rfl) ⟨2755466, by rfl⟩ : syracuseStep 3673955 = 5510933) B5510933
theorem B1150865 : Blo 507795 1150865 := bstep (se 2 (by rfl) ⟨431574, by rfl⟩ : syracuseStep 1150865 = 863149) B863149
theorem B1150883 : Blo 507795 1150883 := bstep (se 1 (by rfl) ⟨863162, by rfl⟩ : syracuseStep 1150883 = 1726325) B1726325
theorem B724945 : Blo 507795 724945 := bstep (se 2 (by rfl) ⟨271854, by rfl⟩ : syracuseStep 724945 = 543709) B543709
theorem B8851427 : Blo 507795 8851427 := bstep (se 1 (by rfl) ⟨6638570, by rfl⟩ : syracuseStep 8851427 = 13277141) B13277141
theorem B725059 : Blo 507795 725059 := bstep (se 1 (by rfl) ⟨543794, by rfl⟩ : syracuseStep 725059 = 1087589) B1087589
theorem B1380493 : Blo 507795 1380493 := bstep (se 3 (by rfl) ⟨258842, by rfl⟩ : syracuseStep 1380493 = 517685) B517685
theorem B2330765 : Blo 507795 2330765 := bstep (se 3 (by rfl) ⟨437018, by rfl⟩ : syracuseStep 2330765 = 874037) B874037
theorem B1151153 : Blo 507795 1151153 := bstep (se 2 (by rfl) ⟨431682, by rfl⟩ : syracuseStep 1151153 = 863365) B863365
theorem B1151171 : Blo 507795 1151171 := bstep (se 1 (by rfl) ⟨863378, by rfl⟩ : syracuseStep 1151171 = 1726757) B1726757
theorem B3870989 : Blo 507795 3870989 := bstep (se 3 (by rfl) ⟨725810, by rfl⟩ : syracuseStep 3870989 = 1451621) B1451621
theorem B1085795 : Blo 507795 1085795 := bstep (se 1 (by rfl) ⟨814346, by rfl⟩ : syracuseStep 1085795 = 1628693) B1628693
theorem B1151441 : Blo 507795 1151441 := bstep (se 2 (by rfl) ⟨431790, by rfl⟩ : syracuseStep 1151441 = 863581) B863581
theorem B1151459 : Blo 507795 1151459 := bstep (se 1 (by rfl) ⟨863594, by rfl⟩ : syracuseStep 1151459 = 1727189) B1727189
theorem B1938275 : Blo 507795 1938275 := bstep (se 1 (by rfl) ⟨1453706, by rfl⟩ : syracuseStep 1938275 = 2907413) B2907413
theorem B1938289 : Blo 507795 1938289 := bstep (se 2 (by rfl) ⟨726858, by rfl⟩ : syracuseStep 1938289 = 1453717) B1453717
theorem B856993 : Blo 507795 856993 := bstep (se 2 (by rfl) ⟨321372, by rfl⟩ : syracuseStep 856993 = 642745) B642745
theorem B1086385 : Blo 507795 1086385 := bstep (se 2 (by rfl) ⟨407394, by rfl⟩ : syracuseStep 1086385 = 814789) B814789
theorem B857027 : Blo 507795 857027 := bstep (se 1 (by rfl) ⟨642770, by rfl⟩ : syracuseStep 857027 = 1285541) B1285541
theorem B2790413 : Blo 507795 2790413 := bstep (se 3 (by rfl) ⟨523202, by rfl⟩ : syracuseStep 2790413 = 1046405) B1046405
theorem B1446929 : Blo 507795 1446929 := bstep (se 2 (by rfl) ⟨542598, by rfl⟩ : syracuseStep 1446929 = 1085197) B1085197
theorem B857155 : Blo 507795 857155 := bstep (se 1 (by rfl) ⟨642866, by rfl⟩ : syracuseStep 857155 = 1285733) B1285733
theorem B2266289 : Blo 507795 2266289 := bstep (se 2 (by rfl) ⟨849858, by rfl⟩ : syracuseStep 2266289 = 1699717) B1699717
theorem B857297 : Blo 507795 857297 := bstep (se 2 (by rfl) ⟨321486, by rfl⟩ : syracuseStep 857297 = 642973) B642973
theorem B3151075 : Blo 507795 3151075 := bstep (se 1 (by rfl) ⟨2363306, by rfl⟩ : syracuseStep 3151075 = 4726613) B4726613
theorem B1545475 : Blo 507795 1545475 := bstep (se 1 (by rfl) ⟨1159106, by rfl⟩ : syracuseStep 1545475 = 2318213) B2318213
theorem B2954501 : Blo 507795 2954501 := bstep (se 4 (by rfl) ⟨276984, by rfl⟩ : syracuseStep 2954501 = 553969) B553969
theorem B857425 : Blo 507795 857425 := bstep (se 2 (by rfl) ⟨321534, by rfl⟩ : syracuseStep 857425 = 643069) B643069
theorem B857459 : Blo 507795 857459 := bstep (se 1 (by rfl) ⟨643094, by rfl⟩ : syracuseStep 857459 = 1286189) B1286189
theorem B726403 : Blo 507795 726403 := bstep (se 1 (by rfl) ⟨544802, by rfl⟩ : syracuseStep 726403 = 1089605) B1089605
theorem B857587 : Blo 507795 857587 := bstep (se 1 (by rfl) ⟨643190, by rfl⟩ : syracuseStep 857587 = 1286381) B1286381
theorem B857729 : Blo 507795 857729 := bstep (se 2 (by rfl) ⟨321648, by rfl⟩ : syracuseStep 857729 = 643297) B643297
theorem B3479267 : Blo 507795 3479267 := bstep (se 1 (by rfl) ⟨2609450, by rfl⟩ : syracuseStep 3479267 = 5218901) B5218901
theorem B857857 : Blo 507795 857857 := bstep (se 2 (by rfl) ⟨321696, by rfl⟩ : syracuseStep 857857 = 643393) B643393
theorem B857891 : Blo 507795 857891 := bstep (se 1 (by rfl) ⟨643418, by rfl⟩ : syracuseStep 857891 = 1286837) B1286837
theorem B1840931 : Blo 507795 1840931 := bstep (se 1 (by rfl) ⟨1380698, by rfl⟩ : syracuseStep 1840931 = 2761397) B2761397
theorem B858019 : Blo 507795 858019 := bstep (se 1 (by rfl) ⟨643514, by rfl⟩ : syracuseStep 858019 = 1287029) B1287029
theorem B1447885 : Blo 507795 1447885 := bstep (se 3 (by rfl) ⟨271478, by rfl⟩ : syracuseStep 1447885 = 542957) B542957
theorem B2758627 : Blo 507795 2758627 := bstep (se 1 (by rfl) ⟨2068970, by rfl⟩ : syracuseStep 2758627 = 4137941) B4137941
theorem B858161 : Blo 507795 858161 := bstep (se 2 (by rfl) ⟨321810, by rfl⟩ : syracuseStep 858161 = 643621) B643621
theorem B1448113 : Blo 507795 1448113 := bstep (se 2 (by rfl) ⟨543042, by rfl⟩ : syracuseStep 1448113 = 1086085) B1086085
theorem B858289 : Blo 507795 858289 := bstep (se 2 (by rfl) ⟨321858, by rfl⟩ : syracuseStep 858289 = 643717) B643717
theorem B858323 : Blo 507795 858323 := bstep (se 1 (by rfl) ⟨643742, by rfl⟩ : syracuseStep 858323 = 1287485) B1287485
theorem B1939747 : Blo 507795 1939747 := bstep (se 1 (by rfl) ⟨1454810, by rfl⟩ : syracuseStep 1939747 = 2909621) B2909621
theorem B1448273 : Blo 507795 1448273 := bstep (se 2 (by rfl) ⟨543102, by rfl⟩ : syracuseStep 1448273 = 1086205) B1086205
theorem B858451 : Blo 507795 858451 := bstep (se 1 (by rfl) ⟨643838, by rfl⟩ : syracuseStep 858451 = 1287677) B1287677
theorem B1448387 : Blo 507795 1448387 := bstep (se 1 (by rfl) ⟨1086290, by rfl⟩ : syracuseStep 1448387 = 2172581) B2172581
theorem B858593 : Blo 507795 858593 := bstep (se 2 (by rfl) ⟨321972, by rfl⟩ : syracuseStep 858593 = 643945) B643945
theorem B727537 : Blo 507795 727537 := bstep (se 2 (by rfl) ⟨272826, by rfl⟩ : syracuseStep 727537 = 545653) B545653
theorem B727633 : Blo 507795 727633 := bstep (se 2 (by rfl) ⟨272862, by rfl⟩ : syracuseStep 727633 = 545725) B545725
theorem B858721 : Blo 507795 858721 := bstep (se 2 (by rfl) ⟨322020, by rfl⟩ : syracuseStep 858721 = 644041) B644041
theorem B1383011 : Blo 507795 1383011 := bstep (se 1 (by rfl) ⟨1037258, by rfl⟩ : syracuseStep 1383011 = 2074517) B2074517
theorem B858755 : Blo 507795 858755 := bstep (se 1 (by rfl) ⟨644066, by rfl⟩ : syracuseStep 858755 = 1288133) B1288133
theorem B858883 : Blo 507795 858883 := bstep (se 1 (by rfl) ⟨644162, by rfl⟩ : syracuseStep 858883 = 1288325) B1288325
theorem B859025 : Blo 507795 859025 := bstep (se 2 (by rfl) ⟨322134, by rfl⟩ : syracuseStep 859025 = 644269) B644269
theorem B859153 : Blo 507795 859153 := bstep (se 2 (by rfl) ⟨322182, by rfl⟩ : syracuseStep 859153 = 644365) B644365
theorem B859187 : Blo 507795 859187 := bstep (se 1 (by rfl) ⟨644390, by rfl⟩ : syracuseStep 859187 = 1288781) B1288781
theorem B728129 : Blo 507795 728129 := bstep (se 2 (by rfl) ⟨273048, by rfl⟩ : syracuseStep 728129 = 546097) B546097
theorem B5905477 : Blo 507795 5905477 := bstep (se 4 (by rfl) ⟨553638, by rfl⟩ : syracuseStep 5905477 = 1107277) B1107277
theorem B3873905 : Blo 507795 3873905 := bstep (se 2 (by rfl) ⟨1452714, by rfl⟩ : syracuseStep 3873905 = 2905429) B2905429
theorem B859315 : Blo 507795 859315 := bstep (se 1 (by rfl) ⟨644486, by rfl⟩ : syracuseStep 859315 = 1288973) B1288973
theorem B1285379 : Blo 507795 1285379 := bstep (se 1 (by rfl) ⟨964034, by rfl⟩ : syracuseStep 1285379 = 1928069) B1928069
theorem B859457 : Blo 507795 859457 := bstep (se 2 (by rfl) ⟨322296, by rfl⟩ : syracuseStep 859457 = 644593) B644593
theorem B2071921 : Blo 507795 2071921 := bstep (se 2 (by rfl) ⟨776970, by rfl⟩ : syracuseStep 2071921 = 1553941) B1553941
theorem B1449389 : Blo 507795 1449389 := bstep (se 3 (by rfl) ⟨271760, by rfl⟩ : syracuseStep 1449389 = 543521) B543521
theorem B859585 : Blo 507795 859585 := bstep (se 2 (by rfl) ⟨322344, by rfl⟩ : syracuseStep 859585 = 644689) B644689
theorem B1285571 : Blo 507795 1285571 := bstep (se 1 (by rfl) ⟨964178, by rfl⟩ : syracuseStep 1285571 = 1928357) B1928357
theorem B859619 : Blo 507795 859619 := bstep (se 1 (by rfl) ⟨644714, by rfl⟩ : syracuseStep 859619 = 1289429) B1289429
theorem B2760227 : Blo 507795 2760227 := bstep (se 1 (by rfl) ⟨2070170, by rfl⟩ : syracuseStep 2760227 = 4140341) B4140341
theorem B1449571 : Blo 507795 1449571 := bstep (se 1 (by rfl) ⟨1087178, by rfl⟩ : syracuseStep 1449571 = 2174357) B2174357
theorem B859747 : Blo 507795 859747 := bstep (se 1 (by rfl) ⟨644810, by rfl⟩ : syracuseStep 859747 = 1289621) B1289621
theorem B859889 : Blo 507795 859889 := bstep (se 2 (by rfl) ⟨322458, by rfl⟩ : syracuseStep 859889 = 644917) B644917
theorem B1449731 : Blo 507795 1449731 := bstep (se 1 (by rfl) ⟨1087298, by rfl⟩ : syracuseStep 1449731 = 2174597) B2174597
theorem B761699 : Blo 507795 761699 := bstep (se 1 (by rfl) ⟨571274, by rfl⟩ : syracuseStep 761699 = 1142549) B1142549
theorem B860017 : Blo 507795 860017 := bstep (se 2 (by rfl) ⟨322506, by rfl⟩ : syracuseStep 860017 = 645013) B645013
theorem B761729 : Blo 507795 761729 := bstep (se 2 (by rfl) ⟨285648, by rfl⟩ : syracuseStep 761729 = 571297) B571297
theorem B761747 : Blo 507795 761747 := bstep (se 1 (by rfl) ⟨571310, by rfl⟩ : syracuseStep 761747 = 1142621) B1142621
theorem B860051 : Blo 507795 860051 := bstep (se 1 (by rfl) ⟨645038, by rfl⟩ : syracuseStep 860051 = 1290077) B1290077
theorem B761777 : Blo 507795 761777 := bstep (se 2 (by rfl) ⟨285666, by rfl⟩ : syracuseStep 761777 = 571333) B571333
theorem B761795 : Blo 507795 761795 := bstep (se 1 (by rfl) ⟨571346, by rfl⟩ : syracuseStep 761795 = 1142693) B1142693
theorem B761825 : Blo 507795 761825 := bstep (se 2 (by rfl) ⟨285684, by rfl⟩ : syracuseStep 761825 = 571369) B571369
theorem B761843 : Blo 507795 761843 := bstep (se 1 (by rfl) ⟨571382, by rfl⟩ : syracuseStep 761843 = 1142765) B1142765
theorem B761873 : Blo 507795 761873 := bstep (se 2 (by rfl) ⟨285702, by rfl⟩ : syracuseStep 761873 = 571405) B571405
theorem B860179 : Blo 507795 860179 := bstep (se 1 (by rfl) ⟨645134, by rfl⟩ : syracuseStep 860179 = 1290269) B1290269
theorem B761891 : Blo 507795 761891 := bstep (se 1 (by rfl) ⟨571418, by rfl⟩ : syracuseStep 761891 = 1142837) B1142837
theorem B1089571 : Blo 507795 1089571 := bstep (se 1 (by rfl) ⟨817178, by rfl⟩ : syracuseStep 1089571 = 1634357) B1634357
theorem B761921 : Blo 507795 761921 := bstep (se 2 (by rfl) ⟨285720, by rfl⟩ : syracuseStep 761921 = 571441) B571441
theorem B761939 : Blo 507795 761939 := bstep (se 1 (by rfl) ⟨571454, by rfl⟩ : syracuseStep 761939 = 1142909) B1142909
theorem B761969 : Blo 507795 761969 := bstep (se 2 (by rfl) ⟨285738, by rfl⟩ : syracuseStep 761969 = 571477) B571477
theorem B761987 : Blo 507795 761987 := bstep (se 1 (by rfl) ⟨571490, by rfl⟩ : syracuseStep 761987 = 1142981) B1142981
theorem B5218445 : Blo 507795 5218445 := bstep (se 3 (by rfl) ⟨978458, by rfl⟩ : syracuseStep 5218445 = 1956917) B1956917
theorem B762017 : Blo 507795 762017 := bstep (se 2 (by rfl) ⟨285756, by rfl⟩ : syracuseStep 762017 = 571513) B571513
theorem B860321 : Blo 507795 860321 := bstep (se 2 (by rfl) ⟨322620, by rfl⟩ : syracuseStep 860321 = 645241) B645241
theorem B762035 : Blo 507795 762035 := bstep (se 1 (by rfl) ⟨571526, by rfl⟩ : syracuseStep 762035 = 1143053) B1143053
theorem B762065 : Blo 507795 762065 := bstep (se 2 (by rfl) ⟨285774, by rfl⟩ : syracuseStep 762065 = 571549) B571549
theorem B3711203 : Blo 507795 3711203 := bstep (se 1 (by rfl) ⟨2783402, by rfl⟩ : syracuseStep 3711203 = 5566805) B5566805
theorem B762083 : Blo 507795 762083 := bstep (se 1 (by rfl) ⟨571562, by rfl⟩ : syracuseStep 762083 = 1143125) B1143125
theorem B762113 : Blo 507795 762113 := bstep (se 2 (by rfl) ⟨285792, by rfl⟩ : syracuseStep 762113 = 571585) B571585
theorem B762131 : Blo 507795 762131 := bstep (se 1 (by rfl) ⟨571598, by rfl⟩ : syracuseStep 762131 = 1143197) B1143197
theorem B860449 : Blo 507795 860449 := bstep (se 2 (by rfl) ⟨322668, by rfl⟩ : syracuseStep 860449 = 645337) B645337
theorem B762161 : Blo 507795 762161 := bstep (se 2 (by rfl) ⟨285810, by rfl⟩ : syracuseStep 762161 = 571621) B571621
theorem B762179 : Blo 507795 762179 := bstep (se 1 (by rfl) ⟨571634, by rfl⟩ : syracuseStep 762179 = 1143269) B1143269
theorem B860483 : Blo 507795 860483 := bstep (se 1 (by rfl) ⟨645362, by rfl⟩ : syracuseStep 860483 = 1290725) B1290725
theorem B762209 : Blo 507795 762209 := bstep (se 2 (by rfl) ⟨285828, by rfl⟩ : syracuseStep 762209 = 571657) B571657
theorem B1286513 : Blo 507795 1286513 := bstep (se 2 (by rfl) ⟨482442, by rfl⟩ : syracuseStep 1286513 = 964885) B964885
theorem B8954225 : Blo 507795 8954225 := bstep (se 2 (by rfl) ⟨3357834, by rfl⟩ : syracuseStep 8954225 = 6715669) B6715669
theorem B762227 : Blo 507795 762227 := bstep (se 1 (by rfl) ⟨571670, by rfl⟩ : syracuseStep 762227 = 1143341) B1143341
theorem B762257 : Blo 507795 762257 := bstep (se 2 (by rfl) ⟨285846, by rfl⟩ : syracuseStep 762257 = 571693) B571693
theorem B762275 : Blo 507795 762275 := bstep (se 1 (by rfl) ⟨571706, by rfl⟩ : syracuseStep 762275 = 1143413) B1143413
theorem B1286563 : Blo 507795 1286563 := bstep (se 1 (by rfl) ⟨964922, by rfl⟩ : syracuseStep 1286563 = 1929845) B1929845
theorem B762305 : Blo 507795 762305 := bstep (se 2 (by rfl) ⟨285864, by rfl⟩ : syracuseStep 762305 = 571729) B571729
theorem B860611 : Blo 507795 860611 := bstep (se 1 (by rfl) ⟨645458, by rfl⟩ : syracuseStep 860611 = 1290917) B1290917
theorem B5513669 : Blo 507795 5513669 := bstep (se 4 (by rfl) ⟨516906, by rfl⟩ : syracuseStep 5513669 = 1033813) B1033813
theorem B1941965 : Blo 507795 1941965 := bstep (se 3 (by rfl) ⟨364118, by rfl⟩ : syracuseStep 1941965 = 728237) B728237
theorem B762323 : Blo 507795 762323 := bstep (se 1 (by rfl) ⟨571742, by rfl⟩ : syracuseStep 762323 = 1143485) B1143485
theorem B762353 : Blo 507795 762353 := bstep (se 2 (by rfl) ⟨285882, by rfl⟩ : syracuseStep 762353 = 571765) B571765
theorem B762371 : Blo 507795 762371 := bstep (se 1 (by rfl) ⟨571778, by rfl⟩ : syracuseStep 762371 = 1143557) B1143557
theorem B762401 : Blo 507795 762401 := bstep (se 2 (by rfl) ⟨285900, by rfl⟩ : syracuseStep 762401 = 571801) B571801
theorem B1286705 : Blo 507795 1286705 := bstep (se 2 (by rfl) ⟨482514, by rfl⟩ : syracuseStep 1286705 = 965029) B965029
theorem B762419 : Blo 507795 762419 := bstep (se 1 (by rfl) ⟨571814, by rfl⟩ : syracuseStep 762419 = 1143629) B1143629
theorem B762449 : Blo 507795 762449 := bstep (se 2 (by rfl) ⟨285918, by rfl⟩ : syracuseStep 762449 = 571837) B571837
theorem B860753 : Blo 507795 860753 := bstep (se 2 (by rfl) ⟨322782, by rfl⟩ : syracuseStep 860753 = 645565) B645565
theorem B762467 : Blo 507795 762467 := bstep (se 1 (by rfl) ⟨571850, by rfl⟩ : syracuseStep 762467 = 1143701) B1143701
theorem B762497 : Blo 507795 762497 := bstep (se 2 (by rfl) ⟨285936, by rfl⟩ : syracuseStep 762497 = 571873) B571873
theorem B762515 : Blo 507795 762515 := bstep (se 1 (by rfl) ⟨571886, by rfl⟩ : syracuseStep 762515 = 1143773) B1143773
theorem B2171555 : Blo 507795 2171555 := bstep (se 1 (by rfl) ⟨1628666, by rfl⟩ : syracuseStep 2171555 = 3257333) B3257333
theorem B2073251 : Blo 507795 2073251 := bstep (se 1 (by rfl) ⟨1554938, by rfl⟩ : syracuseStep 2073251 = 3109877) B3109877
theorem B762545 : Blo 507795 762545 := bstep (se 2 (by rfl) ⟨285954, by rfl⟩ : syracuseStep 762545 = 571909) B571909
theorem B1548977 : Blo 507795 1548977 := bstep (se 2 (by rfl) ⟨580866, by rfl⟩ : syracuseStep 1548977 = 1161733) B1161733
theorem B762563 : Blo 507795 762563 := bstep (se 1 (by rfl) ⟨571922, by rfl⟩ : syracuseStep 762563 = 1143845) B1143845
theorem B860881 : Blo 507795 860881 := bstep (se 2 (by rfl) ⟨322830, by rfl⟩ : syracuseStep 860881 = 645661) B645661
theorem B762593 : Blo 507795 762593 := bstep (se 2 (by rfl) ⟨285972, by rfl⟩ : syracuseStep 762593 = 571945) B571945
theorem B762611 : Blo 507795 762611 := bstep (se 1 (by rfl) ⟨571958, by rfl⟩ : syracuseStep 762611 = 1143917) B1143917
theorem B860915 : Blo 507795 860915 := bstep (se 1 (by rfl) ⟨645686, by rfl⟩ : syracuseStep 860915 = 1291373) B1291373
theorem B762641 : Blo 507795 762641 := bstep (se 2 (by rfl) ⟨285990, by rfl⟩ : syracuseStep 762641 = 571981) B571981
theorem B762659 : Blo 507795 762659 := bstep (se 1 (by rfl) ⟨571994, by rfl⟩ : syracuseStep 762659 = 1143989) B1143989
theorem B1450801 : Blo 507795 1450801 := bstep (se 2 (by rfl) ⟨544050, by rfl⟩ : syracuseStep 1450801 = 1088101) B1088101
theorem B762689 : Blo 507795 762689 := bstep (se 2 (by rfl) ⟨286008, by rfl⟩ : syracuseStep 762689 = 572017) B572017
theorem B1844045 : Blo 507795 1844045 := bstep (se 3 (by rfl) ⟨345758, by rfl⟩ : syracuseStep 1844045 = 691517) B691517
theorem B762707 : Blo 507795 762707 := bstep (se 1 (by rfl) ⟨572030, by rfl⟩ : syracuseStep 762707 = 1144061) B1144061
theorem B762737 : Blo 507795 762737 := bstep (se 2 (by rfl) ⟨286026, by rfl⟩ : syracuseStep 762737 = 572053) B572053
theorem B1090417 : Blo 507795 1090417 := bstep (se 2 (by rfl) ⟨408906, by rfl⟩ : syracuseStep 1090417 = 817813) B817813
theorem B861043 : Blo 507795 861043 := bstep (se 1 (by rfl) ⟨645782, by rfl⟩ : syracuseStep 861043 = 1291565) B1291565
theorem B762755 : Blo 507795 762755 := bstep (se 1 (by rfl) ⟨572066, by rfl⟩ : syracuseStep 762755 = 1144133) B1144133
theorem B2761613 : Blo 507795 2761613 := bstep (se 3 (by rfl) ⟨517802, by rfl⟩ : syracuseStep 2761613 = 1035605) B1035605
theorem B762785 : Blo 507795 762785 := bstep (se 2 (by rfl) ⟨286044, by rfl⟩ : syracuseStep 762785 = 572089) B572089
theorem B762803 : Blo 507795 762803 := bstep (se 1 (by rfl) ⟨572102, by rfl⟩ : syracuseStep 762803 = 1144205) B1144205
theorem B762833 : Blo 507795 762833 := bstep (se 2 (by rfl) ⟨286062, by rfl⟩ : syracuseStep 762833 = 572125) B572125
theorem B762851 : Blo 507795 762851 := bstep (se 1 (by rfl) ⟨572138, by rfl⟩ : syracuseStep 762851 = 1144277) B1144277
theorem B762881 : Blo 507795 762881 := bstep (se 2 (by rfl) ⟨286080, by rfl⟩ : syracuseStep 762881 = 572161) B572161
theorem B861185 : Blo 507795 861185 := bstep (se 2 (by rfl) ⟨322944, by rfl⟩ : syracuseStep 861185 = 645889) B645889
theorem B762899 : Blo 507795 762899 := bstep (se 1 (by rfl) ⟨572174, by rfl⟩ : syracuseStep 762899 = 1144349) B1144349
theorem B762929 : Blo 507795 762929 := bstep (se 2 (by rfl) ⟨286098, by rfl⟩ : syracuseStep 762929 = 572197) B572197
theorem B14754869 : Blo 507795 14754869 := bstep (se 5 (by rfl) ⟨691634, by rfl⟩ : syracuseStep 14754869 = 1383269) B1383269
theorem B762947 : Blo 507795 762947 := bstep (se 1 (by rfl) ⟨572210, by rfl⟩ : syracuseStep 762947 = 1144421) B1144421
theorem B762977 : Blo 507795 762977 := bstep (se 2 (by rfl) ⟨286116, by rfl⟩ : syracuseStep 762977 = 572233) B572233
theorem B762995 : Blo 507795 762995 := bstep (se 1 (by rfl) ⟨572246, by rfl⟩ : syracuseStep 762995 = 1144493) B1144493
theorem B861313 : Blo 507795 861313 := bstep (se 2 (by rfl) ⟨322992, by rfl⟩ : syracuseStep 861313 = 645985) B645985
theorem B763025 : Blo 507795 763025 := bstep (se 2 (by rfl) ⟨286134, by rfl⟩ : syracuseStep 763025 = 572269) B572269
theorem B763043 : Blo 507795 763043 := bstep (se 1 (by rfl) ⟨572282, by rfl⟩ : syracuseStep 763043 = 1144565) B1144565
theorem B861347 : Blo 507795 861347 := bstep (se 1 (by rfl) ⟨646010, by rfl⟩ : syracuseStep 861347 = 1292021) B1292021
theorem B763073 : Blo 507795 763073 := bstep (se 2 (by rfl) ⟨286152, by rfl⟩ : syracuseStep 763073 = 572305) B572305
theorem B763091 : Blo 507795 763091 := bstep (se 1 (by rfl) ⟨572318, by rfl⟩ : syracuseStep 763091 = 1144637) B1144637
theorem B763121 : Blo 507795 763121 := bstep (se 2 (by rfl) ⟨286170, by rfl⟩ : syracuseStep 763121 = 572341) B572341
theorem B763139 : Blo 507795 763139 := bstep (se 1 (by rfl) ⟨572354, by rfl⟩ : syracuseStep 763139 = 1144709) B1144709
theorem B763169 : Blo 507795 763169 := bstep (se 2 (by rfl) ⟨286188, by rfl⟩ : syracuseStep 763169 = 572377) B572377
theorem B861475 : Blo 507795 861475 := bstep (se 1 (by rfl) ⟨646106, by rfl⟩ : syracuseStep 861475 = 1292213) B1292213
theorem B763187 : Blo 507795 763187 := bstep (se 1 (by rfl) ⟨572390, by rfl⟩ : syracuseStep 763187 = 1144781) B1144781
theorem B763217 : Blo 507795 763217 := bstep (se 2 (by rfl) ⟨286206, by rfl⟩ : syracuseStep 763217 = 572413) B572413
theorem B763235 : Blo 507795 763235 := bstep (se 1 (by rfl) ⟨572426, by rfl⟩ : syracuseStep 763235 = 1144853) B1144853
theorem B763265 : Blo 507795 763265 := bstep (se 2 (by rfl) ⟨286224, by rfl⟩ : syracuseStep 763265 = 572449) B572449
theorem B763283 : Blo 507795 763283 := bstep (se 1 (by rfl) ⟨572462, by rfl⟩ : syracuseStep 763283 = 1144925) B1144925
theorem B763313 : Blo 507795 763313 := bstep (se 2 (by rfl) ⟨286242, by rfl⟩ : syracuseStep 763313 = 572485) B572485
theorem B861617 : Blo 507795 861617 := bstep (se 2 (by rfl) ⟨323106, by rfl⟩ : syracuseStep 861617 = 646213) B646213
theorem B763331 : Blo 507795 763331 := bstep (se 1 (by rfl) ⟨572498, by rfl⟩ : syracuseStep 763331 = 1144997) B1144997
theorem B763361 : Blo 507795 763361 := bstep (se 2 (by rfl) ⟨286260, by rfl⟩ : syracuseStep 763361 = 572521) B572521
theorem B763379 : Blo 507795 763379 := bstep (se 1 (by rfl) ⟨572534, by rfl⟩ : syracuseStep 763379 = 1145069) B1145069
theorem B2991629 : Blo 507795 2991629 := bstep (se 3 (by rfl) ⟨560930, by rfl⟩ : syracuseStep 2991629 = 1121861) B1121861
theorem B1287697 : Blo 507795 1287697 := bstep (se 2 (by rfl) ⟨482886, by rfl⟩ : syracuseStep 1287697 = 965773) B965773
theorem B763409 : Blo 507795 763409 := bstep (se 2 (by rfl) ⟨286278, by rfl⟩ : syracuseStep 763409 = 572557) B572557
theorem B763427 : Blo 507795 763427 := bstep (se 1 (by rfl) ⟨572570, by rfl⟩ : syracuseStep 763427 = 1145141) B1145141
theorem B861745 : Blo 507795 861745 := bstep (se 2 (by rfl) ⟨323154, by rfl⟩ : syracuseStep 861745 = 646309) B646309
theorem B763457 : Blo 507795 763457 := bstep (se 2 (by rfl) ⟨286296, by rfl⟩ : syracuseStep 763457 = 572593) B572593
theorem B763475 : Blo 507795 763475 := bstep (se 1 (by rfl) ⟨572606, by rfl⟩ : syracuseStep 763475 = 1145213) B1145213
theorem B861779 : Blo 507795 861779 := bstep (se 1 (by rfl) ⟨646334, by rfl⟩ : syracuseStep 861779 = 1292669) B1292669
theorem B763505 : Blo 507795 763505 := bstep (se 2 (by rfl) ⟨286314, by rfl⟩ : syracuseStep 763505 = 572629) B572629
theorem B8726129 : Blo 507795 8726129 := bstep (se 2 (by rfl) ⟨3272298, by rfl⟩ : syracuseStep 8726129 = 6544597) B6544597
theorem B763523 : Blo 507795 763523 := bstep (se 1 (by rfl) ⟨572642, by rfl⟩ : syracuseStep 763523 = 1145285) B1145285
theorem B763553 : Blo 507795 763553 := bstep (se 2 (by rfl) ⟨286332, by rfl⟩ : syracuseStep 763553 = 572665) B572665
theorem B763571 : Blo 507795 763571 := bstep (se 1 (by rfl) ⟨572678, by rfl⟩ : syracuseStep 763571 = 1145357) B1145357
theorem B763601 : Blo 507795 763601 := bstep (se 2 (by rfl) ⟨286350, by rfl⟩ : syracuseStep 763601 = 572701) B572701
theorem B861907 : Blo 507795 861907 := bstep (se 1 (by rfl) ⟨646430, by rfl⟩ : syracuseStep 861907 = 1292861) B1292861
theorem B763619 : Blo 507795 763619 := bstep (se 1 (by rfl) ⟨572714, by rfl⟩ : syracuseStep 763619 = 1145429) B1145429
theorem B1713905 : Blo 507795 1713905 := bstep (se 2 (by rfl) ⟨642714, by rfl⟩ : syracuseStep 1713905 = 1285429) B1285429
theorem B763649 : Blo 507795 763649 := bstep (se 2 (by rfl) ⟨286368, by rfl⟩ : syracuseStep 763649 = 572737) B572737
theorem B763667 : Blo 507795 763667 := bstep (se 1 (by rfl) ⟨572750, by rfl⟩ : syracuseStep 763667 = 1145501) B1145501
theorem B1287971 : Blo 507795 1287971 := bstep (se 1 (by rfl) ⟨965978, by rfl⟩ : syracuseStep 1287971 = 1931957) B1931957
theorem B763697 : Blo 507795 763697 := bstep (se 2 (by rfl) ⟨286386, by rfl⟩ : syracuseStep 763697 = 572773) B572773
theorem B763715 : Blo 507795 763715 := bstep (se 1 (by rfl) ⟨572786, by rfl⟩ : syracuseStep 763715 = 1145573) B1145573
theorem B763745 : Blo 507795 763745 := bstep (se 2 (by rfl) ⟨286404, by rfl⟩ : syracuseStep 763745 = 572809) B572809
theorem B862049 : Blo 507795 862049 := bstep (se 2 (by rfl) ⟨323268, by rfl⟩ : syracuseStep 862049 = 646537) B646537
theorem B1222499 : Blo 507795 1222499 := bstep (se 1 (by rfl) ⟨916874, by rfl⟩ : syracuseStep 1222499 = 1833749) B1833749
theorem B763763 : Blo 507795 763763 := bstep (se 1 (by rfl) ⟨572822, by rfl⟩ : syracuseStep 763763 = 1145645) B1145645
theorem B763793 : Blo 507795 763793 := bstep (se 2 (by rfl) ⟨286422, by rfl⟩ : syracuseStep 763793 = 572845) B572845
theorem B763811 : Blo 507795 763811 := bstep (se 1 (by rfl) ⟨572858, by rfl⟩ : syracuseStep 763811 = 1145717) B1145717
theorem B1222577 : Blo 507795 1222577 := bstep (se 2 (by rfl) ⟨458466, by rfl⟩ : syracuseStep 1222577 = 916933) B916933
theorem B763841 : Blo 507795 763841 := bstep (se 2 (by rfl) ⟨286440, by rfl⟩ : syracuseStep 763841 = 572881) B572881
theorem B2893765 : Blo 507795 2893765 := bstep (se 4 (by rfl) ⟨271290, by rfl⟩ : syracuseStep 2893765 = 542581) B542581
theorem B763859 : Blo 507795 763859 := bstep (se 1 (by rfl) ⟨572894, by rfl⟩ : syracuseStep 763859 = 1145789) B1145789
theorem B862177 : Blo 507795 862177 := bstep (se 2 (by rfl) ⟨323316, by rfl⟩ : syracuseStep 862177 = 646633) B646633
theorem B1288163 : Blo 507795 1288163 := bstep (se 1 (by rfl) ⟨966122, by rfl⟩ : syracuseStep 1288163 = 1932245) B1932245
theorem B763889 : Blo 507795 763889 := bstep (se 2 (by rfl) ⟨286458, by rfl⟩ : syracuseStep 763889 = 572917) B572917
theorem B763907 : Blo 507795 763907 := bstep (se 1 (by rfl) ⟨572930, by rfl⟩ : syracuseStep 763907 = 1145861) B1145861
theorem B862211 : Blo 507795 862211 := bstep (se 1 (by rfl) ⟨646658, by rfl⟩ : syracuseStep 862211 = 1293317) B1293317
theorem B763937 : Blo 507795 763937 := bstep (se 2 (by rfl) ⟨286476, by rfl⟩ : syracuseStep 763937 = 572953) B572953
theorem B1452077 : Blo 507795 1452077 := bstep (se 3 (by rfl) ⟨272264, by rfl⟩ : syracuseStep 1452077 = 544529) B544529
theorem B763955 : Blo 507795 763955 := bstep (se 1 (by rfl) ⟨572966, by rfl⟩ : syracuseStep 763955 = 1145933) B1145933
theorem B763985 : Blo 507795 763985 := bstep (se 2 (by rfl) ⟨286494, by rfl⟩ : syracuseStep 763985 = 572989) B572989
theorem B764003 : Blo 507795 764003 := bstep (se 1 (by rfl) ⟨573002, by rfl⟩ : syracuseStep 764003 = 1146005) B1146005
theorem B1222769 : Blo 507795 1222769 := bstep (se 2 (by rfl) ⟨458538, by rfl⟩ : syracuseStep 1222769 = 917077) B917077
theorem B764033 : Blo 507795 764033 := bstep (se 2 (by rfl) ⟨286512, by rfl⟩ : syracuseStep 764033 = 573025) B573025
theorem B862339 : Blo 507795 862339 := bstep (se 1 (by rfl) ⟨646754, by rfl⟩ : syracuseStep 862339 = 1293509) B1293509
theorem B764051 : Blo 507795 764051 := bstep (se 1 (by rfl) ⟨573038, by rfl⟩ : syracuseStep 764051 = 1146077) B1146077
theorem B1747117 : Blo 507795 1747117 := bstep (se 3 (by rfl) ⟨327584, by rfl⟩ : syracuseStep 1747117 = 655169) B655169
theorem B764081 : Blo 507795 764081 := bstep (se 2 (by rfl) ⟨286530, by rfl⟩ : syracuseStep 764081 = 573061) B573061
theorem B764099 : Blo 507795 764099 := bstep (se 1 (by rfl) ⟨573074, by rfl⟩ : syracuseStep 764099 = 1146149) B1146149
theorem B764129 : Blo 507795 764129 := bstep (se 2 (by rfl) ⟨286548, by rfl⟩ : syracuseStep 764129 = 573097) B573097
theorem B1452259 : Blo 507795 1452259 := bstep (se 1 (by rfl) ⟨1089194, by rfl⟩ : syracuseStep 1452259 = 2178389) B2178389
theorem B764147 : Blo 507795 764147 := bstep (se 1 (by rfl) ⟨573110, by rfl⟩ : syracuseStep 764147 = 1146221) B1146221
theorem B1714445 : Blo 507795 1714445 := bstep (se 3 (by rfl) ⟨321458, by rfl⟩ : syracuseStep 1714445 = 642917) B642917
theorem B764177 : Blo 507795 764177 := bstep (se 2 (by rfl) ⟨286566, by rfl⟩ : syracuseStep 764177 = 573133) B573133
theorem B1452305 : Blo 507795 1452305 := bstep (se 2 (by rfl) ⟨544614, by rfl⟩ : syracuseStep 1452305 = 1089229) B1089229
theorem B862481 : Blo 507795 862481 := bstep (se 2 (by rfl) ⟨323430, by rfl⟩ : syracuseStep 862481 = 646861) B646861
theorem B764195 : Blo 507795 764195 := bstep (se 1 (by rfl) ⟨573146, by rfl⟩ : syracuseStep 764195 = 1146293) B1146293
theorem B764225 : Blo 507795 764225 := bstep (se 2 (by rfl) ⟨286584, by rfl⟩ : syracuseStep 764225 = 573169) B573169
theorem B1714499 : Blo 507795 1714499 := bstep (se 1 (by rfl) ⟨1285874, by rfl⟩ : syracuseStep 1714499 = 2571749) B2571749
theorem B764243 : Blo 507795 764243 := bstep (se 1 (by rfl) ⟨573182, by rfl⟩ : syracuseStep 764243 = 1146365) B1146365
theorem B764273 : Blo 507795 764273 := bstep (se 2 (by rfl) ⟨286602, by rfl⟩ : syracuseStep 764273 = 573205) B573205
theorem B764291 : Blo 507795 764291 := bstep (se 1 (by rfl) ⟨573218, by rfl⟩ : syracuseStep 764291 = 1146437) B1146437
theorem B1223057 : Blo 507795 1223057 := bstep (se 2 (by rfl) ⟨458646, by rfl⟩ : syracuseStep 1223057 = 917293) B917293
theorem B862609 : Blo 507795 862609 := bstep (se 2 (by rfl) ⟨323478, by rfl⟩ : syracuseStep 862609 = 646957) B646957
theorem B764321 : Blo 507795 764321 := bstep (se 2 (by rfl) ⟨286620, by rfl⟩ : syracuseStep 764321 = 573241) B573241
theorem B764339 : Blo 507795 764339 := bstep (se 1 (by rfl) ⟨573254, by rfl⟩ : syracuseStep 764339 = 1146509) B1146509
theorem B862643 : Blo 507795 862643 := bstep (se 1 (by rfl) ⟨646982, by rfl⟩ : syracuseStep 862643 = 1293965) B1293965
theorem B764369 : Blo 507795 764369 := bstep (se 2 (by rfl) ⟨286638, by rfl⟩ : syracuseStep 764369 = 573277) B573277
theorem B764387 : Blo 507795 764387 := bstep (se 1 (by rfl) ⟨573290, by rfl⟩ : syracuseStep 764387 = 1146581) B1146581
theorem B764417 : Blo 507795 764417 := bstep (se 2 (by rfl) ⟨286656, by rfl⟩ : syracuseStep 764417 = 573313) B573313
theorem B764435 : Blo 507795 764435 := bstep (se 1 (by rfl) ⟨573326, by rfl⟩ : syracuseStep 764435 = 1146653) B1146653
theorem B764465 : Blo 507795 764465 := bstep (se 2 (by rfl) ⟨286674, by rfl⟩ : syracuseStep 764465 = 573349) B573349
theorem B862771 : Blo 507795 862771 := bstep (se 1 (by rfl) ⟨647078, by rfl⟩ : syracuseStep 862771 = 1294157) B1294157
theorem B764483 : Blo 507795 764483 := bstep (se 1 (by rfl) ⟨573362, by rfl⟩ : syracuseStep 764483 = 1146725) B1146725
theorem B1714769 : Blo 507795 1714769 := bstep (se 2 (by rfl) ⟨643038, by rfl⟩ : syracuseStep 1714769 = 1286077) B1286077
theorem B764513 : Blo 507795 764513 := bstep (se 2 (by rfl) ⟨286692, by rfl⟩ : syracuseStep 764513 = 573385) B573385
theorem B764531 : Blo 507795 764531 := bstep (se 1 (by rfl) ⟨573398, by rfl⟩ : syracuseStep 764531 = 1146797) B1146797
theorem B764561 : Blo 507795 764561 := bstep (se 2 (by rfl) ⟨286710, by rfl⟩ : syracuseStep 764561 = 573421) B573421
theorem B764579 : Blo 507795 764579 := bstep (se 1 (by rfl) ⟨573434, by rfl⟩ : syracuseStep 764579 = 1146869) B1146869
theorem B764609 : Blo 507795 764609 := bstep (se 2 (by rfl) ⟨286728, by rfl⟩ : syracuseStep 764609 = 573457) B573457
theorem B862913 : Blo 507795 862913 := bstep (se 2 (by rfl) ⟨323592, by rfl⟩ : syracuseStep 862913 = 647185) B647185
theorem B1092305 : Blo 507795 1092305 := bstep (se 2 (by rfl) ⟨409614, by rfl⟩ : syracuseStep 1092305 = 819229) B819229
theorem B764627 : Blo 507795 764627 := bstep (se 1 (by rfl) ⟨573470, by rfl⟩ : syracuseStep 764627 = 1146941) B1146941
theorem B764657 : Blo 507795 764657 := bstep (se 2 (by rfl) ⟨286746, by rfl⟩ : syracuseStep 764657 = 573493) B573493
theorem B764675 : Blo 507795 764675 := bstep (se 1 (by rfl) ⟨573506, by rfl⟩ : syracuseStep 764675 = 1147013) B1147013
theorem B764705 : Blo 507795 764705 := bstep (se 2 (by rfl) ⟨286764, by rfl⟩ : syracuseStep 764705 = 573529) B573529
theorem B764723 : Blo 507795 764723 := bstep (se 1 (by rfl) ⟨573542, by rfl⟩ : syracuseStep 764723 = 1147085) B1147085
theorem B863041 : Blo 507795 863041 := bstep (se 2 (by rfl) ⟨323640, by rfl⟩ : syracuseStep 863041 = 647281) B647281
theorem B764753 : Blo 507795 764753 := bstep (se 2 (by rfl) ⟨286782, by rfl⟩ : syracuseStep 764753 = 573565) B573565
theorem B764771 : Blo 507795 764771 := bstep (se 1 (by rfl) ⟨573578, by rfl⟩ : syracuseStep 764771 = 1147157) B1147157
theorem B863075 : Blo 507795 863075 := bstep (se 1 (by rfl) ⟨647306, by rfl⟩ : syracuseStep 863075 = 1294613) B1294613
theorem B764801 : Blo 507795 764801 := bstep (se 2 (by rfl) ⟨286800, by rfl⟩ : syracuseStep 764801 = 573601) B573601
theorem B1289105 : Blo 507795 1289105 := bstep (se 2 (by rfl) ⟨483414, by rfl⟩ : syracuseStep 1289105 = 966829) B966829
theorem B764819 : Blo 507795 764819 := bstep (se 1 (by rfl) ⟨573614, by rfl⟩ : syracuseStep 764819 = 1147229) B1147229
theorem B764849 : Blo 507795 764849 := bstep (se 2 (by rfl) ⟨286818, by rfl⟩ : syracuseStep 764849 = 573637) B573637
theorem B1289155 : Blo 507795 1289155 := bstep (se 1 (by rfl) ⟨966866, by rfl⟩ : syracuseStep 1289155 = 1933733) B1933733
theorem B764867 : Blo 507795 764867 := bstep (se 1 (by rfl) ⟨573650, by rfl⟩ : syracuseStep 764867 = 1147301) B1147301
theorem B764897 : Blo 507795 764897 := bstep (se 2 (by rfl) ⟨286836, by rfl⟩ : syracuseStep 764897 = 573673) B573673
theorem B863203 : Blo 507795 863203 := bstep (se 1 (by rfl) ⟨647402, by rfl⟩ : syracuseStep 863203 = 1294805) B1294805
theorem B764915 : Blo 507795 764915 := bstep (se 1 (by rfl) ⟨573686, by rfl⟩ : syracuseStep 764915 = 1147373) B1147373
theorem B764945 : Blo 507795 764945 := bstep (se 2 (by rfl) ⟨286854, by rfl⟩ : syracuseStep 764945 = 573709) B573709
theorem B764963 : Blo 507795 764963 := bstep (se 1 (by rfl) ⟨573722, by rfl⟩ : syracuseStep 764963 = 1147445) B1147445
theorem B764993 : Blo 507795 764993 := bstep (se 2 (by rfl) ⟨286872, by rfl⟩ : syracuseStep 764993 = 573745) B573745
theorem B1289297 : Blo 507795 1289297 := bstep (se 2 (by rfl) ⟨483486, by rfl⟩ : syracuseStep 1289297 = 966973) B966973
theorem B765011 : Blo 507795 765011 := bstep (se 1 (by rfl) ⟨573758, by rfl⟩ : syracuseStep 765011 = 1147517) B1147517
theorem B1715309 : Blo 507795 1715309 := bstep (se 3 (by rfl) ⟨321620, by rfl⟩ : syracuseStep 1715309 = 643241) B643241
theorem B765041 : Blo 507795 765041 := bstep (se 2 (by rfl) ⟨286890, by rfl⟩ : syracuseStep 765041 = 573781) B573781
theorem B863345 : Blo 507795 863345 := bstep (se 2 (by rfl) ⟨323754, by rfl⟩ : syracuseStep 863345 = 647509) B647509
theorem B765059 : Blo 507795 765059 := bstep (se 1 (by rfl) ⟨573794, by rfl⟩ : syracuseStep 765059 = 1147589) B1147589
theorem B765089 : Blo 507795 765089 := bstep (se 2 (by rfl) ⟨286908, by rfl⟩ : syracuseStep 765089 = 573817) B573817
theorem B1715363 : Blo 507795 1715363 := bstep (se 1 (by rfl) ⟨1286522, by rfl⟩ : syracuseStep 1715363 = 2573045) B2573045
theorem B765107 : Blo 507795 765107 := bstep (se 1 (by rfl) ⟨573830, by rfl⟩ : syracuseStep 765107 = 1147661) B1147661
theorem B765137 : Blo 507795 765137 := bstep (se 2 (by rfl) ⟨286926, by rfl⟩ : syracuseStep 765137 = 573853) B573853
theorem B1158371 : Blo 507795 1158371 := bstep (se 1 (by rfl) ⟨868778, by rfl⟩ : syracuseStep 1158371 = 1737557) B1737557
theorem B765155 : Blo 507795 765155 := bstep (se 1 (by rfl) ⟨573866, by rfl⟩ : syracuseStep 765155 = 1147733) B1147733
theorem B863473 : Blo 507795 863473 := bstep (se 2 (by rfl) ⟨323802, by rfl⟩ : syracuseStep 863473 = 647605) B647605
theorem B765185 : Blo 507795 765185 := bstep (se 2 (by rfl) ⟨286944, by rfl⟩ : syracuseStep 765185 = 573889) B573889
theorem B765203 : Blo 507795 765203 := bstep (se 1 (by rfl) ⟨573902, by rfl⟩ : syracuseStep 765203 = 1147805) B1147805
theorem B863507 : Blo 507795 863507 := bstep (se 1 (by rfl) ⟨647630, by rfl⟩ : syracuseStep 863507 = 1295261) B1295261
theorem B765233 : Blo 507795 765233 := bstep (se 2 (by rfl) ⟨286962, by rfl⟩ : syracuseStep 765233 = 573925) B573925
theorem B765251 : Blo 507795 765251 := bstep (se 1 (by rfl) ⟨573938, by rfl⟩ : syracuseStep 765251 = 1147877) B1147877
theorem B765281 : Blo 507795 765281 := bstep (se 2 (by rfl) ⟨286980, by rfl⟩ : syracuseStep 765281 = 573961) B573961
theorem B765299 : Blo 507795 765299 := bstep (se 1 (by rfl) ⟨573974, by rfl⟩ : syracuseStep 765299 = 1147949) B1147949
theorem B765329 : Blo 507795 765329 := bstep (se 2 (by rfl) ⟨286998, by rfl⟩ : syracuseStep 765329 = 573997) B573997
theorem B863635 : Blo 507795 863635 := bstep (se 1 (by rfl) ⟨647726, by rfl⟩ : syracuseStep 863635 = 1295453) B1295453
theorem B765347 : Blo 507795 765347 := bstep (se 1 (by rfl) ⟨574010, by rfl⟩ : syracuseStep 765347 = 1148021) B1148021
theorem B1715633 : Blo 507795 1715633 := bstep (se 2 (by rfl) ⟨643362, by rfl⟩ : syracuseStep 1715633 = 1286725) B1286725
theorem B765377 : Blo 507795 765377 := bstep (se 2 (by rfl) ⟨287016, by rfl⟩ : syracuseStep 765377 = 574033) B574033
theorem B1486289 : Blo 507795 1486289 := bstep (se 2 (by rfl) ⟨557358, by rfl⟩ : syracuseStep 1486289 = 1114717) B1114717
theorem B765395 : Blo 507795 765395 := bstep (se 1 (by rfl) ⟨574046, by rfl⟩ : syracuseStep 765395 = 1148093) B1148093
theorem B765425 : Blo 507795 765425 := bstep (se 2 (by rfl) ⟨287034, by rfl⟩ : syracuseStep 765425 = 574069) B574069
theorem B765443 : Blo 507795 765443 := bstep (se 1 (by rfl) ⟨574082, by rfl⟩ : syracuseStep 765443 = 1148165) B1148165
theorem B765473 : Blo 507795 765473 := bstep (se 2 (by rfl) ⟨287052, by rfl⟩ : syracuseStep 765473 = 574105) B574105
theorem B765491 : Blo 507795 765491 := bstep (se 1 (by rfl) ⟨574118, by rfl⟩ : syracuseStep 765491 = 1148237) B1148237
theorem B765521 : Blo 507795 765521 := bstep (se 2 (by rfl) ⟨287070, by rfl⟩ : syracuseStep 765521 = 574141) B574141
theorem B765539 : Blo 507795 765539 := bstep (se 1 (by rfl) ⟨574154, by rfl⟩ : syracuseStep 765539 = 1148309) B1148309
theorem B765569 : Blo 507795 765569 := bstep (se 2 (by rfl) ⟨287088, by rfl⟩ : syracuseStep 765569 = 574177) B574177
theorem B765587 : Blo 507795 765587 := bstep (se 1 (by rfl) ⟨574190, by rfl⟩ : syracuseStep 765587 = 1148381) B1148381
theorem B765617 : Blo 507795 765617 := bstep (se 2 (by rfl) ⟨287106, by rfl⟩ : syracuseStep 765617 = 574213) B574213
theorem B765635 : Blo 507795 765635 := bstep (se 1 (by rfl) ⟨574226, by rfl⟩ : syracuseStep 765635 = 1148453) B1148453
theorem B1453763 : Blo 507795 1453763 := bstep (se 1 (by rfl) ⟨1090322, by rfl⟩ : syracuseStep 1453763 = 2180645) B2180645
theorem B765665 : Blo 507795 765665 := bstep (se 2 (by rfl) ⟨287124, by rfl⟩ : syracuseStep 765665 = 574249) B574249
theorem B765683 : Blo 507795 765683 := bstep (se 1 (by rfl) ⟨574262, by rfl⟩ : syracuseStep 765683 = 1148525) B1148525
theorem B765713 : Blo 507795 765713 := bstep (se 2 (by rfl) ⟨287142, by rfl⟩ : syracuseStep 765713 = 574285) B574285
theorem B765731 : Blo 507795 765731 := bstep (se 1 (by rfl) ⟨574298, by rfl⟩ : syracuseStep 765731 = 1148597) B1148597
theorem B765761 : Blo 507795 765761 := bstep (se 2 (by rfl) ⟨287160, by rfl⟩ : syracuseStep 765761 = 574321) B574321
theorem B765779 : Blo 507795 765779 := bstep (se 1 (by rfl) ⟨574334, by rfl⟩ : syracuseStep 765779 = 1148669) B1148669
theorem B765809 : Blo 507795 765809 := bstep (se 2 (by rfl) ⟨287178, by rfl⟩ : syracuseStep 765809 = 574357) B574357
theorem B765827 : Blo 507795 765827 := bstep (se 1 (by rfl) ⟨574370, by rfl⟩ : syracuseStep 765827 = 1148741) B1148741
theorem B2895749 : Blo 507795 2895749 := bstep (se 4 (by rfl) ⟨271476, by rfl⟩ : syracuseStep 2895749 = 542953) B542953
theorem B765857 : Blo 507795 765857 := bstep (se 2 (by rfl) ⟨287196, by rfl⟩ : syracuseStep 765857 = 574393) B574393
theorem B765875 : Blo 507795 765875 := bstep (se 1 (by rfl) ⟨574406, by rfl⟩ : syracuseStep 765875 = 1148813) B1148813
theorem B1716173 : Blo 507795 1716173 := bstep (se 3 (by rfl) ⟨321782, by rfl⟩ : syracuseStep 1716173 = 643565) B643565
theorem B765905 : Blo 507795 765905 := bstep (se 2 (by rfl) ⟨287214, by rfl⟩ : syracuseStep 765905 = 574429) B574429
theorem B765923 : Blo 507795 765923 := bstep (se 1 (by rfl) ⟨574442, by rfl⟩ : syracuseStep 765923 = 1148885) B1148885
theorem B765953 : Blo 507795 765953 := bstep (se 2 (by rfl) ⟨287232, by rfl⟩ : syracuseStep 765953 = 574465) B574465
theorem B1716227 : Blo 507795 1716227 := bstep (se 1 (by rfl) ⟨1287170, by rfl⟩ : syracuseStep 1716227 = 2574341) B2574341
theorem B765971 : Blo 507795 765971 := bstep (se 1 (by rfl) ⟨574478, by rfl⟩ : syracuseStep 765971 = 1148957) B1148957
theorem B1290289 : Blo 507795 1290289 := bstep (se 2 (by rfl) ⟨483858, by rfl⟩ : syracuseStep 1290289 = 967717) B967717
theorem B766001 : Blo 507795 766001 := bstep (se 2 (by rfl) ⟨287250, by rfl⟩ : syracuseStep 766001 = 574501) B574501
theorem B766019 : Blo 507795 766019 := bstep (se 1 (by rfl) ⟨574514, by rfl⟩ : syracuseStep 766019 = 1149029) B1149029
theorem B766049 : Blo 507795 766049 := bstep (se 2 (by rfl) ⟨287268, by rfl⟩ : syracuseStep 766049 = 574537) B574537
theorem B3584099 : Blo 507795 3584099 := bstep (se 1 (by rfl) ⟨2688074, by rfl⟩ : syracuseStep 3584099 = 5376149) B5376149
theorem B766067 : Blo 507795 766067 := bstep (se 1 (by rfl) ⟨574550, by rfl⟩ : syracuseStep 766067 = 1149101) B1149101
theorem B766097 : Blo 507795 766097 := bstep (se 2 (by rfl) ⟨287286, by rfl⟩ : syracuseStep 766097 = 574573) B574573
theorem B766115 : Blo 507795 766115 := bstep (se 1 (by rfl) ⟨574586, by rfl⟩ : syracuseStep 766115 = 1149173) B1149173
theorem B766145 : Blo 507795 766145 := bstep (se 2 (by rfl) ⟨287304, by rfl⟩ : syracuseStep 766145 = 574609) B574609
theorem B766163 : Blo 507795 766163 := bstep (se 1 (by rfl) ⟨574622, by rfl⟩ : syracuseStep 766163 = 1149245) B1149245
theorem B766193 : Blo 507795 766193 := bstep (se 2 (by rfl) ⟨287322, by rfl⟩ : syracuseStep 766193 = 574645) B574645
theorem B766211 : Blo 507795 766211 := bstep (se 1 (by rfl) ⟨574658, by rfl⟩ : syracuseStep 766211 = 1149317) B1149317
theorem B2175245 : Blo 507795 2175245 := bstep (se 3 (by rfl) ⟨407858, by rfl⟩ : syracuseStep 2175245 = 815717) B815717
theorem B1716497 : Blo 507795 1716497 := bstep (se 2 (by rfl) ⟨643686, by rfl⟩ : syracuseStep 1716497 = 1287373) B1287373
theorem B766241 : Blo 507795 766241 := bstep (se 2 (by rfl) ⟨287340, by rfl⟩ : syracuseStep 766241 = 574681) B574681
theorem B2175281 : Blo 507795 2175281 := bstep (se 2 (by rfl) ⟨815730, by rfl⟩ : syracuseStep 2175281 = 1631461) B1631461
theorem B766259 : Blo 507795 766259 := bstep (se 1 (by rfl) ⟨574694, by rfl⟩ : syracuseStep 766259 = 1149389) B1149389
theorem B1290563 : Blo 507795 1290563 := bstep (se 1 (by rfl) ⟨967922, by rfl⟩ : syracuseStep 1290563 = 1935845) B1935845
theorem B766289 : Blo 507795 766289 := bstep (se 2 (by rfl) ⟨287358, by rfl⟩ : syracuseStep 766289 = 574717) B574717
theorem B766307 : Blo 507795 766307 := bstep (se 1 (by rfl) ⟨574730, by rfl⟩ : syracuseStep 766307 = 1149461) B1149461
theorem B766337 : Blo 507795 766337 := bstep (se 2 (by rfl) ⟨287376, by rfl⟩ : syracuseStep 766337 = 574753) B574753
theorem B766355 : Blo 507795 766355 := bstep (se 1 (by rfl) ⟨574766, by rfl⟩ : syracuseStep 766355 = 1149533) B1149533
theorem B766385 : Blo 507795 766385 := bstep (se 2 (by rfl) ⟨287394, by rfl⟩ : syracuseStep 766385 = 574789) B574789
theorem B766403 : Blo 507795 766403 := bstep (se 1 (by rfl) ⟨574802, by rfl⟩ : syracuseStep 766403 = 1149605) B1149605
theorem B766433 : Blo 507795 766433 := bstep (se 2 (by rfl) ⟨287412, by rfl⟩ : syracuseStep 766433 = 574825) B574825
theorem B766451 : Blo 507795 766451 := bstep (se 1 (by rfl) ⟨574838, by rfl⟩ : syracuseStep 766451 = 1149677) B1149677
theorem B1290755 : Blo 507795 1290755 := bstep (se 1 (by rfl) ⟨968066, by rfl⟩ : syracuseStep 1290755 = 1936133) B1936133
theorem B2241037 : Blo 507795 2241037 := bstep (se 3 (by rfl) ⟨420194, by rfl⟩ : syracuseStep 2241037 = 840389) B840389
theorem B766481 : Blo 507795 766481 := bstep (se 2 (by rfl) ⟨287430, by rfl⟩ : syracuseStep 766481 = 574861) B574861
theorem B766499 : Blo 507795 766499 := bstep (se 1 (by rfl) ⟨574874, by rfl⟩ : syracuseStep 766499 = 1149749) B1149749
theorem B766529 : Blo 507795 766529 := bstep (se 2 (by rfl) ⟨287448, by rfl⟩ : syracuseStep 766529 = 574897) B574897
theorem B766547 : Blo 507795 766547 := bstep (se 1 (by rfl) ⟨574910, by rfl⟩ : syracuseStep 766547 = 1149821) B1149821
theorem B766577 : Blo 507795 766577 := bstep (se 2 (by rfl) ⟨287466, by rfl⟩ : syracuseStep 766577 = 574933) B574933
theorem B766595 : Blo 507795 766595 := bstep (se 1 (by rfl) ⟨574946, by rfl⟩ : syracuseStep 766595 = 1149893) B1149893
theorem B766625 : Blo 507795 766625 := bstep (se 2 (by rfl) ⟨287484, by rfl⟩ : syracuseStep 766625 = 574969) B574969
theorem B766643 : Blo 507795 766643 := bstep (se 1 (by rfl) ⟨574982, by rfl⟩ : syracuseStep 766643 = 1149965) B1149965
theorem B766673 : Blo 507795 766673 := bstep (se 2 (by rfl) ⟨287502, by rfl⟩ : syracuseStep 766673 = 575005) B575005
theorem B766691 : Blo 507795 766691 := bstep (se 1 (by rfl) ⟨575018, by rfl⟩ : syracuseStep 766691 = 1150037) B1150037
theorem B766721 : Blo 507795 766721 := bstep (se 2 (by rfl) ⟨287520, by rfl⟩ : syracuseStep 766721 = 575041) B575041
theorem B1553165 : Blo 507795 1553165 := bstep (se 3 (by rfl) ⟨291218, by rfl⟩ : syracuseStep 1553165 = 582437) B582437
theorem B766739 : Blo 507795 766739 := bstep (se 1 (by rfl) ⟨575054, by rfl⟩ : syracuseStep 766739 = 1150109) B1150109
theorem B1717037 : Blo 507795 1717037 := bstep (se 3 (by rfl) ⟨321944, by rfl⟩ : syracuseStep 1717037 = 643889) B643889
theorem B766769 : Blo 507795 766769 := bstep (se 2 (by rfl) ⟨287538, by rfl⟩ : syracuseStep 766769 = 575077) B575077
theorem B5813045 : Blo 507795 5813045 := bstep (se 5 (by rfl) ⟨272486, by rfl⟩ : syracuseStep 5813045 = 544973) B544973
theorem B766787 : Blo 507795 766787 := bstep (se 1 (by rfl) ⟨575090, by rfl⟩ : syracuseStep 766787 = 1150181) B1150181
theorem B766817 : Blo 507795 766817 := bstep (se 2 (by rfl) ⟨287556, by rfl⟩ : syracuseStep 766817 = 575113) B575113
theorem B1717091 : Blo 507795 1717091 := bstep (se 1 (by rfl) ⟨1287818, by rfl⟩ : syracuseStep 1717091 = 2575637) B2575637
theorem B766835 : Blo 507795 766835 := bstep (se 1 (by rfl) ⟨575126, by rfl⟩ : syracuseStep 766835 = 1150253) B1150253
theorem B1454993 : Blo 507795 1454993 := bstep (se 2 (by rfl) ⟨545622, by rfl⟩ : syracuseStep 1454993 = 1091245) B1091245
theorem B766865 : Blo 507795 766865 := bstep (se 2 (by rfl) ⟨287574, by rfl⟩ : syracuseStep 766865 = 575149) B575149
theorem B766883 : Blo 507795 766883 := bstep (se 1 (by rfl) ⟨575162, by rfl⟩ : syracuseStep 766883 = 1150325) B1150325
theorem B1749937 : Blo 507795 1749937 := bstep (se 2 (by rfl) ⟨656226, by rfl⟩ : syracuseStep 1749937 = 1312453) B1312453
theorem B766913 : Blo 507795 766913 := bstep (se 2 (by rfl) ⟨287592, by rfl⟩ : syracuseStep 766913 = 575185) B575185
theorem B766931 : Blo 507795 766931 := bstep (se 1 (by rfl) ⟨575198, by rfl⟩ : syracuseStep 766931 = 1150397) B1150397
theorem B766961 : Blo 507795 766961 := bstep (se 2 (by rfl) ⟨287610, by rfl⟩ : syracuseStep 766961 = 575221) B575221
theorem B766979 : Blo 507795 766979 := bstep (se 1 (by rfl) ⟨575234, by rfl⟩ : syracuseStep 766979 = 1150469) B1150469
theorem B767009 : Blo 507795 767009 := bstep (se 2 (by rfl) ⟨287628, by rfl⟩ : syracuseStep 767009 = 575257) B575257
theorem B767027 : Blo 507795 767027 := bstep (se 1 (by rfl) ⟨575270, by rfl⟩ : syracuseStep 767027 = 1150541) B1150541
theorem B767057 : Blo 507795 767057 := bstep (se 2 (by rfl) ⟨287646, by rfl⟩ : syracuseStep 767057 = 575293) B575293
theorem B767075 : Blo 507795 767075 := bstep (se 1 (by rfl) ⟨575306, by rfl⟩ : syracuseStep 767075 = 1150613) B1150613
theorem B1717361 : Blo 507795 1717361 := bstep (se 2 (by rfl) ⟨644010, by rfl⟩ : syracuseStep 1717361 = 1288021) B1288021
theorem B767105 : Blo 507795 767105 := bstep (se 2 (by rfl) ⟨287664, by rfl⟩ : syracuseStep 767105 = 575329) B575329
theorem B767123 : Blo 507795 767123 := bstep (se 1 (by rfl) ⟨575342, by rfl⟩ : syracuseStep 767123 = 1150685) B1150685
theorem B767153 : Blo 507795 767153 := bstep (se 2 (by rfl) ⟨287682, by rfl⟩ : syracuseStep 767153 = 575365) B575365
theorem B2766001 : Blo 507795 2766001 := bstep (se 2 (by rfl) ⟨1037250, by rfl⟩ : syracuseStep 2766001 = 2074501) B2074501
theorem B767171 : Blo 507795 767171 := bstep (se 1 (by rfl) ⟨575378, by rfl⟩ : syracuseStep 767171 = 1150757) B1150757
theorem B767201 : Blo 507795 767201 := bstep (se 2 (by rfl) ⟨287700, by rfl⟩ : syracuseStep 767201 = 575401) B575401
theorem B767219 : Blo 507795 767219 := bstep (se 1 (by rfl) ⟨575414, by rfl⟩ : syracuseStep 767219 = 1150829) B1150829
theorem B767249 : Blo 507795 767249 := bstep (se 2 (by rfl) ⟨287718, by rfl⟩ : syracuseStep 767249 = 575437) B575437
theorem B25212181 : Blo 507795 25212181 := bstep (se 6 (by rfl) ⟨590910, by rfl⟩ : syracuseStep 25212181 = 1181821) B1181821
theorem B767267 : Blo 507795 767267 := bstep (se 1 (by rfl) ⟨575450, by rfl⟩ : syracuseStep 767267 = 1150901) B1150901
theorem B734513 : Blo 507795 734513 := bstep (se 2 (by rfl) ⟨275442, by rfl⟩ : syracuseStep 734513 = 550885) B550885
theorem B767297 : Blo 507795 767297 := bstep (se 2 (by rfl) ⟨287736, by rfl⟩ : syracuseStep 767297 = 575473) B575473
theorem B767315 : Blo 507795 767315 := bstep (se 1 (by rfl) ⟨575486, by rfl⟩ : syracuseStep 767315 = 1150973) B1150973
theorem B767345 : Blo 507795 767345 := bstep (se 2 (by rfl) ⟨287754, by rfl⟩ : syracuseStep 767345 = 575509) B575509
theorem B767363 : Blo 507795 767363 := bstep (se 1 (by rfl) ⟨575522, by rfl⟩ : syracuseStep 767363 = 1151045) B1151045
theorem B767393 : Blo 507795 767393 := bstep (se 2 (by rfl) ⟨287772, by rfl⟩ : syracuseStep 767393 = 575545) B575545
theorem B1291697 : Blo 507795 1291697 := bstep (se 2 (by rfl) ⟨484386, by rfl⟩ : syracuseStep 1291697 = 968773) B968773
theorem B767411 : Blo 507795 767411 := bstep (se 1 (by rfl) ⟨575558, by rfl⟩ : syracuseStep 767411 = 1151117) B1151117
theorem B767441 : Blo 507795 767441 := bstep (se 2 (by rfl) ⟨287790, by rfl⟩ : syracuseStep 767441 = 575581) B575581
theorem B1291747 : Blo 507795 1291747 := bstep (se 1 (by rfl) ⟨968810, by rfl⟩ : syracuseStep 1291747 = 1937621) B1937621
theorem B767459 : Blo 507795 767459 := bstep (se 1 (by rfl) ⟨575594, by rfl⟩ : syracuseStep 767459 = 1151189) B1151189
theorem B767489 : Blo 507795 767489 := bstep (se 2 (by rfl) ⟨287808, by rfl⟩ : syracuseStep 767489 = 575617) B575617
theorem B767507 : Blo 507795 767507 := bstep (se 1 (by rfl) ⟨575630, by rfl⟩ : syracuseStep 767507 = 1151261) B1151261
theorem B767537 : Blo 507795 767537 := bstep (se 2 (by rfl) ⟨287826, by rfl⟩ : syracuseStep 767537 = 575653) B575653
theorem B964163 : Blo 507795 964163 := bstep (se 1 (by rfl) ⟨723122, by rfl⟩ : syracuseStep 964163 = 1446245) B1446245
theorem B767555 : Blo 507795 767555 := bstep (se 1 (by rfl) ⟨575666, by rfl⟩ : syracuseStep 767555 = 1151333) B1151333
theorem B767585 : Blo 507795 767585 := bstep (se 2 (by rfl) ⟨287844, by rfl⟩ : syracuseStep 767585 = 575689) B575689
theorem B1291889 : Blo 507795 1291889 := bstep (se 2 (by rfl) ⟨484458, by rfl⟩ : syracuseStep 1291889 = 968917) B968917
theorem B767603 : Blo 507795 767603 := bstep (se 1 (by rfl) ⟨575702, by rfl⟩ : syracuseStep 767603 = 1151405) B1151405
theorem B1717901 : Blo 507795 1717901 := bstep (se 3 (by rfl) ⟨322106, by rfl⟩ : syracuseStep 1717901 = 644213) B644213
theorem B767633 : Blo 507795 767633 := bstep (se 2 (by rfl) ⟨287862, by rfl⟩ : syracuseStep 767633 = 575725) B575725
theorem B767651 : Blo 507795 767651 := bstep (se 1 (by rfl) ⟨575738, by rfl⟩ : syracuseStep 767651 = 1151477) B1151477
theorem B767681 : Blo 507795 767681 := bstep (se 2 (by rfl) ⟨287880, by rfl⟩ : syracuseStep 767681 = 575761) B575761
theorem B1717955 : Blo 507795 1717955 := bstep (se 1 (by rfl) ⟨1288466, by rfl⟩ : syracuseStep 1717955 = 2576933) B2576933
theorem B4896611 : Blo 507795 4896611 := bstep (se 1 (by rfl) ⟨3672458, by rfl⟩ : syracuseStep 4896611 = 7344917) B7344917
theorem B571315 : Blo 507795 571315 := bstep (se 1 (by rfl) ⟨428486, by rfl⟩ : syracuseStep 571315 = 856973) B856973
theorem B1718225 : Blo 507795 1718225 := bstep (se 2 (by rfl) ⟨644334, by rfl⟩ : syracuseStep 1718225 = 1288669) B1288669
theorem B571459 : Blo 507795 571459 := bstep (se 1 (by rfl) ⟨428594, by rfl⟩ : syracuseStep 571459 = 857189) B857189
theorem B571603 : Blo 507795 571603 := bstep (se 1 (by rfl) ⟨428702, by rfl⟩ : syracuseStep 571603 = 857405) B857405
theorem B1456451 : Blo 507795 1456451 := bstep (se 1 (by rfl) ⟨1092338, by rfl⟩ : syracuseStep 1456451 = 2184677) B2184677
theorem B571747 : Blo 507795 571747 := bstep (se 1 (by rfl) ⟨428810, by rfl⟩ : syracuseStep 571747 = 857621) B857621
theorem B1718765 : Blo 507795 1718765 := bstep (se 3 (by rfl) ⟨322268, by rfl⟩ : syracuseStep 1718765 = 644537) B644537
theorem B965105 : Blo 507795 965105 := bstep (se 2 (by rfl) ⟨361914, by rfl⟩ : syracuseStep 965105 = 723829) B723829
theorem B571891 : Blo 507795 571891 := bstep (se 1 (by rfl) ⟨428918, by rfl⟩ : syracuseStep 571891 = 857837) B857837
theorem B1718819 : Blo 507795 1718819 := bstep (se 1 (by rfl) ⟨1289114, by rfl⟩ : syracuseStep 1718819 = 2578229) B2578229
theorem B1030705 : Blo 507795 1030705 := bstep (se 2 (by rfl) ⟨386514, by rfl⟩ : syracuseStep 1030705 = 773029) B773029
theorem B1292881 : Blo 507795 1292881 := bstep (se 2 (by rfl) ⟨484830, by rfl⟩ : syracuseStep 1292881 = 969661) B969661
theorem B572035 : Blo 507795 572035 := bstep (se 1 (by rfl) ⟨429026, by rfl⟩ : syracuseStep 572035 = 858053) B858053
theorem B4668101 : Blo 507795 4668101 := bstep (se 4 (by rfl) ⟨437634, by rfl⟩ : syracuseStep 4668101 = 875269) B875269
theorem B572179 : Blo 507795 572179 := bstep (se 1 (by rfl) ⟨429134, by rfl⟩ : syracuseStep 572179 = 858269) B858269
theorem B1719089 : Blo 507795 1719089 := bstep (se 2 (by rfl) ⟨644658, by rfl⟩ : syracuseStep 1719089 = 1289317) B1289317
theorem B1293155 : Blo 507795 1293155 := bstep (se 1 (by rfl) ⟨969866, by rfl⟩ : syracuseStep 1293155 = 1939733) B1939733
theorem B572323 : Blo 507795 572323 := bstep (se 1 (by rfl) ⟨429242, by rfl⟩ : syracuseStep 572323 = 858485) B858485
theorem B8240069 : Blo 507795 8240069 := bstep (se 4 (by rfl) ⟨772506, by rfl⟩ : syracuseStep 8240069 = 1545013) B1545013
theorem B1293347 : Blo 507795 1293347 := bstep (se 1 (by rfl) ⟨970010, by rfl⟩ : syracuseStep 1293347 = 1940021) B1940021
theorem B572467 : Blo 507795 572467 := bstep (se 1 (by rfl) ⟨429350, by rfl⟩ : syracuseStep 572467 = 858701) B858701
theorem B1457261 : Blo 507795 1457261 := bstep (se 3 (by rfl) ⟨273236, by rfl⟩ : syracuseStep 1457261 = 546473) B546473
theorem B572611 : Blo 507795 572611 := bstep (se 1 (by rfl) ⟨429458, by rfl⟩ : syracuseStep 572611 = 858917) B858917
theorem B1719629 : Blo 507795 1719629 := bstep (se 3 (by rfl) ⟨322430, by rfl⟩ : syracuseStep 1719629 = 644861) B644861
theorem B572755 : Blo 507795 572755 := bstep (se 1 (by rfl) ⟨429566, by rfl⟩ : syracuseStep 572755 = 859133) B859133
theorem B966001 : Blo 507795 966001 := bstep (se 2 (by rfl) ⟨362250, by rfl⟩ : syracuseStep 966001 = 724501) B724501
theorem B1719683 : Blo 507795 1719683 := bstep (se 1 (by rfl) ⟨1289762, by rfl⟩ : syracuseStep 1719683 = 2579525) B2579525
theorem B572899 : Blo 507795 572899 := bstep (se 1 (by rfl) ⟨429674, by rfl⟩ : syracuseStep 572899 = 859349) B859349
theorem B966161 : Blo 507795 966161 := bstep (se 2 (by rfl) ⟨362310, by rfl⟩ : syracuseStep 966161 = 724621) B724621
theorem B1555985 : Blo 507795 1555985 := bstep (se 2 (by rfl) ⟨583494, by rfl⟩ : syracuseStep 1555985 = 1166989) B1166989
theorem B573043 : Blo 507795 573043 := bstep (se 1 (by rfl) ⟨429782, by rfl⟩ : syracuseStep 573043 = 859565) B859565
theorem B2899597 : Blo 507795 2899597 := bstep (se 3 (by rfl) ⟨543674, by rfl⟩ : syracuseStep 2899597 = 1087349) B1087349
theorem B1719953 : Blo 507795 1719953 := bstep (se 2 (by rfl) ⟨644982, by rfl⟩ : syracuseStep 1719953 = 1289965) B1289965
theorem B1556131 : Blo 507795 1556131 := bstep (se 1 (by rfl) ⟨1167098, by rfl⟩ : syracuseStep 1556131 = 2334197) B2334197
theorem B573187 : Blo 507795 573187 := bstep (se 1 (by rfl) ⟨429890, by rfl⟩ : syracuseStep 573187 = 859781) B859781
theorem B507795 : Blo 507795 507795 := bstep (se 1 (by rfl) ⟨380846, by rfl⟩ : syracuseStep 507795 = 761693) B761693
theorem B573331 : Blo 507795 573331 := bstep (se 1 (by rfl) ⟨429998, by rfl⟩ : syracuseStep 573331 = 859997) B859997
theorem B507811 : Blo 507795 507811 := bstep (se 1 (by rfl) ⟨380858, by rfl⟩ : syracuseStep 507811 = 761717) B761717
theorem B966563 : Blo 507795 966563 := bstep (se 1 (by rfl) ⟨724922, by rfl⟩ : syracuseStep 966563 = 1449845) B1449845
theorem B2441137 : Blo 507795 2441137 := bstep (se 2 (by rfl) ⟨915426, by rfl⟩ : syracuseStep 2441137 = 1830853) B1830853
theorem B507827 : Blo 507795 507827 := bstep (se 1 (by rfl) ⟨380870, by rfl⟩ : syracuseStep 507827 = 761741) B761741
theorem B507843 : Blo 507795 507843 := bstep (se 1 (by rfl) ⟨380882, by rfl⟩ : syracuseStep 507843 = 761765) B761765
theorem B1294289 : Blo 507795 1294289 := bstep (se 2 (by rfl) ⟨485358, by rfl⟩ : syracuseStep 1294289 = 970717) B970717
theorem B507859 : Blo 507795 507859 := bstep (se 1 (by rfl) ⟨380894, by rfl⟩ : syracuseStep 507859 = 761789) B761789
theorem B507875 : Blo 507795 507875 := bstep (se 1 (by rfl) ⟨380906, by rfl⟩ : syracuseStep 507875 = 761813) B761813
theorem B507891 : Blo 507795 507891 := bstep (se 1 (by rfl) ⟨380918, by rfl⟩ : syracuseStep 507891 = 761837) B761837
theorem B507907 : Blo 507795 507907 := bstep (se 1 (by rfl) ⟨380930, by rfl⟩ : syracuseStep 507907 = 761861) B761861
theorem B1294339 : Blo 507795 1294339 := bstep (se 1 (by rfl) ⟨970754, by rfl⟩ : syracuseStep 1294339 = 1941509) B1941509
theorem B507923 : Blo 507795 507923 := bstep (se 1 (by rfl) ⟨380942, by rfl⟩ : syracuseStep 507923 = 761885) B761885
theorem B507939 : Blo 507795 507939 := bstep (se 1 (by rfl) ⟨380954, by rfl⟩ : syracuseStep 507939 = 761909) B761909
theorem B573475 : Blo 507795 573475 := bstep (se 1 (by rfl) ⟨430106, by rfl⟩ : syracuseStep 573475 = 860213) B860213
theorem B507955 : Blo 507795 507955 := bstep (se 1 (by rfl) ⟨380966, by rfl⟩ : syracuseStep 507955 = 761933) B761933
theorem B507971 : Blo 507795 507971 := bstep (se 1 (by rfl) ⟨380978, by rfl⟩ : syracuseStep 507971 = 761957) B761957
theorem B507987 : Blo 507795 507987 := bstep (se 1 (by rfl) ⟨380990, by rfl⟩ : syracuseStep 507987 = 761981) B761981
theorem B508003 : Blo 507795 508003 := bstep (se 1 (by rfl) ⟨381002, by rfl⟩ : syracuseStep 508003 = 762005) B762005
theorem B508019 : Blo 507795 508019 := bstep (se 1 (by rfl) ⟨381014, by rfl⟩ : syracuseStep 508019 = 762029) B762029
theorem B508035 : Blo 507795 508035 := bstep (se 1 (by rfl) ⟨381026, by rfl⟩ : syracuseStep 508035 = 762053) B762053
theorem B1294481 : Blo 507795 1294481 := bstep (se 2 (by rfl) ⟨485430, by rfl⟩ : syracuseStep 1294481 = 970861) B970861
theorem B508051 : Blo 507795 508051 := bstep (se 1 (by rfl) ⟨381038, by rfl⟩ : syracuseStep 508051 = 762077) B762077
theorem B508067 : Blo 507795 508067 := bstep (se 1 (by rfl) ⟨381050, by rfl⟩ : syracuseStep 508067 = 762101) B762101
theorem B1720493 : Blo 507795 1720493 := bstep (se 3 (by rfl) ⟨322592, by rfl⟩ : syracuseStep 1720493 = 645185) B645185
theorem B508083 : Blo 507795 508083 := bstep (se 1 (by rfl) ⟨381062, by rfl⟩ : syracuseStep 508083 = 762125) B762125
theorem B573619 : Blo 507795 573619 := bstep (se 1 (by rfl) ⟨430214, by rfl⟩ : syracuseStep 573619 = 860429) B860429
theorem B508099 : Blo 507795 508099 := bstep (se 1 (by rfl) ⟨381074, by rfl⟩ : syracuseStep 508099 = 762149) B762149
theorem B508115 : Blo 507795 508115 := bstep (se 1 (by rfl) ⟨381086, by rfl⟩ : syracuseStep 508115 = 762173) B762173
theorem B508131 : Blo 507795 508131 := bstep (se 1 (by rfl) ⟨381098, by rfl⟩ : syracuseStep 508131 = 762197) B762197
theorem B1720547 : Blo 507795 1720547 := bstep (se 1 (by rfl) ⟨1290410, by rfl⟩ : syracuseStep 1720547 = 2580821) B2580821
theorem B508147 : Blo 507795 508147 := bstep (se 1 (by rfl) ⟨381110, by rfl⟩ : syracuseStep 508147 = 762221) B762221
theorem B508163 : Blo 507795 508163 := bstep (se 1 (by rfl) ⟨381122, by rfl⟩ : syracuseStep 508163 = 762245) B762245
theorem B508179 : Blo 507795 508179 := bstep (se 1 (by rfl) ⟨381134, by rfl⟩ : syracuseStep 508179 = 762269) B762269
theorem B508195 : Blo 507795 508195 := bstep (se 1 (by rfl) ⟨381146, by rfl⟩ : syracuseStep 508195 = 762293) B762293
theorem B508211 : Blo 507795 508211 := bstep (se 1 (by rfl) ⟨381158, by rfl⟩ : syracuseStep 508211 = 762317) B762317
theorem B508227 : Blo 507795 508227 := bstep (se 1 (by rfl) ⟨381170, by rfl⟩ : syracuseStep 508227 = 762341) B762341
theorem B573763 : Blo 507795 573763 := bstep (se 1 (by rfl) ⟨430322, by rfl⟩ : syracuseStep 573763 = 860645) B860645
theorem B4342085 : Blo 507795 4342085 := bstep (se 4 (by rfl) ⟨407070, by rfl⟩ : syracuseStep 4342085 = 814141) B814141
theorem B4538693 : Blo 507795 4538693 := bstep (se 4 (by rfl) ⟨425502, by rfl⟩ : syracuseStep 4538693 = 851005) B851005
theorem B508243 : Blo 507795 508243 := bstep (se 1 (by rfl) ⟨381182, by rfl⟩ : syracuseStep 508243 = 762365) B762365
theorem B508259 : Blo 507795 508259 := bstep (se 1 (by rfl) ⟨381194, by rfl⟩ : syracuseStep 508259 = 762389) B762389
theorem B508275 : Blo 507795 508275 := bstep (se 1 (by rfl) ⟨381206, by rfl⟩ : syracuseStep 508275 = 762413) B762413
theorem B508291 : Blo 507795 508291 := bstep (se 1 (by rfl) ⟨381218, by rfl⟩ : syracuseStep 508291 = 762437) B762437
theorem B508307 : Blo 507795 508307 := bstep (se 1 (by rfl) ⟨381230, by rfl⟩ : syracuseStep 508307 = 762461) B762461
theorem B508323 : Blo 507795 508323 := bstep (se 1 (by rfl) ⟨381242, by rfl⟩ : syracuseStep 508323 = 762485) B762485
theorem B2572721 : Blo 507795 2572721 := bstep (se 2 (by rfl) ⟨964770, by rfl⟩ : syracuseStep 2572721 = 1929541) B1929541
theorem B508339 : Blo 507795 508339 := bstep (se 1 (by rfl) ⟨381254, by rfl⟩ : syracuseStep 508339 = 762509) B762509
theorem B508355 : Blo 507795 508355 := bstep (se 1 (by rfl) ⟨381266, by rfl⟩ : syracuseStep 508355 = 762533) B762533
theorem B508371 : Blo 507795 508371 := bstep (se 1 (by rfl) ⟨381278, by rfl⟩ : syracuseStep 508371 = 762557) B762557
theorem B573907 : Blo 507795 573907 := bstep (se 1 (by rfl) ⟨430430, by rfl⟩ : syracuseStep 573907 = 860861) B860861
theorem B508387 : Blo 507795 508387 := bstep (se 1 (by rfl) ⟨381290, by rfl⟩ : syracuseStep 508387 = 762581) B762581
theorem B1720817 : Blo 507795 1720817 := bstep (se 2 (by rfl) ⟨645306, by rfl⟩ : syracuseStep 1720817 = 1290613) B1290613
theorem B508403 : Blo 507795 508403 := bstep (se 1 (by rfl) ⟨381302, by rfl⟩ : syracuseStep 508403 = 762605) B762605
theorem B508419 : Blo 507795 508419 := bstep (se 1 (by rfl) ⟨381314, by rfl⟩ : syracuseStep 508419 = 762629) B762629
theorem B508435 : Blo 507795 508435 := bstep (se 1 (by rfl) ⟨381326, by rfl⟩ : syracuseStep 508435 = 762653) B762653
theorem B508451 : Blo 507795 508451 := bstep (se 1 (by rfl) ⟨381338, by rfl⟩ : syracuseStep 508451 = 762677) B762677
theorem B2179619 : Blo 507795 2179619 := bstep (se 1 (by rfl) ⟨1634714, by rfl⟩ : syracuseStep 2179619 = 3269429) B3269429
theorem B508467 : Blo 507795 508467 := bstep (se 1 (by rfl) ⟨381350, by rfl⟩ : syracuseStep 508467 = 762701) B762701
theorem B508483 : Blo 507795 508483 := bstep (se 1 (by rfl) ⟨381362, by rfl⟩ : syracuseStep 508483 = 762725) B762725
theorem B508499 : Blo 507795 508499 := bstep (se 1 (by rfl) ⟨381374, by rfl⟩ : syracuseStep 508499 = 762749) B762749
theorem B508515 : Blo 507795 508515 := bstep (se 1 (by rfl) ⟨381386, by rfl⟩ : syracuseStep 508515 = 762773) B762773
theorem B574051 : Blo 507795 574051 := bstep (se 1 (by rfl) ⟨430538, by rfl⟩ : syracuseStep 574051 = 861077) B861077
theorem B508531 : Blo 507795 508531 := bstep (se 1 (by rfl) ⟨381398, by rfl⟩ : syracuseStep 508531 = 762797) B762797
theorem B508547 : Blo 507795 508547 := bstep (se 1 (by rfl) ⟨381410, by rfl⟩ : syracuseStep 508547 = 762821) B762821
theorem B508563 : Blo 507795 508563 := bstep (se 1 (by rfl) ⟨381422, by rfl⟩ : syracuseStep 508563 = 762845) B762845
theorem B508579 : Blo 507795 508579 := bstep (se 1 (by rfl) ⟨381434, by rfl⟩ : syracuseStep 508579 = 762869) B762869
theorem B508595 : Blo 507795 508595 := bstep (se 1 (by rfl) ⟨381446, by rfl⟩ : syracuseStep 508595 = 762893) B762893
theorem B508611 : Blo 507795 508611 := bstep (se 1 (by rfl) ⟨381458, by rfl⟩ : syracuseStep 508611 = 762917) B762917
theorem B508627 : Blo 507795 508627 := bstep (se 1 (by rfl) ⟨381470, by rfl⟩ : syracuseStep 508627 = 762941) B762941
theorem B508643 : Blo 507795 508643 := bstep (se 1 (by rfl) ⟨381482, by rfl⟩ : syracuseStep 508643 = 762965) B762965
theorem B508659 : Blo 507795 508659 := bstep (se 1 (by rfl) ⟨381494, by rfl⟩ : syracuseStep 508659 = 762989) B762989
theorem B574195 : Blo 507795 574195 := bstep (se 1 (by rfl) ⟨430646, by rfl⟩ : syracuseStep 574195 = 861293) B861293
theorem B508675 : Blo 507795 508675 := bstep (se 1 (by rfl) ⟨381506, by rfl⟩ : syracuseStep 508675 = 763013) B763013
theorem B508691 : Blo 507795 508691 := bstep (se 1 (by rfl) ⟨381518, by rfl⟩ : syracuseStep 508691 = 763037) B763037
theorem B508707 : Blo 507795 508707 := bstep (se 1 (by rfl) ⟨381530, by rfl⟩ : syracuseStep 508707 = 763061) B763061
theorem B967459 : Blo 507795 967459 := bstep (se 1 (by rfl) ⟨725594, by rfl⟩ : syracuseStep 967459 = 1451189) B1451189
theorem B508723 : Blo 507795 508723 := bstep (se 1 (by rfl) ⟨381542, by rfl⟩ : syracuseStep 508723 = 763085) B763085
theorem B508739 : Blo 507795 508739 := bstep (se 1 (by rfl) ⟨381554, by rfl⟩ : syracuseStep 508739 = 763109) B763109
theorem B508755 : Blo 507795 508755 := bstep (se 1 (by rfl) ⟨381566, by rfl⟩ : syracuseStep 508755 = 763133) B763133
theorem B508771 : Blo 507795 508771 := bstep (se 1 (by rfl) ⟨381578, by rfl⟩ : syracuseStep 508771 = 763157) B763157
theorem B508787 : Blo 507795 508787 := bstep (se 1 (by rfl) ⟨381590, by rfl⟩ : syracuseStep 508787 = 763181) B763181
theorem B508803 : Blo 507795 508803 := bstep (se 1 (by rfl) ⟨381602, by rfl⟩ : syracuseStep 508803 = 763205) B763205
theorem B574339 : Blo 507795 574339 := bstep (se 1 (by rfl) ⟨430754, by rfl⟩ : syracuseStep 574339 = 861509) B861509
theorem B508819 : Blo 507795 508819 := bstep (se 1 (by rfl) ⟨381614, by rfl⟩ : syracuseStep 508819 = 763229) B763229
theorem B508835 : Blo 507795 508835 := bstep (se 1 (by rfl) ⟨381626, by rfl⟩ : syracuseStep 508835 = 763253) B763253
theorem B508851 : Blo 507795 508851 := bstep (se 1 (by rfl) ⟨381638, by rfl⟩ : syracuseStep 508851 = 763277) B763277
theorem B508867 : Blo 507795 508867 := bstep (se 1 (by rfl) ⟨381650, by rfl⟩ : syracuseStep 508867 = 763301) B763301
theorem B967619 : Blo 507795 967619 := bstep (se 1 (by rfl) ⟨725714, by rfl⟩ : syracuseStep 967619 = 1451429) B1451429
theorem B508883 : Blo 507795 508883 := bstep (se 1 (by rfl) ⟨381662, by rfl⟩ : syracuseStep 508883 = 763325) B763325
theorem B508899 : Blo 507795 508899 := bstep (se 1 (by rfl) ⟨381674, by rfl⟩ : syracuseStep 508899 = 763349) B763349
theorem B1328113 : Blo 507795 1328113 := bstep (se 2 (by rfl) ⟨498042, by rfl⟩ : syracuseStep 1328113 = 996085) B996085
theorem B508915 : Blo 507795 508915 := bstep (se 1 (by rfl) ⟨381686, by rfl⟩ : syracuseStep 508915 = 763373) B763373
theorem B508931 : Blo 507795 508931 := bstep (se 1 (by rfl) ⟨381698, by rfl⟩ : syracuseStep 508931 = 763397) B763397
theorem B1721357 : Blo 507795 1721357 := bstep (se 3 (by rfl) ⟨322754, by rfl⟩ : syracuseStep 1721357 = 645509) B645509
theorem B508947 : Blo 507795 508947 := bstep (se 1 (by rfl) ⟨381710, by rfl⟩ : syracuseStep 508947 = 763421) B763421
theorem B574483 : Blo 507795 574483 := bstep (se 1 (by rfl) ⟨430862, by rfl⟩ : syracuseStep 574483 = 861725) B861725
theorem B508963 : Blo 507795 508963 := bstep (se 1 (by rfl) ⟨381722, by rfl⟩ : syracuseStep 508963 = 763445) B763445
theorem B508979 : Blo 507795 508979 := bstep (se 1 (by rfl) ⟨381734, by rfl⟩ : syracuseStep 508979 = 763469) B763469
theorem B508995 : Blo 507795 508995 := bstep (se 1 (by rfl) ⟨381746, by rfl⟩ : syracuseStep 508995 = 763493) B763493
theorem B1721411 : Blo 507795 1721411 := bstep (se 1 (by rfl) ⟨1291058, by rfl⟩ : syracuseStep 1721411 = 2582117) B2582117
theorem B509011 : Blo 507795 509011 := bstep (se 1 (by rfl) ⟨381758, by rfl⟩ : syracuseStep 509011 = 763517) B763517
theorem B509027 : Blo 507795 509027 := bstep (se 1 (by rfl) ⟨381770, by rfl⟩ : syracuseStep 509027 = 763541) B763541
theorem B1295473 : Blo 507795 1295473 := bstep (se 2 (by rfl) ⟨485802, by rfl⟩ : syracuseStep 1295473 = 971605) B971605
theorem B509043 : Blo 507795 509043 := bstep (se 1 (by rfl) ⟨381782, by rfl⟩ : syracuseStep 509043 = 763565) B763565
theorem B509059 : Blo 507795 509059 := bstep (se 1 (by rfl) ⟨381794, by rfl⟩ : syracuseStep 509059 = 763589) B763589
theorem B6210701 : Blo 507795 6210701 := bstep (se 3 (by rfl) ⟨1164506, by rfl⟩ : syracuseStep 6210701 = 2329013) B2329013
theorem B509075 : Blo 507795 509075 := bstep (se 1 (by rfl) ⟨381806, by rfl⟩ : syracuseStep 509075 = 763613) B763613
theorem B509091 : Blo 507795 509091 := bstep (se 1 (by rfl) ⟨381818, by rfl⟩ : syracuseStep 509091 = 763637) B763637
theorem B574627 : Blo 507795 574627 := bstep (se 1 (by rfl) ⟨430970, by rfl⟩ : syracuseStep 574627 = 861941) B861941
theorem B509107 : Blo 507795 509107 := bstep (se 1 (by rfl) ⟨381830, by rfl⟩ : syracuseStep 509107 = 763661) B763661
theorem B509123 : Blo 507795 509123 := bstep (se 1 (by rfl) ⟨381842, by rfl⟩ : syracuseStep 509123 = 763685) B763685
theorem B3261637 : Blo 507795 3261637 := bstep (se 4 (by rfl) ⟨305778, by rfl⟩ : syracuseStep 3261637 = 611557) B611557
theorem B509139 : Blo 507795 509139 := bstep (se 1 (by rfl) ⟨381854, by rfl⟩ : syracuseStep 509139 = 763709) B763709
theorem B509155 : Blo 507795 509155 := bstep (se 1 (by rfl) ⟨381866, by rfl⟩ : syracuseStep 509155 = 763733) B763733
theorem B509171 : Blo 507795 509171 := bstep (se 1 (by rfl) ⟨381878, by rfl⟩ : syracuseStep 509171 = 763757) B763757
theorem B509187 : Blo 507795 509187 := bstep (se 1 (by rfl) ⟨381890, by rfl⟩ : syracuseStep 509187 = 763781) B763781
theorem B1033489 : Blo 507795 1033489 := bstep (se 2 (by rfl) ⟨387558, by rfl⟩ : syracuseStep 1033489 = 775117) B775117
theorem B509203 : Blo 507795 509203 := bstep (se 1 (by rfl) ⟨381902, by rfl⟩ : syracuseStep 509203 = 763805) B763805
theorem B509219 : Blo 507795 509219 := bstep (se 1 (by rfl) ⟨381914, by rfl⟩ : syracuseStep 509219 = 763829) B763829
theorem B509235 : Blo 507795 509235 := bstep (se 1 (by rfl) ⟨381926, by rfl⟩ : syracuseStep 509235 = 763853) B763853
theorem B574771 : Blo 507795 574771 := bstep (se 1 (by rfl) ⟨431078, by rfl⟩ : syracuseStep 574771 = 862157) B862157
theorem B509251 : Blo 507795 509251 := bstep (se 1 (by rfl) ⟨381938, by rfl⟩ : syracuseStep 509251 = 763877) B763877
theorem B1721681 : Blo 507795 1721681 := bstep (se 2 (by rfl) ⟨645630, by rfl⟩ : syracuseStep 1721681 = 1291261) B1291261
theorem B509267 : Blo 507795 509267 := bstep (se 1 (by rfl) ⟨381950, by rfl⟩ : syracuseStep 509267 = 763901) B763901
theorem B509283 : Blo 507795 509283 := bstep (se 1 (by rfl) ⟨381962, by rfl⟩ : syracuseStep 509283 = 763925) B763925
theorem B509299 : Blo 507795 509299 := bstep (se 1 (by rfl) ⟨381974, by rfl⟩ : syracuseStep 509299 = 763949) B763949
theorem B509315 : Blo 507795 509315 := bstep (se 1 (by rfl) ⟨381986, by rfl⟩ : syracuseStep 509315 = 763973) B763973
theorem B509331 : Blo 507795 509331 := bstep (se 1 (by rfl) ⟨381998, by rfl⟩ : syracuseStep 509331 = 763997) B763997
theorem B509347 : Blo 507795 509347 := bstep (se 1 (by rfl) ⟨382010, by rfl⟩ : syracuseStep 509347 = 764021) B764021
theorem B509363 : Blo 507795 509363 := bstep (se 1 (by rfl) ⟨382022, by rfl⟩ : syracuseStep 509363 = 764045) B764045
theorem B574915 : Blo 507795 574915 := bstep (se 1 (by rfl) ⟨431186, by rfl⟩ : syracuseStep 574915 = 862373) B862373
theorem B509379 : Blo 507795 509379 := bstep (se 1 (by rfl) ⟨382034, by rfl⟩ : syracuseStep 509379 = 764069) B764069
theorem B509395 : Blo 507795 509395 := bstep (se 1 (by rfl) ⟨382046, by rfl⟩ : syracuseStep 509395 = 764093) B764093
theorem B509411 : Blo 507795 509411 := bstep (se 1 (by rfl) ⟨382058, by rfl⟩ : syracuseStep 509411 = 764117) B764117
theorem B509427 : Blo 507795 509427 := bstep (se 1 (by rfl) ⟨382070, by rfl⟩ : syracuseStep 509427 = 764141) B764141
theorem B509443 : Blo 507795 509443 := bstep (se 1 (by rfl) ⟨382082, by rfl⟩ : syracuseStep 509443 = 764165) B764165
theorem B509459 : Blo 507795 509459 := bstep (se 1 (by rfl) ⟨382094, by rfl⟩ : syracuseStep 509459 = 764189) B764189
theorem B509475 : Blo 507795 509475 := bstep (se 1 (by rfl) ⟨382106, by rfl⟩ : syracuseStep 509475 = 764213) B764213
theorem B509491 : Blo 507795 509491 := bstep (se 1 (by rfl) ⟨382118, by rfl⟩ : syracuseStep 509491 = 764237) B764237
theorem B509507 : Blo 507795 509507 := bstep (se 1 (by rfl) ⟨382130, by rfl⟩ : syracuseStep 509507 = 764261) B764261
theorem B2901581 : Blo 507795 2901581 := bstep (se 3 (by rfl) ⟨544046, by rfl⟩ : syracuseStep 2901581 = 1088093) B1088093
theorem B509523 : Blo 507795 509523 := bstep (se 1 (by rfl) ⟨382142, by rfl⟩ : syracuseStep 509523 = 764285) B764285
theorem B575059 : Blo 507795 575059 := bstep (se 1 (by rfl) ⟨431294, by rfl⟩ : syracuseStep 575059 = 862589) B862589
theorem B869987 : Blo 507795 869987 := bstep (se 1 (by rfl) ⟨652490, by rfl⟩ : syracuseStep 869987 = 1304981) B1304981
theorem B509539 : Blo 507795 509539 := bstep (se 1 (by rfl) ⟨382154, by rfl⟩ : syracuseStep 509539 = 764309) B764309
theorem B509555 : Blo 507795 509555 := bstep (se 1 (by rfl) ⟨382166, by rfl⟩ : syracuseStep 509555 = 764333) B764333
theorem B509571 : Blo 507795 509571 := bstep (se 1 (by rfl) ⟨382178, by rfl⟩ : syracuseStep 509571 = 764357) B764357
theorem B509587 : Blo 507795 509587 := bstep (se 1 (by rfl) ⟨382190, by rfl⟩ : syracuseStep 509587 = 764381) B764381
theorem B509603 : Blo 507795 509603 := bstep (se 1 (by rfl) ⟨382202, by rfl⟩ : syracuseStep 509603 = 764405) B764405
theorem B509619 : Blo 507795 509619 := bstep (se 1 (by rfl) ⟨382214, by rfl⟩ : syracuseStep 509619 = 764429) B764429
theorem B509635 : Blo 507795 509635 := bstep (se 1 (by rfl) ⟨382226, by rfl⟩ : syracuseStep 509635 = 764453) B764453
theorem B509651 : Blo 507795 509651 := bstep (se 1 (by rfl) ⟨382238, by rfl⟩ : syracuseStep 509651 = 764477) B764477
theorem B509667 : Blo 507795 509667 := bstep (se 1 (by rfl) ⟨382250, by rfl⟩ : syracuseStep 509667 = 764501) B764501
theorem B575203 : Blo 507795 575203 := bstep (se 1 (by rfl) ⟨431402, by rfl⟩ : syracuseStep 575203 = 862805) B862805
theorem B509683 : Blo 507795 509683 := bstep (se 1 (by rfl) ⟨382262, by rfl⟩ : syracuseStep 509683 = 764525) B764525
theorem B509699 : Blo 507795 509699 := bstep (se 1 (by rfl) ⟨382274, by rfl⟩ : syracuseStep 509699 = 764549) B764549
theorem B509715 : Blo 507795 509715 := bstep (se 1 (by rfl) ⟨382286, by rfl⟩ : syracuseStep 509715 = 764573) B764573
theorem B509731 : Blo 507795 509731 := bstep (se 1 (by rfl) ⟨382298, by rfl⟩ : syracuseStep 509731 = 764597) B764597
theorem B509747 : Blo 507795 509747 := bstep (se 1 (by rfl) ⟨382310, by rfl⟩ : syracuseStep 509747 = 764621) B764621
theorem B509763 : Blo 507795 509763 := bstep (se 1 (by rfl) ⟨382322, by rfl⟩ : syracuseStep 509763 = 764645) B764645
theorem B509779 : Blo 507795 509779 := bstep (se 1 (by rfl) ⟨382334, by rfl⟩ : syracuseStep 509779 = 764669) B764669
theorem B2574179 : Blo 507795 2574179 := bstep (se 1 (by rfl) ⟨1930634, by rfl⟩ : syracuseStep 2574179 = 3861269) B3861269
theorem B509795 : Blo 507795 509795 := bstep (se 1 (by rfl) ⟨382346, by rfl⟩ : syracuseStep 509795 = 764693) B764693
theorem B1722221 : Blo 507795 1722221 := bstep (se 3 (by rfl) ⟨322916, by rfl⟩ : syracuseStep 1722221 = 645833) B645833
theorem B509811 : Blo 507795 509811 := bstep (se 1 (by rfl) ⟨382358, by rfl⟩ : syracuseStep 509811 = 764717) B764717
theorem B575347 : Blo 507795 575347 := bstep (se 1 (by rfl) ⟨431510, by rfl⟩ : syracuseStep 575347 = 863021) B863021
theorem B509827 : Blo 507795 509827 := bstep (se 1 (by rfl) ⟨382370, by rfl⟩ : syracuseStep 509827 = 764741) B764741
theorem B509843 : Blo 507795 509843 := bstep (se 1 (by rfl) ⟨382382, by rfl⟩ : syracuseStep 509843 = 764765) B764765
theorem B509859 : Blo 507795 509859 := bstep (se 1 (by rfl) ⟨382394, by rfl⟩ : syracuseStep 509859 = 764789) B764789
theorem B1722275 : Blo 507795 1722275 := bstep (se 1 (by rfl) ⟨1291706, by rfl⟩ : syracuseStep 1722275 = 2583413) B2583413
theorem B509875 : Blo 507795 509875 := bstep (se 1 (by rfl) ⟨382406, by rfl⟩ : syracuseStep 509875 = 764813) B764813
theorem B509891 : Blo 507795 509891 := bstep (se 1 (by rfl) ⟨382418, by rfl⟩ : syracuseStep 509891 = 764837) B764837
theorem B509907 : Blo 507795 509907 := bstep (se 1 (by rfl) ⟨382430, by rfl⟩ : syracuseStep 509907 = 764861) B764861
theorem B509923 : Blo 507795 509923 := bstep (se 1 (by rfl) ⟨382442, by rfl⟩ : syracuseStep 509923 = 764885) B764885
theorem B968689 : Blo 507795 968689 := bstep (se 2 (by rfl) ⟨363258, by rfl⟩ : syracuseStep 968689 = 726517) B726517
theorem B509939 : Blo 507795 509939 := bstep (se 1 (by rfl) ⟨382454, by rfl⟩ : syracuseStep 509939 = 764909) B764909
theorem B509955 : Blo 507795 509955 := bstep (se 1 (by rfl) ⟨382466, by rfl⟩ : syracuseStep 509955 = 764933) B764933
theorem B575491 : Blo 507795 575491 := bstep (se 1 (by rfl) ⟨431618, by rfl⟩ : syracuseStep 575491 = 863237) B863237
theorem B4147213 : Blo 507795 4147213 := bstep (se 3 (by rfl) ⟨777602, by rfl⟩ : syracuseStep 4147213 = 1555205) B1555205
theorem B509971 : Blo 507795 509971 := bstep (se 1 (by rfl) ⟨382478, by rfl⟩ : syracuseStep 509971 = 764957) B764957
theorem B509987 : Blo 507795 509987 := bstep (se 1 (by rfl) ⟨382490, by rfl⟩ : syracuseStep 509987 = 764981) B764981
theorem B510003 : Blo 507795 510003 := bstep (se 1 (by rfl) ⟨382502, by rfl⟩ : syracuseStep 510003 = 765005) B765005
theorem B510019 : Blo 507795 510019 := bstep (se 1 (by rfl) ⟨382514, by rfl⟩ : syracuseStep 510019 = 765029) B765029
theorem B510035 : Blo 507795 510035 := bstep (se 1 (by rfl) ⟨382526, by rfl⟩ : syracuseStep 510035 = 765053) B765053
theorem B510051 : Blo 507795 510051 := bstep (se 1 (by rfl) ⟨382538, by rfl⟩ : syracuseStep 510051 = 765077) B765077
theorem B510067 : Blo 507795 510067 := bstep (se 1 (by rfl) ⟨382550, by rfl⟩ : syracuseStep 510067 = 765101) B765101
theorem B510083 : Blo 507795 510083 := bstep (se 1 (by rfl) ⟨382562, by rfl⟩ : syracuseStep 510083 = 765125) B765125
theorem B510099 : Blo 507795 510099 := bstep (se 1 (by rfl) ⟨382574, by rfl⟩ : syracuseStep 510099 = 765149) B765149
theorem B575635 : Blo 507795 575635 := bstep (se 1 (by rfl) ⟨431726, by rfl⟩ : syracuseStep 575635 = 863453) B863453
theorem B510115 : Blo 507795 510115 := bstep (se 1 (by rfl) ⟨382586, by rfl⟩ : syracuseStep 510115 = 765173) B765173
theorem B1722545 : Blo 507795 1722545 := bstep (se 2 (by rfl) ⟨645954, by rfl⟩ : syracuseStep 1722545 = 1291909) B1291909
theorem B510131 : Blo 507795 510131 := bstep (se 1 (by rfl) ⟨382598, by rfl⟩ : syracuseStep 510131 = 765197) B765197
theorem B510147 : Blo 507795 510147 := bstep (se 1 (by rfl) ⟨382610, by rfl⟩ : syracuseStep 510147 = 765221) B765221
theorem B510163 : Blo 507795 510163 := bstep (se 1 (by rfl) ⟨382622, by rfl⟩ : syracuseStep 510163 = 765245) B765245
theorem B510179 : Blo 507795 510179 := bstep (se 1 (by rfl) ⟨382634, by rfl⟩ : syracuseStep 510179 = 765269) B765269
theorem B510195 : Blo 507795 510195 := bstep (se 1 (by rfl) ⟨382646, by rfl⟩ : syracuseStep 510195 = 765293) B765293
theorem B510211 : Blo 507795 510211 := bstep (se 1 (by rfl) ⟨382658, by rfl⟩ : syracuseStep 510211 = 765317) B765317
theorem B510227 : Blo 507795 510227 := bstep (se 1 (by rfl) ⟨382670, by rfl⟩ : syracuseStep 510227 = 765341) B765341
theorem B510243 : Blo 507795 510243 := bstep (se 1 (by rfl) ⟨382682, by rfl⟩ : syracuseStep 510243 = 765365) B765365
theorem B510259 : Blo 507795 510259 := bstep (se 1 (by rfl) ⟨382694, by rfl⟩ : syracuseStep 510259 = 765389) B765389
theorem B510275 : Blo 507795 510275 := bstep (se 1 (by rfl) ⟨382706, by rfl⟩ : syracuseStep 510275 = 765413) B765413
theorem B510291 : Blo 507795 510291 := bstep (se 1 (by rfl) ⟨382718, by rfl⟩ : syracuseStep 510291 = 765437) B765437
theorem B510307 : Blo 507795 510307 := bstep (se 1 (by rfl) ⟨382730, by rfl⟩ : syracuseStep 510307 = 765461) B765461
theorem B510323 : Blo 507795 510323 := bstep (se 1 (by rfl) ⟨382742, by rfl⟩ : syracuseStep 510323 = 765485) B765485
theorem B510339 : Blo 507795 510339 := bstep (se 1 (by rfl) ⟨382754, by rfl⟩ : syracuseStep 510339 = 765509) B765509
theorem B510355 : Blo 507795 510355 := bstep (se 1 (by rfl) ⟨382766, by rfl⟩ : syracuseStep 510355 = 765533) B765533
theorem B510371 : Blo 507795 510371 := bstep (se 1 (by rfl) ⟨382778, by rfl⟩ : syracuseStep 510371 = 765557) B765557
theorem B510387 : Blo 507795 510387 := bstep (se 1 (by rfl) ⟨382790, by rfl⟩ : syracuseStep 510387 = 765581) B765581
theorem B510403 : Blo 507795 510403 := bstep (se 1 (by rfl) ⟨382802, by rfl⟩ : syracuseStep 510403 = 765605) B765605
theorem B510419 : Blo 507795 510419 := bstep (se 1 (by rfl) ⟨382814, by rfl⟩ : syracuseStep 510419 = 765629) B765629
theorem B510435 : Blo 507795 510435 := bstep (se 1 (by rfl) ⟨382826, by rfl⟩ : syracuseStep 510435 = 765653) B765653
theorem B2902513 : Blo 507795 2902513 := bstep (se 2 (by rfl) ⟨1088442, by rfl⟩ : syracuseStep 2902513 = 2176885) B2176885
theorem B510451 : Blo 507795 510451 := bstep (se 1 (by rfl) ⟨382838, by rfl⟩ : syracuseStep 510451 = 765677) B765677
theorem B510467 : Blo 507795 510467 := bstep (se 1 (by rfl) ⟨382850, by rfl⟩ : syracuseStep 510467 = 765701) B765701
theorem B510483 : Blo 507795 510483 := bstep (se 1 (by rfl) ⟨382862, by rfl⟩ : syracuseStep 510483 = 765725) B765725
theorem B510499 : Blo 507795 510499 := bstep (se 1 (by rfl) ⟨382874, by rfl⟩ : syracuseStep 510499 = 765749) B765749
theorem B510515 : Blo 507795 510515 := bstep (se 1 (by rfl) ⟨382886, by rfl⟩ : syracuseStep 510515 = 765773) B765773
theorem B510531 : Blo 507795 510531 := bstep (se 1 (by rfl) ⟨382898, by rfl⟩ : syracuseStep 510531 = 765797) B765797
theorem B510547 : Blo 507795 510547 := bstep (se 1 (by rfl) ⟨382910, by rfl⟩ : syracuseStep 510547 = 765821) B765821
theorem B510563 : Blo 507795 510563 := bstep (se 1 (by rfl) ⟨382922, by rfl⟩ : syracuseStep 510563 = 765845) B765845
theorem B510579 : Blo 507795 510579 := bstep (se 1 (by rfl) ⟨382934, by rfl⟩ : syracuseStep 510579 = 765869) B765869
theorem B510595 : Blo 507795 510595 := bstep (se 1 (by rfl) ⟨382946, by rfl⟩ : syracuseStep 510595 = 765893) B765893
theorem B2574989 : Blo 507795 2574989 := bstep (se 3 (by rfl) ⟨482810, by rfl⟩ : syracuseStep 2574989 = 965621) B965621
theorem B510611 : Blo 507795 510611 := bstep (se 1 (by rfl) ⟨382958, by rfl⟩ : syracuseStep 510611 = 765917) B765917
theorem B510627 : Blo 507795 510627 := bstep (se 1 (by rfl) ⟨382970, by rfl⟩ : syracuseStep 510627 = 765941) B765941
theorem B510643 : Blo 507795 510643 := bstep (se 1 (by rfl) ⟨382982, by rfl⟩ : syracuseStep 510643 = 765965) B765965
theorem B510659 : Blo 507795 510659 := bstep (se 1 (by rfl) ⟨382994, by rfl⟩ : syracuseStep 510659 = 765989) B765989
theorem B1723085 : Blo 507795 1723085 := bstep (se 3 (by rfl) ⟨323078, by rfl⟩ : syracuseStep 1723085 = 646157) B646157
theorem B510675 : Blo 507795 510675 := bstep (se 1 (by rfl) ⟨383006, by rfl⟩ : syracuseStep 510675 = 766013) B766013
theorem B510691 : Blo 507795 510691 := bstep (se 1 (by rfl) ⟨383018, by rfl⟩ : syracuseStep 510691 = 766037) B766037
theorem B510707 : Blo 507795 510707 := bstep (se 1 (by rfl) ⟨383030, by rfl⟩ : syracuseStep 510707 = 766061) B766061
theorem B1723139 : Blo 507795 1723139 := bstep (se 1 (by rfl) ⟨1292354, by rfl⟩ : syracuseStep 1723139 = 2584709) B2584709
theorem B510723 : Blo 507795 510723 := bstep (se 1 (by rfl) ⟨383042, by rfl⟩ : syracuseStep 510723 = 766085) B766085
theorem B510739 : Blo 507795 510739 := bstep (se 1 (by rfl) ⟨383054, by rfl⟩ : syracuseStep 510739 = 766109) B766109
theorem B510755 : Blo 507795 510755 := bstep (se 1 (by rfl) ⟨383066, by rfl⟩ : syracuseStep 510755 = 766133) B766133
theorem B510771 : Blo 507795 510771 := bstep (se 1 (by rfl) ⟨383078, by rfl⟩ : syracuseStep 510771 = 766157) B766157
theorem B510787 : Blo 507795 510787 := bstep (se 1 (by rfl) ⟨383090, by rfl⟩ : syracuseStep 510787 = 766181) B766181
theorem B510803 : Blo 507795 510803 := bstep (se 1 (by rfl) ⟨383102, by rfl⟩ : syracuseStep 510803 = 766205) B766205
theorem B510819 : Blo 507795 510819 := bstep (se 1 (by rfl) ⟨383114, by rfl⟩ : syracuseStep 510819 = 766229) B766229
theorem B510835 : Blo 507795 510835 := bstep (se 1 (by rfl) ⟨383126, by rfl⟩ : syracuseStep 510835 = 766253) B766253
theorem B510851 : Blo 507795 510851 := bstep (se 1 (by rfl) ⟨383138, by rfl⟩ : syracuseStep 510851 = 766277) B766277
theorem B510867 : Blo 507795 510867 := bstep (se 1 (by rfl) ⟨383150, by rfl⟩ : syracuseStep 510867 = 766301) B766301
theorem B510883 : Blo 507795 510883 := bstep (se 1 (by rfl) ⟨383162, by rfl⟩ : syracuseStep 510883 = 766325) B766325
theorem B510899 : Blo 507795 510899 := bstep (se 1 (by rfl) ⟨383174, by rfl⟩ : syracuseStep 510899 = 766349) B766349
theorem B510915 : Blo 507795 510915 := bstep (se 1 (by rfl) ⟨383186, by rfl⟩ : syracuseStep 510915 = 766373) B766373
theorem B510931 : Blo 507795 510931 := bstep (se 1 (by rfl) ⟨383198, by rfl⟩ : syracuseStep 510931 = 766397) B766397
theorem B510947 : Blo 507795 510947 := bstep (se 1 (by rfl) ⟨383210, by rfl⟩ : syracuseStep 510947 = 766421) B766421
theorem B510963 : Blo 507795 510963 := bstep (se 1 (by rfl) ⟨383222, by rfl⟩ : syracuseStep 510963 = 766445) B766445
theorem B510979 : Blo 507795 510979 := bstep (se 1 (by rfl) ⟨383234, by rfl⟩ : syracuseStep 510979 = 766469) B766469
theorem B1723409 : Blo 507795 1723409 := bstep (se 2 (by rfl) ⟨646278, by rfl⟩ : syracuseStep 1723409 = 1292557) B1292557
theorem B1035281 : Blo 507795 1035281 := bstep (se 2 (by rfl) ⟨388230, by rfl⟩ : syracuseStep 1035281 = 776461) B776461
theorem B969745 : Blo 507795 969745 := bstep (se 2 (by rfl) ⟨363654, by rfl⟩ : syracuseStep 969745 = 727309) B727309
theorem B510995 : Blo 507795 510995 := bstep (se 1 (by rfl) ⟨383246, by rfl⟩ : syracuseStep 510995 = 766493) B766493
theorem B511011 : Blo 507795 511011 := bstep (se 1 (by rfl) ⟨383258, by rfl⟩ : syracuseStep 511011 = 766517) B766517
theorem B511027 : Blo 507795 511027 := bstep (se 1 (by rfl) ⟨383270, by rfl⟩ : syracuseStep 511027 = 766541) B766541
theorem B511043 : Blo 507795 511043 := bstep (se 1 (by rfl) ⟨383282, by rfl⟩ : syracuseStep 511043 = 766565) B766565
theorem B4901957 : Blo 507795 4901957 := bstep (se 4 (by rfl) ⟨459558, by rfl⟩ : syracuseStep 4901957 = 919117) B919117
theorem B511059 : Blo 507795 511059 := bstep (se 1 (by rfl) ⟨383294, by rfl⟩ : syracuseStep 511059 = 766589) B766589
theorem B511075 : Blo 507795 511075 := bstep (se 1 (by rfl) ⟨383306, by rfl⟩ : syracuseStep 511075 = 766613) B766613
theorem B511091 : Blo 507795 511091 := bstep (se 1 (by rfl) ⟨383318, by rfl⟩ : syracuseStep 511091 = 766637) B766637
theorem B511107 : Blo 507795 511107 := bstep (se 1 (by rfl) ⟨383330, by rfl⟩ : syracuseStep 511107 = 766661) B766661
theorem B773267 : Blo 507795 773267 := bstep (se 1 (by rfl) ⟨579950, by rfl⟩ : syracuseStep 773267 = 1159901) B1159901
theorem B511123 : Blo 507795 511123 := bstep (se 1 (by rfl) ⟨383342, by rfl⟩ : syracuseStep 511123 = 766685) B766685
theorem B511139 : Blo 507795 511139 := bstep (se 1 (by rfl) ⟨383354, by rfl⟩ : syracuseStep 511139 = 766709) B766709
theorem B511155 : Blo 507795 511155 := bstep (se 1 (by rfl) ⟨383366, by rfl⟩ : syracuseStep 511155 = 766733) B766733
theorem B511171 : Blo 507795 511171 := bstep (se 1 (by rfl) ⟨383378, by rfl⟩ : syracuseStep 511171 = 766757) B766757
theorem B511187 : Blo 507795 511187 := bstep (se 1 (by rfl) ⟨383390, by rfl⟩ : syracuseStep 511187 = 766781) B766781
theorem B511203 : Blo 507795 511203 := bstep (se 1 (by rfl) ⟨383402, by rfl⟩ : syracuseStep 511203 = 766805) B766805
theorem B511219 : Blo 507795 511219 := bstep (se 1 (by rfl) ⟨383414, by rfl⟩ : syracuseStep 511219 = 766829) B766829
theorem B511235 : Blo 507795 511235 := bstep (se 1 (by rfl) ⟨383426, by rfl⟩ : syracuseStep 511235 = 766853) B766853
theorem B511251 : Blo 507795 511251 := bstep (se 1 (by rfl) ⟨383438, by rfl⟩ : syracuseStep 511251 = 766877) B766877
theorem B511267 : Blo 507795 511267 := bstep (se 1 (by rfl) ⟨383450, by rfl⟩ : syracuseStep 511267 = 766901) B766901
theorem B511283 : Blo 507795 511283 := bstep (se 1 (by rfl) ⟨383462, by rfl⟩ : syracuseStep 511283 = 766925) B766925
theorem B511299 : Blo 507795 511299 := bstep (se 1 (by rfl) ⟨383474, by rfl⟩ : syracuseStep 511299 = 766949) B766949
theorem B511315 : Blo 507795 511315 := bstep (se 1 (by rfl) ⟨383486, by rfl⟩ : syracuseStep 511315 = 766973) B766973
theorem B511331 : Blo 507795 511331 := bstep (se 1 (by rfl) ⟨383498, by rfl⟩ : syracuseStep 511331 = 766997) B766997
theorem B544115 : Blo 507795 544115 := bstep (se 1 (by rfl) ⟨408086, by rfl⟩ : syracuseStep 544115 = 816173) B816173
theorem B511347 : Blo 507795 511347 := bstep (se 1 (by rfl) ⟨383510, by rfl⟩ : syracuseStep 511347 = 767021) B767021
theorem B511363 : Blo 507795 511363 := bstep (se 1 (by rfl) ⟨383522, by rfl⟩ : syracuseStep 511363 = 767045) B767045
theorem B511379 : Blo 507795 511379 := bstep (se 1 (by rfl) ⟨383534, by rfl⟩ : syracuseStep 511379 = 767069) B767069
theorem B970147 : Blo 507795 970147 := bstep (se 1 (by rfl) ⟨727610, by rfl⟩ : syracuseStep 970147 = 1455221) B1455221
theorem B511395 : Blo 507795 511395 := bstep (se 1 (by rfl) ⟨383546, by rfl⟩ : syracuseStep 511395 = 767093) B767093
theorem B511411 : Blo 507795 511411 := bstep (se 1 (by rfl) ⟨383558, by rfl⟩ : syracuseStep 511411 = 767117) B767117
theorem B511427 : Blo 507795 511427 := bstep (se 1 (by rfl) ⟨383570, by rfl⟩ : syracuseStep 511427 = 767141) B767141
theorem B970193 : Blo 507795 970193 := bstep (se 2 (by rfl) ⟨363822, by rfl⟩ : syracuseStep 970193 = 727645) B727645
theorem B511443 : Blo 507795 511443 := bstep (se 1 (by rfl) ⟨383582, by rfl⟩ : syracuseStep 511443 = 767165) B767165
theorem B511459 : Blo 507795 511459 := bstep (se 1 (by rfl) ⟨383594, by rfl⟩ : syracuseStep 511459 = 767189) B767189
theorem B511475 : Blo 507795 511475 := bstep (se 1 (by rfl) ⟨383606, by rfl⟩ : syracuseStep 511475 = 767213) B767213
theorem B511491 : Blo 507795 511491 := bstep (se 1 (by rfl) ⟨383618, by rfl⟩ : syracuseStep 511491 = 767237) B767237
theorem B3919373 : Blo 507795 3919373 := bstep (se 3 (by rfl) ⟨734882, by rfl⟩ : syracuseStep 3919373 = 1469765) B1469765
theorem B511507 : Blo 507795 511507 := bstep (se 1 (by rfl) ⟨383630, by rfl⟩ : syracuseStep 511507 = 767261) B767261
theorem B511523 : Blo 507795 511523 := bstep (se 1 (by rfl) ⟨383642, by rfl⟩ : syracuseStep 511523 = 767285) B767285
theorem B1723949 : Blo 507795 1723949 := bstep (se 3 (by rfl) ⟨323240, by rfl⟩ : syracuseStep 1723949 = 646481) B646481
theorem B511539 : Blo 507795 511539 := bstep (se 1 (by rfl) ⟨383654, by rfl⟩ : syracuseStep 511539 = 767309) B767309
theorem B511555 : Blo 507795 511555 := bstep (se 1 (by rfl) ⟨383666, by rfl⟩ : syracuseStep 511555 = 767333) B767333
theorem B511571 : Blo 507795 511571 := bstep (se 1 (by rfl) ⟨383678, by rfl⟩ : syracuseStep 511571 = 767357) B767357
theorem B1724003 : Blo 507795 1724003 := bstep (se 1 (by rfl) ⟨1293002, by rfl⟩ : syracuseStep 1724003 = 2586005) B2586005
theorem B511587 : Blo 507795 511587 := bstep (se 1 (by rfl) ⟨383690, by rfl⟩ : syracuseStep 511587 = 767381) B767381
theorem B511603 : Blo 507795 511603 := bstep (se 1 (by rfl) ⟨383702, by rfl⟩ : syracuseStep 511603 = 767405) B767405
theorem B511619 : Blo 507795 511619 := bstep (se 1 (by rfl) ⟨383714, by rfl⟩ : syracuseStep 511619 = 767429) B767429
theorem B511635 : Blo 507795 511635 := bstep (se 1 (by rfl) ⟨383726, by rfl⟩ : syracuseStep 511635 = 767453) B767453
theorem B511651 : Blo 507795 511651 := bstep (se 1 (by rfl) ⟨383738, by rfl⟩ : syracuseStep 511651 = 767477) B767477
theorem B511667 : Blo 507795 511667 := bstep (se 1 (by rfl) ⟨383750, by rfl⟩ : syracuseStep 511667 = 767501) B767501
theorem B642755 : Blo 507795 642755 := bstep (se 1 (by rfl) ⟨482066, by rfl⟩ : syracuseStep 642755 = 964133) B964133
theorem B511683 : Blo 507795 511683 := bstep (se 1 (by rfl) ⟨383762, by rfl⟩ : syracuseStep 511683 = 767525) B767525
theorem B511699 : Blo 507795 511699 := bstep (se 1 (by rfl) ⟨383774, by rfl⟩ : syracuseStep 511699 = 767549) B767549
theorem B511715 : Blo 507795 511715 := bstep (se 1 (by rfl) ⟨383786, by rfl⟩ : syracuseStep 511715 = 767573) B767573
theorem B970481 : Blo 507795 970481 := bstep (se 2 (by rfl) ⟨363930, by rfl⟩ : syracuseStep 970481 = 727861) B727861
theorem B511731 : Blo 507795 511731 := bstep (se 1 (by rfl) ⟨383798, by rfl⟩ : syracuseStep 511731 = 767597) B767597
theorem B511747 : Blo 507795 511747 := bstep (se 1 (by rfl) ⟨383810, by rfl⟩ : syracuseStep 511747 = 767621) B767621
theorem B511763 : Blo 507795 511763 := bstep (se 1 (by rfl) ⟨383822, by rfl⟩ : syracuseStep 511763 = 767645) B767645
theorem B511779 : Blo 507795 511779 := bstep (se 1 (by rfl) ⟨383834, by rfl⟩ : syracuseStep 511779 = 767669) B767669
theorem B2477873 : Blo 507795 2477873 := bstep (se 2 (by rfl) ⟨929202, by rfl⟩ : syracuseStep 2477873 = 1858405) B1858405
theorem B511795 : Blo 507795 511795 := bstep (se 1 (by rfl) ⟨383846, by rfl⟩ : syracuseStep 511795 = 767693) B767693
theorem B1724273 : Blo 507795 1724273 := bstep (se 2 (by rfl) ⟨646602, by rfl⟩ : syracuseStep 1724273 = 1293205) B1293205
theorem B2903971 : Blo 507795 2903971 := bstep (se 1 (by rfl) ⟨2177978, by rfl⟩ : syracuseStep 2903971 = 4355957) B4355957
theorem B774193 : Blo 507795 774193 := bstep (se 2 (by rfl) ⟨290322, by rfl⟩ : syracuseStep 774193 = 580645) B580645
theorem B2183345 : Blo 507795 2183345 := bstep (se 2 (by rfl) ⟨818754, by rfl⟩ : syracuseStep 2183345 = 1637509) B1637509
theorem B545059 : Blo 507795 545059 := bstep (se 1 (by rfl) ⟨408794, by rfl⟩ : syracuseStep 545059 = 817589) B817589
theorem B774515 : Blo 507795 774515 := bstep (se 1 (by rfl) ⟨580886, by rfl⟩ : syracuseStep 774515 = 1161773) B1161773
theorem B643459 : Blo 507795 643459 := bstep (se 1 (by rfl) ⟨482594, by rfl⟩ : syracuseStep 643459 = 965189) B965189
theorem B1724813 : Blo 507795 1724813 := bstep (se 3 (by rfl) ⟨323402, by rfl⟩ : syracuseStep 1724813 = 646805) B646805
theorem B2904497 : Blo 507795 2904497 := bstep (se 2 (by rfl) ⟨1089186, by rfl⟩ : syracuseStep 2904497 = 2178373) B2178373
theorem B1724867 : Blo 507795 1724867 := bstep (se 1 (by rfl) ⟨1293650, by rfl⟩ : syracuseStep 1724867 = 2587301) B2587301
theorem B1036739 : Blo 507795 1036739 := bstep (se 1 (by rfl) ⟨777554, by rfl⟩ : syracuseStep 1036739 = 1555109) B1555109
theorem B971203 : Blo 507795 971203 := bstep (se 1 (by rfl) ⟨728402, by rfl⟩ : syracuseStep 971203 = 1456805) B1456805
theorem B643555 : Blo 507795 643555 := bstep (se 1 (by rfl) ⟨482666, by rfl⟩ : syracuseStep 643555 = 965333) B965333
theorem B1495523 : Blo 507795 1495523 := bstep (se 1 (by rfl) ⟨1121642, by rfl⟩ : syracuseStep 1495523 = 2243285) B2243285
theorem B5788259 : Blo 507795 5788259 := bstep (se 1 (by rfl) ⟨4341194, by rfl⟩ : syracuseStep 5788259 = 8682389) B8682389
theorem B3265123 : Blo 507795 3265123 := bstep (se 1 (by rfl) ⟨2448842, by rfl⟩ : syracuseStep 3265123 = 4897685) B4897685
theorem B5526157 : Blo 507795 5526157 := bstep (se 3 (by rfl) ⟨1036154, by rfl⟩ : syracuseStep 5526157 = 2072309) B2072309
theorem B873107 : Blo 507795 873107 := bstep (se 1 (by rfl) ⟨654830, by rfl⟩ : syracuseStep 873107 = 1309661) B1309661
theorem B1725137 : Blo 507795 1725137 := bstep (se 2 (by rfl) ⟨646926, by rfl⟩ : syracuseStep 1725137 = 1293853) B1293853
theorem B644051 : Blo 507795 644051 := bstep (se 1 (by rfl) ⟨483038, by rfl⟩ : syracuseStep 644051 = 966077) B966077
theorem B611491 : Blo 507795 611491 := bstep (se 1 (by rfl) ⟨458618, by rfl⟩ : syracuseStep 611491 = 917237) B917237
theorem B1725677 : Blo 507795 1725677 := bstep (se 3 (by rfl) ⟨323564, by rfl⟩ : syracuseStep 1725677 = 647129) B647129
theorem B1725731 : Blo 507795 1725731 := bstep (se 1 (by rfl) ⟨1294298, by rfl⟩ : syracuseStep 1725731 = 2588597) B2588597
theorem B2577905 : Blo 507795 2577905 := bstep (se 2 (by rfl) ⟨966714, by rfl⟩ : syracuseStep 2577905 = 1933429) B1933429
theorem B546323 : Blo 507795 546323 := bstep (se 1 (by rfl) ⟨409742, by rfl⟩ : syracuseStep 546323 = 819485) B819485
theorem B1726001 : Blo 507795 1726001 := bstep (se 2 (by rfl) ⟨647250, by rfl⟩ : syracuseStep 1726001 = 1294501) B1294501
theorem B644755 : Blo 507795 644755 := bstep (se 1 (by rfl) ⟨483566, by rfl⟩ : syracuseStep 644755 = 967133) B967133
theorem B644851 : Blo 507795 644851 := bstep (se 1 (by rfl) ⟨483638, by rfl⟩ : syracuseStep 644851 = 967277) B967277
theorem B2905955 : Blo 507795 2905955 := bstep (se 1 (by rfl) ⟨2179466, by rfl⟩ : syracuseStep 2905955 = 4358933) B4358933
theorem B612307 : Blo 507795 612307 := bstep (se 1 (by rfl) ⟨459230, by rfl⟩ : syracuseStep 612307 = 918461) B918461
theorem B6510563 : Blo 507795 6510563 := bstep (se 1 (by rfl) ⟨4882922, by rfl⟩ : syracuseStep 6510563 = 9765845) B9765845
theorem B1726541 : Blo 507795 1726541 := bstep (se 3 (by rfl) ⟨323726, by rfl⟩ : syracuseStep 1726541 = 647453) B647453
theorem B2447459 : Blo 507795 2447459 := bstep (se 1 (by rfl) ⟨1835594, by rfl⟩ : syracuseStep 2447459 = 3671189) B3671189
theorem B1726595 : Blo 507795 1726595 := bstep (se 1 (by rfl) ⟨1294946, by rfl⟩ : syracuseStep 1726595 = 2589893) B2589893
theorem B645347 : Blo 507795 645347 := bstep (se 1 (by rfl) ⟨484010, by rfl⟩ : syracuseStep 645347 = 968021) B968021
theorem B1628461 : Blo 507795 1628461 := bstep (se 3 (by rfl) ⟨305336, by rfl⟩ : syracuseStep 1628461 = 610673) B610673
theorem B579955 : Blo 507795 579955 := bstep (se 1 (by rfl) ⟨434966, by rfl⟩ : syracuseStep 579955 = 869933) B869933
theorem B1726865 : Blo 507795 1726865 := bstep (se 2 (by rfl) ⟨647574, by rfl⟩ : syracuseStep 1726865 = 1295149) B1295149
theorem B2447921 : Blo 507795 2447921 := bstep (se 2 (by rfl) ⟨917970, by rfl⟩ : syracuseStep 2447921 = 1835941) B1835941
theorem B2185805 : Blo 507795 2185805 := bstep (se 3 (by rfl) ⟨409838, by rfl⟩ : syracuseStep 2185805 = 819677) B819677
theorem B2316899 : Blo 507795 2316899 := bstep (se 1 (by rfl) ⟨1737674, by rfl⟩ : syracuseStep 2316899 = 3475349) B3475349
theorem B514883 : Blo 507795 514883 := bstep (se 1 (by rfl) ⟨386162, by rfl⟩ : syracuseStep 514883 = 772325) B772325
theorem B2579363 : Blo 507795 2579363 := bstep (se 1 (by rfl) ⟨1934522, by rfl⟩ : syracuseStep 2579363 = 3869045) B3869045
theorem B646051 : Blo 507795 646051 := bstep (se 1 (by rfl) ⟨484538, by rfl⟩ : syracuseStep 646051 = 969077) B969077
theorem B646147 : Blo 507795 646147 := bstep (se 1 (by rfl) ⟨484610, by rfl⟩ : syracuseStep 646147 = 969221) B969221
theorem B646643 : Blo 507795 646643 := bstep (se 1 (by rfl) ⟨484982, by rfl⟩ : syracuseStep 646643 = 969965) B969965
theorem B14114357 : Blo 507795 14114357 := bstep (se 5 (by rfl) ⟨661610, by rfl⟩ : syracuseStep 14114357 = 1323221) B1323221
theorem B581315 : Blo 507795 581315 := bstep (se 1 (by rfl) ⟨435986, by rfl⟩ : syracuseStep 581315 = 871973) B871973
theorem B2907845 : Blo 507795 2907845 := bstep (se 4 (by rfl) ⟨272610, by rfl⟩ : syracuseStep 2907845 = 545221) B545221
theorem B2580173 : Blo 507795 2580173 := bstep (se 3 (by rfl) ⟨483782, by rfl⟩ : syracuseStep 2580173 = 967565) B967565
theorem B1630307 : Blo 507795 1630307 := bstep (se 1 (by rfl) ⟨1222730, by rfl⟩ : syracuseStep 1630307 = 2445461) B2445461
theorem B1106065 : Blo 507795 1106065 := bstep (se 2 (by rfl) ⟨414774, by rfl⟩ : syracuseStep 1106065 = 829549) B829549
theorem B647347 : Blo 507795 647347 := bstep (se 1 (by rfl) ⟨485510, by rfl⟩ : syracuseStep 647347 = 971021) B971021
theorem B5824709 : Blo 507795 5824709 := bstep (se 4 (by rfl) ⟨546066, by rfl⟩ : syracuseStep 5824709 = 1092133) B1092133
theorem B13197539 : Blo 507795 13197539 := bstep (se 1 (by rfl) ⟨9898154, by rfl⟩ : syracuseStep 13197539 = 19796309) B19796309
theorem B647443 : Blo 507795 647443 := bstep (se 1 (by rfl) ⟨485582, by rfl⟩ : syracuseStep 647443 = 971165) B971165
theorem B3268997 : Blo 507795 3268997 := bstep (se 4 (by rfl) ⟨306468, by rfl⟩ : syracuseStep 3268997 = 612937) B612937
theorem B1630705 : Blo 507795 1630705 := bstep (se 2 (by rfl) ⟨611514, by rfl⟩ : syracuseStep 1630705 = 1223029) B1223029
theorem B6545933 : Blo 507795 6545933 := bstep (se 3 (by rfl) ⟨1227362, by rfl⟩ : syracuseStep 6545933 = 2454725) B2454725
theorem B1106723 : Blo 507795 1106723 := bstep (se 1 (by rfl) ⟨830042, by rfl⟩ : syracuseStep 1106723 = 1660085) B1660085
theorem B4350833 : Blo 507795 4350833 := bstep (se 2 (by rfl) ⟨1631562, by rfl⟩ : syracuseStep 4350833 = 3263125) B3263125
theorem B1631153 : Blo 507795 1631153 := bstep (se 2 (by rfl) ⟨611682, by rfl⟩ : syracuseStep 1631153 = 1223365) B1223365
theorem B746689 : Blo 507795 746689 := bstep (se 2 (by rfl) ⟨280008, by rfl⟩ : syracuseStep 746689 = 560017) B560017
theorem B3663089 : Blo 507795 3663089 := bstep (se 2 (by rfl) ⟨1373658, by rfl⟩ : syracuseStep 3663089 = 2747317) B2747317
theorem B3859811 : Blo 507795 3859811 := bstep (se 1 (by rfl) ⟨2894858, by rfl⟩ : syracuseStep 3859811 = 5789717) B5789717
theorem B1467917 : Blo 507795 1467917 := bstep (se 3 (by rfl) ⟨275234, by rfl⟩ : syracuseStep 1467917 = 550469) B550469
theorem B2451149 : Blo 507795 2451149 := bstep (se 3 (by rfl) ⟨459590, by rfl⟩ : syracuseStep 2451149 = 919181) B919181
theorem B4646641 : Blo 507795 4646641 := bstep (se 2 (by rfl) ⟨1742490, by rfl⟩ : syracuseStep 4646641 = 3484981) B3484981
theorem B2320589 : Blo 507795 2320589 := bstep (se 3 (by rfl) ⟨435110, by rfl⟩ : syracuseStep 2320589 = 870221) B870221
theorem B813539 : Blo 507795 813539 := bstep (se 1 (by rfl) ⟨610154, by rfl⟩ : syracuseStep 813539 = 1220309) B1220309
theorem B2583089 : Blo 507795 2583089 := bstep (se 2 (by rfl) ⟨968658, by rfl⟩ : syracuseStep 2583089 = 1937317) B1937317
theorem B813667 : Blo 507795 813667 := bstep (se 1 (by rfl) ⟨610250, by rfl⟩ : syracuseStep 813667 = 1220501) B1220501
theorem B518755 : Blo 507795 518755 := bstep (se 1 (by rfl) ⟨389066, by rfl⟩ : syracuseStep 518755 = 778133) B778133
theorem B2746993 : Blo 507795 2746993 := bstep (se 2 (by rfl) ⟨1030122, by rfl⟩ : syracuseStep 2746993 = 2060245) B2060245
theorem B813731 : Blo 507795 813731 := bstep (se 1 (by rfl) ⟨610298, by rfl⟩ : syracuseStep 813731 = 1220597) B1220597
theorem B2616077 : Blo 507795 2616077 := bstep (se 3 (by rfl) ⟨490514, by rfl⟩ : syracuseStep 2616077 = 981029) B981029
theorem B4025285 : Blo 507795 4025285 := bstep (se 4 (by rfl) ⟨377370, by rfl⟩ : syracuseStep 4025285 = 754741) B754741
theorem B1633229 : Blo 507795 1633229 := bstep (se 3 (by rfl) ⟨306230, by rfl⟩ : syracuseStep 1633229 = 612461) B612461
theorem B814225 : Blo 507795 814225 := bstep (se 2 (by rfl) ⟨305334, by rfl⟩ : syracuseStep 814225 = 610669) B610669
theorem B552115 : Blo 507795 552115 := bstep (se 1 (by rfl) ⟨414086, by rfl⟩ : syracuseStep 552115 = 828173) B828173
theorem B1961165 : Blo 507795 1961165 := bstep (se 3 (by rfl) ⟨367718, by rfl⟩ : syracuseStep 1961165 = 735437) B735437
theorem B3272197 : Blo 507795 3272197 := bstep (se 4 (by rfl) ⟨306768, by rfl⟩ : syracuseStep 3272197 = 613537) B613537
theorem B814897 : Blo 507795 814897 := bstep (se 2 (by rfl) ⟨305586, by rfl⟩ : syracuseStep 814897 = 611173) B611173
theorem B2584547 : Blo 507795 2584547 := bstep (se 1 (by rfl) ⟨1938410, by rfl⟩ : syracuseStep 2584547 = 3876821) B3876821
theorem B1142801 : Blo 507795 1142801 := bstep (se 2 (by rfl) ⟨428550, by rfl⟩ : syracuseStep 1142801 = 857101) B857101
theorem B1142819 : Blo 507795 1142819 := bstep (se 1 (by rfl) ⟨857114, by rfl⟩ : syracuseStep 1142819 = 1714229) B1714229
theorem B1929329 : Blo 507795 1929329 := bstep (se 2 (by rfl) ⟨723498, by rfl⟩ : syracuseStep 1929329 = 1446997) B1446997
theorem B815267 : Blo 507795 815267 := bstep (se 1 (by rfl) ⟨611450, by rfl⟩ : syracuseStep 815267 = 1222901) B1222901
theorem B1634509 : Blo 507795 1634509 := bstep (se 3 (by rfl) ⟨306470, by rfl⟩ : syracuseStep 1634509 = 612941) B612941
theorem B1143089 : Blo 507795 1143089 := bstep (se 2 (by rfl) ⟨428658, by rfl⟩ : syracuseStep 1143089 = 857317) B857317
theorem B1143107 : Blo 507795 1143107 := bstep (se 1 (by rfl) ⟨857330, by rfl⟩ : syracuseStep 1143107 = 1714661) B1714661
theorem B1372717 : Blo 507795 1372717 := bstep (se 3 (by rfl) ⟨257384, by rfl⟩ : syracuseStep 1372717 = 514769) B514769
theorem B1143377 : Blo 507795 1143377 := bstep (se 2 (by rfl) ⟨428766, by rfl⟩ : syracuseStep 1143377 = 857533) B857533
theorem B1143395 : Blo 507795 1143395 := bstep (se 1 (by rfl) ⟨857546, by rfl⟩ : syracuseStep 1143395 = 1715093) B1715093
theorem B1635011 : Blo 507795 1635011 := bstep (se 1 (by rfl) ⟨1226258, by rfl⟩ : syracuseStep 1635011 = 2452517) B2452517
theorem B2585357 : Blo 507795 2585357 := bstep (se 3 (by rfl) ⟨484754, by rfl⟩ : syracuseStep 2585357 = 969509) B969509
theorem B1176401 : Blo 507795 1176401 := bstep (se 2 (by rfl) ⟨441150, by rfl⟩ : syracuseStep 1176401 = 882301) B882301
theorem B1143665 : Blo 507795 1143665 := bstep (se 2 (by rfl) ⟨428874, by rfl⟩ : syracuseStep 1143665 = 857749) B857749
theorem B815987 : Blo 507795 815987 := bstep (se 1 (by rfl) ⟨611990, by rfl⟩ : syracuseStep 815987 = 1223981) B1223981
theorem B1143683 : Blo 507795 1143683 := bstep (se 1 (by rfl) ⟨857762, by rfl⟩ : syracuseStep 1143683 = 1715525) B1715525
theorem B816065 : Blo 507795 816065 := bstep (se 2 (by rfl) ⟨306024, by rfl⟩ : syracuseStep 816065 = 612049) B612049
theorem B1143953 : Blo 507795 1143953 := bstep (se 2 (by rfl) ⟨428982, by rfl⟩ : syracuseStep 1143953 = 857965) B857965
theorem B816275 : Blo 507795 816275 := bstep (se 1 (by rfl) ⟨612206, by rfl⟩ : syracuseStep 816275 = 1224413) B1224413
theorem B1143971 : Blo 507795 1143971 := bstep (se 1 (by rfl) ⟨857978, by rfl⟩ : syracuseStep 1143971 = 1715957) B1715957
theorem B1373539 : Blo 507795 1373539 := bstep (se 1 (by rfl) ⟨1030154, by rfl⟩ : syracuseStep 1373539 = 2060309) B2060309
theorem B2913677 : Blo 507795 2913677 := bstep (se 3 (by rfl) ⟨546314, by rfl⟩ : syracuseStep 2913677 = 1092629) B1092629
theorem B1144241 : Blo 507795 1144241 := bstep (se 2 (by rfl) ⟨429090, by rfl⟩ : syracuseStep 1144241 = 858181) B858181
theorem B1144259 : Blo 507795 1144259 := bstep (se 1 (by rfl) ⟨858194, by rfl⟩ : syracuseStep 1144259 = 1716389) B1716389
theorem B1471981 : Blo 507795 1471981 := bstep (se 3 (by rfl) ⟨275996, by rfl⟩ : syracuseStep 1471981 = 551993) B551993
theorem B1930787 : Blo 507795 1930787 := bstep (se 1 (by rfl) ⟨1448090, by rfl⟩ : syracuseStep 1930787 = 2896181) B2896181
theorem B816691 : Blo 507795 816691 := bstep (se 1 (by rfl) ⟨612518, by rfl⟩ : syracuseStep 816691 = 1225037) B1225037
theorem B2618993 : Blo 507795 2618993 := bstep (se 2 (by rfl) ⟨982122, by rfl⟩ : syracuseStep 2618993 = 1964245) B1964245
theorem B1144529 : Blo 507795 1144529 := bstep (se 2 (by rfl) ⟨429198, by rfl⟩ : syracuseStep 1144529 = 858397) B858397
theorem B1144547 : Blo 507795 1144547 := bstep (se 1 (by rfl) ⟨858410, by rfl⟩ : syracuseStep 1144547 = 1716821) B1716821
theorem B816961 : Blo 507795 816961 := bstep (se 2 (by rfl) ⟨306360, by rfl⟩ : syracuseStep 816961 = 612721) B612721
theorem B1308593 : Blo 507795 1308593 := bstep (se 2 (by rfl) ⟨490722, by rfl⟩ : syracuseStep 1308593 = 981445) B981445
theorem B2750435 : Blo 507795 2750435 := bstep (se 1 (by rfl) ⟨2062826, by rfl⟩ : syracuseStep 2750435 = 4125653) B4125653
theorem B1144817 : Blo 507795 1144817 := bstep (se 2 (by rfl) ⟨429306, by rfl⟩ : syracuseStep 1144817 = 858613) B858613
theorem B1144835 : Blo 507795 1144835 := bstep (se 1 (by rfl) ⟨858626, by rfl⟩ : syracuseStep 1144835 = 1717253) B1717253
theorem B1636355 : Blo 507795 1636355 := bstep (se 1 (by rfl) ⟨1227266, by rfl⟩ : syracuseStep 1636355 = 2454533) B2454533
theorem B2488333 : Blo 507795 2488333 := bstep (se 3 (by rfl) ⟨466562, by rfl⟩ : syracuseStep 2488333 = 933125) B933125
theorem B915491 : Blo 507795 915491 := bstep (se 1 (by rfl) ⟨686618, by rfl⟩ : syracuseStep 915491 = 1373237) B1373237
theorem B2062385 : Blo 507795 2062385 := bstep (se 2 (by rfl) ⟨773394, by rfl⟩ : syracuseStep 2062385 = 1546789) B1546789
theorem B817217 : Blo 507795 817217 := bstep (se 2 (by rfl) ⟨306456, by rfl⟩ : syracuseStep 817217 = 612913) B612913
theorem B981155 : Blo 507795 981155 := bstep (se 1 (by rfl) ⟨735866, by rfl⟩ : syracuseStep 981155 = 1471733) B1471733
theorem B915715 : Blo 507795 915715 := bstep (se 1 (by rfl) ⟨686786, by rfl⟩ : syracuseStep 915715 = 1373573) B1373573
theorem B1145105 : Blo 507795 1145105 := bstep (se 2 (by rfl) ⟨429414, by rfl⟩ : syracuseStep 1145105 = 858829) B858829
theorem B1145123 : Blo 507795 1145123 := bstep (se 1 (by rfl) ⟨858842, by rfl⟩ : syracuseStep 1145123 = 1717685) B1717685
theorem B1571185 : Blo 507795 1571185 := bstep (se 2 (by rfl) ⟨589194, by rfl⟩ : syracuseStep 1571185 = 1178389) B1178389
theorem B4127203 : Blo 507795 4127203 := bstep (se 1 (by rfl) ⟨3095402, by rfl⟩ : syracuseStep 4127203 = 6190805) B6190805
theorem B1931789 : Blo 507795 1931789 := bstep (se 3 (by rfl) ⟨362210, by rfl⟩ : syracuseStep 1931789 = 724421) B724421
theorem B1145393 : Blo 507795 1145393 := bstep (se 2 (by rfl) ⟨429522, by rfl⟩ : syracuseStep 1145393 = 859045) B859045
theorem B686657 : Blo 507795 686657 := bstep (se 2 (by rfl) ⟨257496, by rfl⟩ : syracuseStep 686657 = 514993) B514993
theorem B1145411 : Blo 507795 1145411 := bstep (se 1 (by rfl) ⟨859058, by rfl⟩ : syracuseStep 1145411 = 1718117) B1718117
theorem B3865157 : Blo 507795 3865157 := bstep (se 4 (by rfl) ⟨362358, by rfl⟩ : syracuseStep 3865157 = 724717) B724717
theorem B916067 : Blo 507795 916067 := bstep (se 1 (by rfl) ⟨687050, by rfl⟩ : syracuseStep 916067 = 1374101) B1374101
theorem B9435761 : Blo 507795 9435761 := bstep (se 2 (by rfl) ⟨3538410, by rfl⟩ : syracuseStep 9435761 = 7076821) B7076821
theorem B817921 : Blo 507795 817921 := bstep (se 2 (by rfl) ⟨306720, by rfl⟩ : syracuseStep 817921 = 613441) B613441
theorem B1145681 : Blo 507795 1145681 := bstep (se 2 (by rfl) ⟨429630, by rfl⟩ : syracuseStep 1145681 = 859261) B859261
theorem B1145699 : Blo 507795 1145699 := bstep (se 1 (by rfl) ⟨859274, by rfl⟩ : syracuseStep 1145699 = 1718549) B1718549
theorem B1637329 : Blo 507795 1637329 := bstep (se 2 (by rfl) ⟨613998, by rfl⟩ : syracuseStep 1637329 = 1227997) B1227997
theorem B3275761 : Blo 507795 3275761 := bstep (se 2 (by rfl) ⟨1228410, by rfl⟩ : syracuseStep 3275761 = 2456821) B2456821
theorem B6716515 : Blo 507795 6716515 := bstep (se 1 (by rfl) ⟨5037386, by rfl⟩ : syracuseStep 6716515 = 10074773) B10074773
theorem B1145969 : Blo 507795 1145969 := bstep (se 2 (by rfl) ⟨429738, by rfl⟩ : syracuseStep 1145969 = 859477) B859477
theorem B1145987 : Blo 507795 1145987 := bstep (se 1 (by rfl) ⟨859490, by rfl⟩ : syracuseStep 1145987 = 1718981) B1718981
theorem B1637585 : Blo 507795 1637585 := bstep (se 2 (by rfl) ⟨614094, by rfl⟩ : syracuseStep 1637585 = 1228189) B1228189
theorem B982307 : Blo 507795 982307 := bstep (se 1 (by rfl) ⟨736730, by rfl⟩ : syracuseStep 982307 = 1473461) B1473461
theorem B1146257 : Blo 507795 1146257 := bstep (se 2 (by rfl) ⟨429846, by rfl⟩ : syracuseStep 1146257 = 859693) B859693
theorem B1146275 : Blo 507795 1146275 := bstep (se 1 (by rfl) ⟨859706, by rfl⟩ : syracuseStep 1146275 = 1719413) B1719413
theorem B654851 : Blo 507795 654851 := bstep (se 1 (by rfl) ⟨491138, by rfl⟩ : syracuseStep 654851 = 982277) B982277
theorem B2588273 : Blo 507795 2588273 := bstep (se 2 (by rfl) ⟨970602, by rfl⟩ : syracuseStep 2588273 = 1941205) B1941205
theorem B818819 : Blo 507795 818819 := bstep (se 1 (by rfl) ⟨614114, by rfl⟩ : syracuseStep 818819 = 1228229) B1228229
theorem B2752163 : Blo 507795 2752163 := bstep (se 1 (by rfl) ⟨2064122, by rfl⟩ : syracuseStep 2752163 = 4128245) B4128245
theorem B1146545 : Blo 507795 1146545 := bstep (se 2 (by rfl) ⟨429954, by rfl⟩ : syracuseStep 1146545 = 859909) B859909
theorem B1146563 : Blo 507795 1146563 := bstep (se 1 (by rfl) ⟨859922, by rfl⟩ : syracuseStep 1146563 = 1719845) B1719845
theorem B1834787 : Blo 507795 1834787 := bstep (se 1 (by rfl) ⟨1376090, by rfl⟩ : syracuseStep 1834787 = 2752181) B2752181
theorem B819011 : Blo 507795 819011 := bstep (se 1 (by rfl) ⟨614258, by rfl⟩ : syracuseStep 819011 = 1228517) B1228517
theorem B13565893 : Blo 507795 13565893 := bstep (se 4 (by rfl) ⟨1271802, by rfl⟩ : syracuseStep 13565893 = 2543605) B2543605
theorem B1146833 : Blo 507795 1146833 := bstep (se 2 (by rfl) ⟨430062, by rfl⟩ : syracuseStep 1146833 = 860125) B860125
theorem B1146851 : Blo 507795 1146851 := bstep (se 1 (by rfl) ⟨860138, by rfl⟩ : syracuseStep 1146851 = 1720277) B1720277
theorem B1146905 : Blo 507795 1146905 := bstep (se 2 (by rfl) ⟨430089, by rfl⟩ : syracuseStep 1146905 = 860179) B860179
theorem B1146995 : Blo 507795 1146995 := bstep (se 1 (by rfl) ⟨860246, by rfl⟩ : syracuseStep 1146995 = 1720493) B1720493
theorem B1147031 : Blo 507795 1147031 := bstep (se 1 (by rfl) ⟨860273, by rfl⟩ : syracuseStep 1147031 = 1720547) B1720547
theorem B1147211 : Blo 507795 1147211 := bstep (se 1 (by rfl) ⟨860408, by rfl⟩ : syracuseStep 1147211 = 1720817) B1720817
theorem B1147265 : Blo 507795 1147265 := bstep (se 2 (by rfl) ⟨430224, by rfl⟩ : syracuseStep 1147265 = 860449) B860449
theorem B4718999 : Blo 507795 4718999 := bstep (se 1 (by rfl) ⟨3539249, by rfl⟩ : syracuseStep 4718999 = 7078499) B7078499
theorem B1147481 : Blo 507795 1147481 := bstep (se 2 (by rfl) ⟨430305, by rfl⟩ : syracuseStep 1147481 = 860611) B860611
theorem B35193437 : Blo 507795 35193437 := bstep (se 3 (by rfl) ⟨6598769, by rfl⟩ : syracuseStep 35193437 = 13197539) B13197539
theorem B16515677 : Blo 507795 16515677 := bstep (se 3 (by rfl) ⟨3096689, by rfl⟩ : syracuseStep 16515677 = 6193379) B6193379
theorem B1147571 : Blo 507795 1147571 := bstep (se 1 (by rfl) ⟨860678, by rfl⟩ : syracuseStep 1147571 = 1721357) B1721357
theorem B1147607 : Blo 507795 1147607 := bstep (se 1 (by rfl) ⟨860705, by rfl⟩ : syracuseStep 1147607 = 1721411) B1721411
theorem B3277529 : Blo 507795 3277529 := bstep (se 2 (by rfl) ⟨1229073, by rfl⟩ : syracuseStep 3277529 = 2458147) B2458147
theorem B5899013 : Blo 507795 5899013 := bstep (se 4 (by rfl) ⟨553032, by rfl⟩ : syracuseStep 5899013 = 1106065) B1106065
theorem B1147787 : Blo 507795 1147787 := bstep (se 1 (by rfl) ⟨860840, by rfl⟩ : syracuseStep 1147787 = 1721681) B1721681
theorem B1147841 : Blo 507795 1147841 := bstep (se 2 (by rfl) ⟨430440, by rfl⟩ : syracuseStep 1147841 = 860881) B860881
theorem B1836055 : Blo 507795 1836055 := bstep (se 1 (by rfl) ⟨1377041, by rfl⟩ : syracuseStep 1836055 = 2754083) B2754083
theorem B1934387 : Blo 507795 1934387 := bstep (se 1 (by rfl) ⟨1450790, by rfl⟩ : syracuseStep 1934387 = 2901581) B2901581
theorem B1934401 : Blo 507795 1934401 := bstep (se 2 (by rfl) ⟨725400, by rfl⟩ : syracuseStep 1934401 = 1450801) B1450801
theorem B8717381 : Blo 507795 8717381 := bstep (se 4 (by rfl) ⟨817254, by rfl⟩ : syracuseStep 8717381 = 1634509) B1634509
theorem B1148057 : Blo 507795 1148057 := bstep (se 2 (by rfl) ⟨430521, by rfl⟩ : syracuseStep 1148057 = 861043) B861043
theorem B1148147 : Blo 507795 1148147 := bstep (se 1 (by rfl) ⟨861110, by rfl⟩ : syracuseStep 1148147 = 1722221) B1722221
theorem B1148183 : Blo 507795 1148183 := bstep (se 1 (by rfl) ⟨861137, by rfl⟩ : syracuseStep 1148183 = 1722275) B1722275
theorem B1770817 : Blo 507795 1770817 := bstep (se 2 (by rfl) ⟨664056, by rfl⟩ : syracuseStep 1770817 = 1328113) B1328113
theorem B4883813 : Blo 507795 4883813 := bstep (se 4 (by rfl) ⟨457857, by rfl⟩ : syracuseStep 4883813 = 915715) B915715
theorem B1148363 : Blo 507795 1148363 := bstep (se 1 (by rfl) ⟨861272, by rfl⟩ : syracuseStep 1148363 = 1722545) B1722545
theorem B984523 : Blo 507795 984523 := bstep (se 1 (by rfl) ⟨738392, by rfl⟩ : syracuseStep 984523 = 1476785) B1476785
theorem B1148417 : Blo 507795 1148417 := bstep (se 2 (by rfl) ⟨430656, by rfl⟩ : syracuseStep 1148417 = 861313) B861313
theorem B1181249 : Blo 507795 1181249 := bstep (se 2 (by rfl) ⟨442968, by rfl⟩ : syracuseStep 1181249 = 885937) B885937
theorem B1377985 : Blo 507795 1377985 := bstep (se 2 (by rfl) ⟨516744, by rfl⟩ : syracuseStep 1377985 = 1033489) B1033489
theorem B1148633 : Blo 507795 1148633 := bstep (se 2 (by rfl) ⟨430737, by rfl⟩ : syracuseStep 1148633 = 861475) B861475
theorem B4130605 : Blo 507795 4130605 := bstep (se 3 (by rfl) ⟨774488, by rfl⟩ : syracuseStep 4130605 = 1548977) B1548977
theorem B1148723 : Blo 507795 1148723 := bstep (se 1 (by rfl) ⟨861542, by rfl⟩ : syracuseStep 1148723 = 1723085) B1723085
theorem B1148759 : Blo 507795 1148759 := bstep (se 1 (by rfl) ⟨861569, by rfl⟩ : syracuseStep 1148759 = 1723139) B1723139
theorem B1836893 : Blo 507795 1836893 := bstep (se 3 (by rfl) ⟨344417, by rfl⟩ : syracuseStep 1836893 = 688835) B688835
theorem B1148939 : Blo 507795 1148939 := bstep (se 1 (by rfl) ⟨861704, by rfl⟩ : syracuseStep 1148939 = 1723409) B1723409
theorem B690187 : Blo 507795 690187 := bstep (se 1 (by rfl) ⟨517640, by rfl⟩ : syracuseStep 690187 = 1035281) B1035281
theorem B1148993 : Blo 507795 1148993 := bstep (se 2 (by rfl) ⟨430872, by rfl⟩ : syracuseStep 1148993 = 861745) B861745
theorem B2951261 : Blo 507795 2951261 := bstep (se 3 (by rfl) ⟨553361, by rfl⟩ : syracuseStep 2951261 = 1106723) B1106723
theorem B919831 : Blo 507795 919831 := bstep (se 1 (by rfl) ⟨689873, by rfl⟩ : syracuseStep 919831 = 1379747) B1379747
theorem B1149209 : Blo 507795 1149209 := bstep (se 2 (by rfl) ⟨430953, by rfl⟩ : syracuseStep 1149209 = 861907) B861907
theorem B6195521 : Blo 507795 6195521 := bstep (se 2 (by rfl) ⟨2323320, by rfl⟩ : syracuseStep 6195521 = 4646641) B4646641
theorem B1149299 : Blo 507795 1149299 := bstep (se 1 (by rfl) ⟨861974, by rfl⟩ : syracuseStep 1149299 = 1723949) B1723949
theorem B1149335 : Blo 507795 1149335 := bstep (se 1 (by rfl) ⟨862001, by rfl⟩ : syracuseStep 1149335 = 1724003) B1724003
theorem B1149515 : Blo 507795 1149515 := bstep (se 1 (by rfl) ⟨862136, by rfl⟩ : syracuseStep 1149515 = 1724273) B1724273
theorem B1149569 : Blo 507795 1149569 := bstep (se 2 (by rfl) ⟨431088, by rfl⟩ : syracuseStep 1149569 = 862177) B862177
theorem B5900951 : Blo 507795 5900951 := bstep (se 1 (by rfl) ⟨4425713, by rfl⟩ : syracuseStep 5900951 = 8851427) B8851427
theorem B1149785 : Blo 507795 1149785 := bstep (se 2 (by rfl) ⟨431169, by rfl⟩ : syracuseStep 1149785 = 862339) B862339
theorem B2329489 : Blo 507795 2329489 := bstep (se 2 (by rfl) ⟨873558, by rfl⟩ : syracuseStep 2329489 = 1747117) B1747117
theorem B723863 : Blo 507795 723863 := bstep (se 1 (by rfl) ⟨542897, by rfl⟩ : syracuseStep 723863 = 1085795) B1085795
theorem B1149875 : Blo 507795 1149875 := bstep (se 1 (by rfl) ⟨862406, by rfl⟩ : syracuseStep 1149875 = 1724813) B1724813
theorem B1936331 : Blo 507795 1936331 := bstep (se 1 (by rfl) ⟨1452248, by rfl⟩ : syracuseStep 1936331 = 2904497) B2904497
theorem B1149911 : Blo 507795 1149911 := bstep (se 1 (by rfl) ⟨862433, by rfl⟩ : syracuseStep 1149911 = 1724867) B1724867
theorem B1936345 : Blo 507795 1936345 := bstep (se 2 (by rfl) ⟨726129, by rfl⟩ : syracuseStep 1936345 = 1452259) B1452259
theorem B1150091 : Blo 507795 1150091 := bstep (se 1 (by rfl) ⟨862568, by rfl⟩ : syracuseStep 1150091 = 1725137) B1725137
theorem B7834805 : Blo 507795 7834805 := bstep (se 5 (by rfl) ⟨367256, by rfl⟩ : syracuseStep 7834805 = 734513) B734513
theorem B1150145 : Blo 507795 1150145 := bstep (se 2 (by rfl) ⟨431304, by rfl⟩ : syracuseStep 1150145 = 862609) B862609
theorem B3870017 : Blo 507795 3870017 := bstep (se 2 (by rfl) ⟨1451256, by rfl⟩ : syracuseStep 3870017 = 2902513) B2902513
theorem B1150361 : Blo 507795 1150361 := bstep (se 2 (by rfl) ⟨431385, by rfl⟩ : syracuseStep 1150361 = 862771) B862771
theorem B1510859 : Blo 507795 1510859 := bstep (se 1 (by rfl) ⟨1133144, by rfl⟩ : syracuseStep 1510859 = 2266289) B2266289
theorem B1084889 : Blo 507795 1084889 := bstep (se 2 (by rfl) ⟨406833, by rfl⟩ : syracuseStep 1084889 = 813667) B813667
theorem B691673 : Blo 507795 691673 := bstep (se 2 (by rfl) ⟨259377, by rfl⟩ : syracuseStep 691673 = 518755) B518755
theorem B1150451 : Blo 507795 1150451 := bstep (se 1 (by rfl) ⟨862838, by rfl⟩ : syracuseStep 1150451 = 1725677) B1725677
theorem B1969667 : Blo 507795 1969667 := bstep (se 1 (by rfl) ⟨1477250, by rfl⟩ : syracuseStep 1969667 = 2954501) B2954501
theorem B1150487 : Blo 507795 1150487 := bstep (se 1 (by rfl) ⟨862865, by rfl⟩ : syracuseStep 1150487 = 1725731) B1725731
theorem B1150667 : Blo 507795 1150667 := bstep (se 1 (by rfl) ⟨863000, by rfl⟩ : syracuseStep 1150667 = 1726001) B1726001
theorem B1150721 : Blo 507795 1150721 := bstep (se 2 (by rfl) ⟨431520, by rfl⟩ : syracuseStep 1150721 = 863041) B863041
theorem B1937303 : Blo 507795 1937303 := bstep (se 1 (by rfl) ⟨1452977, by rfl⟩ : syracuseStep 1937303 = 2905955) B2905955
theorem B1150937 : Blo 507795 1150937 := bstep (se 2 (by rfl) ⟨431601, by rfl⟩ : syracuseStep 1150937 = 863203) B863203
theorem B4362245 : Blo 507795 4362245 := bstep (se 4 (by rfl) ⟨408960, by rfl⟩ : syracuseStep 4362245 = 817921) B817921
theorem B1151027 : Blo 507795 1151027 := bstep (se 1 (by rfl) ⟨863270, by rfl⟩ : syracuseStep 1151027 = 1726541) B1726541
theorem B1151063 : Blo 507795 1151063 := bstep (se 1 (by rfl) ⟨863297, by rfl⟩ : syracuseStep 1151063 = 1726595) B1726595
theorem B1085633 : Blo 507795 1085633 := bstep (se 2 (by rfl) ⟨407112, by rfl⟩ : syracuseStep 1085633 = 814225) B814225
theorem B1151243 : Blo 507795 1151243 := bstep (se 1 (by rfl) ⟨863432, by rfl⟩ : syracuseStep 1151243 = 1726865) B1726865
theorem B6983981 : Blo 507795 6983981 := bstep (se 3 (by rfl) ⟨1309496, by rfl⟩ : syracuseStep 6983981 = 2618993) B2618993
theorem B1151297 : Blo 507795 1151297 := bstep (se 2 (by rfl) ⟨431736, by rfl⟩ : syracuseStep 1151297 = 863473) B863473
theorem B1544599 : Blo 507795 1544599 := bstep (se 1 (by rfl) ⟨1158449, by rfl⟩ : syracuseStep 1544599 = 2316899) B2316899
theorem B922007 : Blo 507795 922007 := bstep (se 1 (by rfl) ⟨691505, by rfl⟩ : syracuseStep 922007 = 1383011) B1383011
theorem B1151513 : Blo 507795 1151513 := bstep (se 2 (by rfl) ⟨431817, by rfl⟩ : syracuseStep 1151513 = 863635) B863635
theorem B4362929 : Blo 507795 4362929 := bstep (se 2 (by rfl) ⟨1636098, by rfl⟩ : syracuseStep 4362929 = 3272197) B3272197
theorem B856919 : Blo 507795 856919 := bstep (se 1 (by rfl) ⟨642689, by rfl⟩ : syracuseStep 856919 = 1285379) B1285379
theorem B857047 : Blo 507795 857047 := bstep (se 1 (by rfl) ⟨642785, by rfl⟩ : syracuseStep 857047 = 1285571) B1285571
theorem B1840151 : Blo 507795 1840151 := bstep (se 1 (by rfl) ⟨1380113, by rfl⟩ : syracuseStep 1840151 = 2760227) B2760227
theorem B9409571 : Blo 507795 9409571 := bstep (se 1 (by rfl) ⟨7057178, by rfl⟩ : syracuseStep 9409571 = 14114357) B14114357
theorem B1086529 : Blo 507795 1086529 := bstep (se 2 (by rfl) ⟨407448, by rfl⟩ : syracuseStep 1086529 = 814897) B814897
theorem B1938563 : Blo 507795 1938563 := bstep (se 1 (by rfl) ⟨1453922, by rfl⟩ : syracuseStep 1938563 = 2907845) B2907845
theorem B3871961 : Blo 507795 3871961 := bstep (se 2 (by rfl) ⟨1451985, by rfl⟩ : syracuseStep 3871961 = 2903971) B2903971
theorem B1086871 : Blo 507795 1086871 := bstep (se 1 (by rfl) ⟨815153, by rfl⟩ : syracuseStep 1086871 = 1630307) B1630307
theorem B3478963 : Blo 507795 3478963 := bstep (se 1 (by rfl) ⟨2609222, by rfl⟩ : syracuseStep 3478963 = 5218445) B5218445
theorem B1840657 : Blo 507795 1840657 := bstep (se 2 (by rfl) ⟨690246, by rfl⟩ : syracuseStep 1840657 = 1380493) B1380493
theorem B857675 : Blo 507795 857675 := bstep (se 1 (by rfl) ⟨643256, by rfl⟩ : syracuseStep 857675 = 1286513) B1286513
theorem B5969483 : Blo 507795 5969483 := bstep (se 1 (by rfl) ⟨4477112, by rfl⟩ : syracuseStep 5969483 = 8954225) B8954225
theorem B3675779 : Blo 507795 3675779 := bstep (se 1 (by rfl) ⟨2756834, by rfl⟩ : syracuseStep 3675779 = 5513669) B5513669
theorem B4363955 : Blo 507795 4363955 := bstep (se 1 (by rfl) ⟨3272966, by rfl⟩ : syracuseStep 4363955 = 6545933) B6545933
theorem B31495877 : Blo 507795 31495877 := bstep (se 4 (by rfl) ⟨2952738, by rfl⟩ : syracuseStep 31495877 = 5905477) B5905477
theorem B857803 : Blo 507795 857803 := bstep (se 1 (by rfl) ⟨643352, by rfl⟩ : syracuseStep 857803 = 1286705) B1286705
theorem B726745 : Blo 507795 726745 := bstep (se 2 (by rfl) ⟨272529, by rfl⟩ : syracuseStep 726745 = 545059) B545059
theorem B1447703 : Blo 507795 1447703 := bstep (se 1 (by rfl) ⟨1085777, by rfl⟩ : syracuseStep 1447703 = 2171555) B2171555
theorem B1382167 : Blo 507795 1382167 := bstep (se 1 (by rfl) ⟨1036625, by rfl⟩ : syracuseStep 1382167 = 2073251) B2073251
theorem B857945 : Blo 507795 857945 := bstep (se 2 (by rfl) ⟨321729, by rfl⟩ : syracuseStep 857945 = 643459) B643459
theorem B1841075 : Blo 507795 1841075 := bstep (se 1 (by rfl) ⟨1380806, by rfl⟩ : syracuseStep 1841075 = 2761613) B2761613
theorem B1087435 : Blo 507795 1087435 := bstep (se 1 (by rfl) ⟨815576, by rfl⟩ : syracuseStep 1087435 = 1631153) B1631153
theorem B858073 : Blo 507795 858073 := bstep (se 2 (by rfl) ⟨321777, by rfl⟩ : syracuseStep 858073 = 643555) B643555
theorem B9836579 : Blo 507795 9836579 := bstep (se 1 (by rfl) ⟨7377434, by rfl⟩ : syracuseStep 9836579 = 14754869) B14754869
theorem B3151973 : Blo 507795 3151973 := bstep (se 4 (by rfl) ⟨295497, by rfl⟩ : syracuseStep 3151973 = 590995) B590995
theorem B858647 : Blo 507795 858647 := bstep (se 1 (by rfl) ⟨643985, by rfl⟩ : syracuseStep 858647 = 1287971) B1287971
theorem B1448513 : Blo 507795 1448513 := bstep (se 2 (by rfl) ⟨543192, by rfl⟩ : syracuseStep 1448513 = 1086385) B1086385
theorem B2333249 : Blo 507795 2333249 := bstep (se 2 (by rfl) ⟨874968, by rfl⟩ : syracuseStep 2333249 = 1749937) B1749937
theorem B858775 : Blo 507795 858775 := bstep (se 1 (by rfl) ⟨644081, by rfl⟩ : syracuseStep 858775 = 1288163) B1288163
theorem B1547059 : Blo 507795 1547059 := bstep (se 1 (by rfl) ⟨1160294, by rfl⟩ : syracuseStep 1547059 = 2320589) B2320589
theorem B4201433 : Blo 507795 4201433 := bstep (se 2 (by rfl) ⟨1575537, by rfl⟩ : syracuseStep 4201433 = 3151075) B3151075
theorem B2169949 : Blo 507795 2169949 := bstep (se 3 (by rfl) ⟨406865, by rfl⟩ : syracuseStep 2169949 = 813731) B813731
theorem B728203 : Blo 507795 728203 := bstep (se 1 (by rfl) ⟨546152, by rfl⟩ : syracuseStep 728203 = 1092305) B1092305
theorem B859403 : Blo 507795 859403 := bstep (se 1 (by rfl) ⟨644552, by rfl⟩ : syracuseStep 859403 = 1289105) B1289105
theorem B1088819 : Blo 507795 1088819 := bstep (se 1 (by rfl) ⟨816614, by rfl⟩ : syracuseStep 1088819 = 1633229) B1633229
theorem B859531 : Blo 507795 859531 := bstep (se 1 (by rfl) ⟨644648, by rfl⟩ : syracuseStep 859531 = 1289297) B1289297
theorem B1088921 : Blo 507795 1088921 := bstep (se 2 (by rfl) ⟨408345, by rfl⟩ : syracuseStep 1088921 = 816691) B816691
theorem B859673 : Blo 507795 859673 := bstep (se 2 (by rfl) ⟨322377, by rfl⟩ : syracuseStep 859673 = 644755) B644755
theorem B990859 : Blo 507795 990859 := bstep (se 1 (by rfl) ⟨743144, by rfl⟩ : syracuseStep 990859 = 1486289) B1486289
theorem B859801 : Blo 507795 859801 := bstep (se 2 (by rfl) ⟨322425, by rfl⟩ : syracuseStep 859801 = 644851) B644851
theorem B1089281 : Blo 507795 1089281 := bstep (se 2 (by rfl) ⟨408480, by rfl⟩ : syracuseStep 1089281 = 816961) B816961
theorem B761753 : Blo 507795 761753 := bstep (se 2 (by rfl) ⟨285657, by rfl⟩ : syracuseStep 761753 = 571315) B571315
theorem B3678169 : Blo 507795 3678169 := bstep (se 2 (by rfl) ⟨1379313, by rfl⟩ : syracuseStep 3678169 = 2758627) B2758627
theorem B761867 : Blo 507795 761867 := bstep (se 1 (by rfl) ⟨571400, by rfl⟩ : syracuseStep 761867 = 1142801) B1142801
theorem B3317777 : Blo 507795 3317777 := bstep (se 2 (by rfl) ⟨1244166, by rfl⟩ : syracuseStep 3317777 = 2488333) B2488333
theorem B761879 : Blo 507795 761879 := bstep (se 1 (by rfl) ⟨571409, by rfl⟩ : syracuseStep 761879 = 1142819) B1142819
theorem B1286219 : Blo 507795 1286219 := bstep (se 1 (by rfl) ⟨964664, by rfl⟩ : syracuseStep 1286219 = 1929329) B1929329
theorem B761945 : Blo 507795 761945 := bstep (se 2 (by rfl) ⟨285729, by rfl⟩ : syracuseStep 761945 = 571459) B571459
theorem B1941677 : Blo 507795 1941677 := bstep (se 3 (by rfl) ⟨364064, by rfl⟩ : syracuseStep 1941677 = 728129) B728129
theorem B1450163 : Blo 507795 1450163 := bstep (se 1 (by rfl) ⟨1087622, by rfl⟩ : syracuseStep 1450163 = 2175245) B2175245
theorem B762059 : Blo 507795 762059 := bstep (se 1 (by rfl) ⟨571544, by rfl⟩ : syracuseStep 762059 = 1143089) B1143089
theorem B1450187 : Blo 507795 1450187 := bstep (se 1 (by rfl) ⟨1087640, by rfl⟩ : syracuseStep 1450187 = 2175281) B2175281
theorem B762071 : Blo 507795 762071 := bstep (se 1 (by rfl) ⟨571553, by rfl⟩ : syracuseStep 762071 = 1143107) B1143107
theorem B860375 : Blo 507795 860375 := bstep (se 1 (by rfl) ⟨645281, by rfl⟩ : syracuseStep 860375 = 1290563) B1290563
theorem B762137 : Blo 507795 762137 := bstep (se 2 (by rfl) ⟨285801, by rfl⟩ : syracuseStep 762137 = 571603) B571603
theorem B860503 : Blo 507795 860503 := bstep (se 1 (by rfl) ⟨645377, by rfl⟩ : syracuseStep 860503 = 1290755) B1290755
theorem B2892125 : Blo 507795 2892125 := bstep (se 3 (by rfl) ⟨542273, by rfl⟩ : syracuseStep 2892125 = 1084547) B1084547
theorem B762251 : Blo 507795 762251 := bstep (se 1 (by rfl) ⟨571688, by rfl⟩ : syracuseStep 762251 = 1143377) B1143377
theorem B2171281 : Blo 507795 2171281 := bstep (se 2 (by rfl) ⟨814230, by rfl⟩ : syracuseStep 2171281 = 1628461) B1628461
theorem B762263 : Blo 507795 762263 := bstep (se 1 (by rfl) ⟨571697, by rfl⟩ : syracuseStep 762263 = 1143395) B1143395
theorem B1090007 : Blo 507795 1090007 := bstep (se 1 (by rfl) ⟨817505, by rfl⟩ : syracuseStep 1090007 = 1635011) B1635011
theorem B762329 : Blo 507795 762329 := bstep (se 2 (by rfl) ⟨285873, by rfl⟩ : syracuseStep 762329 = 571747) B571747
theorem B3875363 : Blo 507795 3875363 := bstep (se 1 (by rfl) ⟨2906522, by rfl⟩ : syracuseStep 3875363 = 5813045) B5813045
theorem B762443 : Blo 507795 762443 := bstep (se 1 (by rfl) ⟨571832, by rfl⟩ : syracuseStep 762443 = 1143665) B1143665
theorem B762455 : Blo 507795 762455 := bstep (se 1 (by rfl) ⟨571841, by rfl⟩ : syracuseStep 762455 = 1143683) B1143683
theorem B762521 : Blo 507795 762521 := bstep (se 2 (by rfl) ⟨285945, by rfl⟩ : syracuseStep 762521 = 571891) B571891
theorem B762635 : Blo 507795 762635 := bstep (se 1 (by rfl) ⟨571976, by rfl⟩ : syracuseStep 762635 = 1143953) B1143953
theorem B762647 : Blo 507795 762647 := bstep (se 1 (by rfl) ⟨571985, by rfl⟩ : syracuseStep 762647 = 1143971) B1143971
theorem B762713 : Blo 507795 762713 := bstep (se 2 (by rfl) ⟨286017, by rfl⟩ : syracuseStep 762713 = 572035) B572035
theorem B1942451 : Blo 507795 1942451 := bstep (se 1 (by rfl) ⟨1456838, by rfl⟩ : syracuseStep 1942451 = 2913677) B2913677
theorem B762827 : Blo 507795 762827 := bstep (se 1 (by rfl) ⟨572120, by rfl⟩ : syracuseStep 762827 = 1144241) B1144241
theorem B861131 : Blo 507795 861131 := bstep (se 1 (by rfl) ⟨645848, by rfl⟩ : syracuseStep 861131 = 1291697) B1291697
theorem B762839 : Blo 507795 762839 := bstep (se 1 (by rfl) ⟨572129, by rfl⟩ : syracuseStep 762839 = 1144259) B1144259
theorem B1450973 : Blo 507795 1450973 := bstep (se 3 (by rfl) ⟨272057, by rfl⟩ : syracuseStep 1450973 = 544115) B544115
theorem B1287191 : Blo 507795 1287191 := bstep (se 1 (by rfl) ⟨965393, by rfl⟩ : syracuseStep 1287191 = 1930787) B1930787
theorem B762905 : Blo 507795 762905 := bstep (se 2 (by rfl) ⟨286089, by rfl⟩ : syracuseStep 762905 = 572179) B572179
theorem B861259 : Blo 507795 861259 := bstep (se 1 (by rfl) ⟨645944, by rfl⟩ : syracuseStep 861259 = 1291889) B1291889
theorem B763019 : Blo 507795 763019 := bstep (se 1 (by rfl) ⟨572264, by rfl⟩ : syracuseStep 763019 = 1144529) B1144529
theorem B763031 : Blo 507795 763031 := bstep (se 1 (by rfl) ⟨572273, by rfl⟩ : syracuseStep 763031 = 1144547) B1144547
theorem B763097 : Blo 507795 763097 := bstep (se 2 (by rfl) ⟨286161, by rfl⟩ : syracuseStep 763097 = 572323) B572323
theorem B861401 : Blo 507795 861401 := bstep (se 2 (by rfl) ⟨323025, by rfl⟩ : syracuseStep 861401 = 646051) B646051
theorem B4367681 : Blo 507795 4367681 := bstep (se 2 (by rfl) ⟨1637880, by rfl⟩ : syracuseStep 4367681 = 3275761) B3275761
theorem B763211 : Blo 507795 763211 := bstep (se 1 (by rfl) ⟨572408, by rfl⟩ : syracuseStep 763211 = 1144817) B1144817
theorem B763223 : Blo 507795 763223 := bstep (se 1 (by rfl) ⟨572417, by rfl⟩ : syracuseStep 763223 = 1144835) B1144835
theorem B1090903 : Blo 507795 1090903 := bstep (se 1 (by rfl) ⟨818177, by rfl⟩ : syracuseStep 1090903 = 1636355) B1636355
theorem B861529 : Blo 507795 861529 := bstep (se 2 (by rfl) ⟨323073, by rfl⟩ : syracuseStep 861529 = 646147) B646147
theorem B1746269 : Blo 507795 1746269 := bstep (se 3 (by rfl) ⟨327425, by rfl⟩ : syracuseStep 1746269 = 654851) B654851
theorem B763289 : Blo 507795 763289 := bstep (se 2 (by rfl) ⟨286233, by rfl⟩ : syracuseStep 763289 = 572467) B572467
theorem B8955353 : Blo 507795 8955353 := bstep (se 2 (by rfl) ⟨3358257, by rfl⟩ : syracuseStep 8955353 = 6716515) B6716515
theorem B763403 : Blo 507795 763403 := bstep (se 1 (by rfl) ⟨572552, by rfl⟩ : syracuseStep 763403 = 1145105) B1145105
theorem B763415 : Blo 507795 763415 := bstep (se 1 (by rfl) ⟨572561, by rfl⟩ : syracuseStep 763415 = 1145123) B1145123
theorem B763481 : Blo 507795 763481 := bstep (se 2 (by rfl) ⟨286305, by rfl⟩ : syracuseStep 763481 = 572611) B572611
theorem B1287859 : Blo 507795 1287859 := bstep (se 1 (by rfl) ⟨965894, by rfl⟩ : syracuseStep 1287859 = 1931789) B1931789
theorem B763595 : Blo 507795 763595 := bstep (se 1 (by rfl) ⟨572696, by rfl⟩ : syracuseStep 763595 = 1145393) B1145393
theorem B763607 : Blo 507795 763607 := bstep (se 1 (by rfl) ⟨572705, by rfl⟩ : syracuseStep 763607 = 1145411) B1145411
theorem B763673 : Blo 507795 763673 := bstep (se 2 (by rfl) ⟨286377, by rfl⟩ : syracuseStep 763673 = 572755) B572755
theorem B1288001 : Blo 507795 1288001 := bstep (se 2 (by rfl) ⟨483000, by rfl⟩ : syracuseStep 1288001 = 966001) B966001
theorem B2762561 : Blo 507795 2762561 := bstep (se 2 (by rfl) ⟨1035960, by rfl⟩ : syracuseStep 2762561 = 2071921) B2071921
theorem B1714013 : Blo 507795 1714013 := bstep (se 3 (by rfl) ⟨321377, by rfl⟩ : syracuseStep 1714013 = 642755) B642755
theorem B1550173 : Blo 507795 1550173 := bstep (se 3 (by rfl) ⟨290657, by rfl⟩ : syracuseStep 1550173 = 581315) B581315
theorem B763787 : Blo 507795 763787 := bstep (se 1 (by rfl) ⟨572840, by rfl⟩ : syracuseStep 763787 = 1145681) B1145681
theorem B763799 : Blo 507795 763799 := bstep (se 1 (by rfl) ⟨572849, by rfl⟩ : syracuseStep 763799 = 1145699) B1145699
theorem B862103 : Blo 507795 862103 := bstep (se 1 (by rfl) ⟨646577, by rfl⟩ : syracuseStep 862103 = 1293155) B1293155
theorem B763865 : Blo 507795 763865 := bstep (se 2 (by rfl) ⟨286449, by rfl⟩ : syracuseStep 763865 = 572899) B572899
theorem B862231 : Blo 507795 862231 := bstep (se 1 (by rfl) ⟨646673, by rfl⟩ : syracuseStep 862231 = 1293347) B1293347
theorem B763979 : Blo 507795 763979 := bstep (se 1 (by rfl) ⟨572984, by rfl⟩ : syracuseStep 763979 = 1145969) B1145969
theorem B763991 : Blo 507795 763991 := bstep (se 1 (by rfl) ⟨572993, by rfl⟩ : syracuseStep 763991 = 1145987) B1145987
theorem B1091723 : Blo 507795 1091723 := bstep (se 1 (by rfl) ⟨818792, by rfl⟩ : syracuseStep 1091723 = 1637585) B1637585
theorem B764057 : Blo 507795 764057 := bstep (se 2 (by rfl) ⟨286521, by rfl⟩ : syracuseStep 764057 = 573043) B573043
theorem B2074841 : Blo 507795 2074841 := bstep (se 2 (by rfl) ⟨778065, by rfl⟩ : syracuseStep 2074841 = 1556131) B1556131
theorem B764171 : Blo 507795 764171 := bstep (se 1 (by rfl) ⟨573128, by rfl⟩ : syracuseStep 764171 = 1146257) B1146257
theorem B764183 : Blo 507795 764183 := bstep (se 1 (by rfl) ⟨573137, by rfl⟩ : syracuseStep 764183 = 1146275) B1146275
theorem B764249 : Blo 507795 764249 := bstep (se 2 (by rfl) ⟨286593, by rfl⟩ : syracuseStep 764249 = 573187) B573187
theorem B764363 : Blo 507795 764363 := bstep (se 1 (by rfl) ⟨573272, by rfl⟩ : syracuseStep 764363 = 1146545) B1146545
theorem B764375 : Blo 507795 764375 := bstep (se 1 (by rfl) ⟨573281, by rfl⟩ : syracuseStep 764375 = 1146563) B1146563
theorem B1223191 : Blo 507795 1223191 := bstep (se 1 (by rfl) ⟨917393, by rfl⟩ : syracuseStep 1223191 = 1834787) B1834787
theorem B764441 : Blo 507795 764441 := bstep (se 2 (by rfl) ⟨286665, by rfl⟩ : syracuseStep 764441 = 573331) B573331
theorem B3254849 : Blo 507795 3254849 := bstep (se 2 (by rfl) ⟨1220568, by rfl⟩ : syracuseStep 3254849 = 2441137) B2441137
theorem B764555 : Blo 507795 764555 := bstep (se 1 (by rfl) ⟨573416, by rfl⟩ : syracuseStep 764555 = 1146833) B1146833
theorem B862859 : Blo 507795 862859 := bstep (se 1 (by rfl) ⟨647144, by rfl⟩ : syracuseStep 862859 = 1294289) B1294289
theorem B764567 : Blo 507795 764567 := bstep (se 1 (by rfl) ⟨573425, by rfl⟩ : syracuseStep 764567 = 1146851) B1146851
theorem B764633 : Blo 507795 764633 := bstep (se 2 (by rfl) ⟨286737, by rfl⟩ : syracuseStep 764633 = 573475) B573475
theorem B1452761 : Blo 507795 1452761 := bstep (se 2 (by rfl) ⟨544785, by rfl⟩ : syracuseStep 1452761 = 1089571) B1089571
theorem B862987 : Blo 507795 862987 := bstep (se 1 (by rfl) ⟨647240, by rfl⟩ : syracuseStep 862987 = 1294481) B1294481
theorem B764747 : Blo 507795 764747 := bstep (se 1 (by rfl) ⟨573560, by rfl⟩ : syracuseStep 764747 = 1147121) B1147121
theorem B764759 : Blo 507795 764759 := bstep (se 1 (by rfl) ⟨573569, by rfl⟩ : syracuseStep 764759 = 1147139) B1147139
theorem B1092467 : Blo 507795 1092467 := bstep (se 1 (by rfl) ⟨819350, by rfl⟩ : syracuseStep 1092467 = 1638701) B1638701
theorem B2894723 : Blo 507795 2894723 := bstep (se 1 (by rfl) ⟨2171042, by rfl⟩ : syracuseStep 2894723 = 4342085) B4342085
theorem B3025795 : Blo 507795 3025795 := bstep (se 1 (by rfl) ⟨2269346, by rfl⟩ : syracuseStep 3025795 = 4538693) B4538693
theorem B764825 : Blo 507795 764825 := bstep (se 2 (by rfl) ⟨286809, by rfl⟩ : syracuseStep 764825 = 573619) B573619
theorem B863129 : Blo 507795 863129 := bstep (se 2 (by rfl) ⟨323673, by rfl⟩ : syracuseStep 863129 = 647347) B647347
theorem B1715147 : Blo 507795 1715147 := bstep (se 1 (by rfl) ⟨1286360, by rfl⟩ : syracuseStep 1715147 = 2572721) B2572721
theorem B764939 : Blo 507795 764939 := bstep (se 1 (by rfl) ⟨573704, by rfl⟩ : syracuseStep 764939 = 1147409) B1147409
theorem B764951 : Blo 507795 764951 := bstep (se 1 (by rfl) ⟨573713, by rfl⟩ : syracuseStep 764951 = 1147427) B1147427
theorem B1453079 : Blo 507795 1453079 := bstep (se 1 (by rfl) ⟨1089809, by rfl⟩ : syracuseStep 1453079 = 2179619) B2179619
theorem B863257 : Blo 507795 863257 := bstep (se 2 (by rfl) ⟨323721, by rfl⟩ : syracuseStep 863257 = 647443) B647443
theorem B1289267 : Blo 507795 1289267 := bstep (se 1 (by rfl) ⟨966950, by rfl⟩ : syracuseStep 1289267 = 1933901) B1933901
theorem B765017 : Blo 507795 765017 := bstep (se 2 (by rfl) ⟨286881, by rfl⟩ : syracuseStep 765017 = 573763) B573763
theorem B2174045 : Blo 507795 2174045 := bstep (se 3 (by rfl) ⟨407633, by rfl⟩ : syracuseStep 2174045 = 815267) B815267
theorem B765131 : Blo 507795 765131 := bstep (se 1 (by rfl) ⟨573848, by rfl⟩ : syracuseStep 765131 = 1147697) B1147697
theorem B1748171 : Blo 507795 1748171 := bstep (se 1 (by rfl) ⟨1311128, by rfl⟩ : syracuseStep 1748171 = 2622257) B2622257
theorem B765143 : Blo 507795 765143 := bstep (se 1 (by rfl) ⟨573857, by rfl⟩ : syracuseStep 765143 = 1147715) B1147715
theorem B1715417 : Blo 507795 1715417 := bstep (se 2 (by rfl) ⟨643281, by rfl⟩ : syracuseStep 1715417 = 1286563) B1286563
theorem B3681541 : Blo 507795 3681541 := bstep (se 4 (by rfl) ⟨345144, by rfl⟩ : syracuseStep 3681541 = 690289) B690289
theorem B6991109 : Blo 507795 6991109 := bstep (se 4 (by rfl) ⟨655416, by rfl⟩ : syracuseStep 6991109 = 1310833) B1310833
theorem B765209 : Blo 507795 765209 := bstep (se 2 (by rfl) ⟨286953, by rfl⟩ : syracuseStep 765209 = 573907) B573907
theorem B2174273 : Blo 507795 2174273 := bstep (se 2 (by rfl) ⟨815352, by rfl⟩ : syracuseStep 2174273 = 1630705) B1630705
theorem B765323 : Blo 507795 765323 := bstep (se 1 (by rfl) ⟨573992, by rfl⟩ : syracuseStep 765323 = 1147985) B1147985
theorem B765335 : Blo 507795 765335 := bstep (se 1 (by rfl) ⟨574001, by rfl⟩ : syracuseStep 765335 = 1148003) B1148003
theorem B4140467 : Blo 507795 4140467 := bstep (se 1 (by rfl) ⟨3105350, by rfl⟩ : syracuseStep 4140467 = 6210701) B6210701
theorem B765401 : Blo 507795 765401 := bstep (se 2 (by rfl) ⟨287025, by rfl⟩ : syracuseStep 765401 = 574051) B574051
theorem B1289803 : Blo 507795 1289803 := bstep (se 1 (by rfl) ⟨967352, by rfl⟩ : syracuseStep 1289803 = 1934705) B1934705
theorem B765515 : Blo 507795 765515 := bstep (se 1 (by rfl) ⟨574136, by rfl⟩ : syracuseStep 765515 = 1148273) B1148273
theorem B765527 : Blo 507795 765527 := bstep (se 1 (by rfl) ⟨574145, by rfl⟩ : syracuseStep 765527 = 1148291) B1148291
theorem B765593 : Blo 507795 765593 := bstep (se 2 (by rfl) ⟨287097, by rfl⟩ : syracuseStep 765593 = 574195) B574195
theorem B1289945 : Blo 507795 1289945 := bstep (se 2 (by rfl) ⟨483729, by rfl⟩ : syracuseStep 1289945 = 967459) B967459
theorem B765707 : Blo 507795 765707 := bstep (se 1 (by rfl) ⟨574280, by rfl⟩ : syracuseStep 765707 = 1148561) B1148561
theorem B765719 : Blo 507795 765719 := bstep (se 1 (by rfl) ⟨574289, by rfl⟩ : syracuseStep 765719 = 1148579) B1148579
theorem B1453889 : Blo 507795 1453889 := bstep (se 2 (by rfl) ⟨545208, by rfl⟩ : syracuseStep 1453889 = 1090417) B1090417
theorem B765785 : Blo 507795 765785 := bstep (se 2 (by rfl) ⟨287169, by rfl⟩ : syracuseStep 765785 = 574339) B574339
theorem B2764637 : Blo 507795 2764637 := bstep (se 3 (by rfl) ⟨518369, by rfl⟩ : syracuseStep 2764637 = 1036739) B1036739
theorem B1716119 : Blo 507795 1716119 := bstep (se 1 (by rfl) ⟨1287089, by rfl⟩ : syracuseStep 1716119 = 2574179) B2574179
theorem B25472945 : Blo 507795 25472945 := bstep (se 2 (by rfl) ⟨9552354, by rfl⟩ : syracuseStep 25472945 = 19104709) B19104709
theorem B765899 : Blo 507795 765899 := bstep (se 1 (by rfl) ⟨574424, by rfl⟩ : syracuseStep 765899 = 1148849) B1148849
theorem B765911 : Blo 507795 765911 := bstep (se 1 (by rfl) ⟨574433, by rfl⟩ : syracuseStep 765911 = 1148867) B1148867
theorem B765977 : Blo 507795 765977 := bstep (se 2 (by rfl) ⟨287241, by rfl⟩ : syracuseStep 765977 = 574483) B574483
theorem B766091 : Blo 507795 766091 := bstep (se 1 (by rfl) ⟨574568, by rfl⟩ : syracuseStep 766091 = 1149137) B1149137
theorem B766103 : Blo 507795 766103 := bstep (se 1 (by rfl) ⟨574577, by rfl⟩ : syracuseStep 766103 = 1149155) B1149155
theorem B766169 : Blo 507795 766169 := bstep (se 2 (by rfl) ⟨287313, by rfl⟩ : syracuseStep 766169 = 574627) B574627
theorem B995585 : Blo 507795 995585 := bstep (se 2 (by rfl) ⟨373344, by rfl⟩ : syracuseStep 995585 = 746689) B746689
theorem B766283 : Blo 507795 766283 := bstep (se 1 (by rfl) ⟨574712, by rfl⟩ : syracuseStep 766283 = 1149425) B1149425
theorem B766295 : Blo 507795 766295 := bstep (se 1 (by rfl) ⟨574721, by rfl⟩ : syracuseStep 766295 = 1149443) B1149443
theorem B766361 : Blo 507795 766361 := bstep (se 2 (by rfl) ⟨287385, by rfl⟩ : syracuseStep 766361 = 574771) B574771
theorem B1716659 : Blo 507795 1716659 := bstep (se 1 (by rfl) ⟨1287494, by rfl⟩ : syracuseStep 1716659 = 2574989) B2574989
theorem B766475 : Blo 507795 766475 := bstep (se 1 (by rfl) ⟨574856, by rfl⟩ : syracuseStep 766475 = 1149713) B1149713
theorem B1290775 : Blo 507795 1290775 := bstep (se 1 (by rfl) ⟨968081, by rfl⟩ : syracuseStep 1290775 = 1936163) B1936163
theorem B766487 : Blo 507795 766487 := bstep (se 1 (by rfl) ⟨574865, by rfl⟩ : syracuseStep 766487 = 1149731) B1149731
theorem B766553 : Blo 507795 766553 := bstep (se 2 (by rfl) ⟨287457, by rfl⟩ : syracuseStep 766553 = 574915) B574915
theorem B1716929 : Blo 507795 1716929 := bstep (se 2 (by rfl) ⟨643848, by rfl⟩ : syracuseStep 1716929 = 1287697) B1287697
theorem B766667 : Blo 507795 766667 := bstep (se 1 (by rfl) ⟨575000, by rfl⟩ : syracuseStep 766667 = 1150001) B1150001
theorem B766679 : Blo 507795 766679 := bstep (se 1 (by rfl) ⟨575009, by rfl⟩ : syracuseStep 766679 = 1150019) B1150019
theorem B766745 : Blo 507795 766745 := bstep (se 2 (by rfl) ⟨287529, by rfl⟩ : syracuseStep 766745 = 575059) B575059
theorem B1160075 : Blo 507795 1160075 := bstep (se 1 (by rfl) ⟨870056, by rfl⟩ : syracuseStep 1160075 = 1740113) B1740113
theorem B766859 : Blo 507795 766859 := bstep (se 1 (by rfl) ⟨575144, by rfl⟩ : syracuseStep 766859 = 1150289) B1150289
theorem B766871 : Blo 507795 766871 := bstep (se 1 (by rfl) ⟨575153, by rfl⟩ : syracuseStep 766871 = 1150307) B1150307
theorem B1291211 : Blo 507795 1291211 := bstep (se 1 (by rfl) ⟨968408, by rfl⟩ : syracuseStep 1291211 = 1936817) B1936817
theorem B766937 : Blo 507795 766937 := bstep (se 2 (by rfl) ⟨287601, by rfl⟩ : syracuseStep 766937 = 575203) B575203
theorem B767051 : Blo 507795 767051 := bstep (se 1 (by rfl) ⟨575288, by rfl⟩ : syracuseStep 767051 = 1150577) B1150577
theorem B767063 : Blo 507795 767063 := bstep (se 1 (by rfl) ⟨575297, by rfl⟩ : syracuseStep 767063 = 1150595) B1150595
theorem B767129 : Blo 507795 767129 := bstep (se 2 (by rfl) ⟨287673, by rfl⟩ : syracuseStep 767129 = 575347) B575347
theorem B1651915 : Blo 507795 1651915 := bstep (se 1 (by rfl) ⟨1238936, by rfl⟩ : syracuseStep 1651915 = 2477873) B2477873
theorem B1717469 : Blo 507795 1717469 := bstep (se 3 (by rfl) ⟨322025, by rfl⟩ : syracuseStep 1717469 = 644051) B644051
theorem B767243 : Blo 507795 767243 := bstep (se 1 (by rfl) ⟨575432, by rfl⟩ : syracuseStep 767243 = 1150865) B1150865
theorem B767255 : Blo 507795 767255 := bstep (se 1 (by rfl) ⟨575441, by rfl⟩ : syracuseStep 767255 = 1150883) B1150883
theorem B1291585 : Blo 507795 1291585 := bstep (se 2 (by rfl) ⟨484344, by rfl⟩ : syracuseStep 1291585 = 968689) B968689
theorem B767321 : Blo 507795 767321 := bstep (se 2 (by rfl) ⟨287745, by rfl⟩ : syracuseStep 767321 = 575491) B575491
theorem B1553843 : Blo 507795 1553843 := bstep (se 1 (by rfl) ⟨1165382, by rfl⟩ : syracuseStep 1553843 = 2330765) B2330765
theorem B1455563 : Blo 507795 1455563 := bstep (se 1 (by rfl) ⟨1091672, by rfl⟩ : syracuseStep 1455563 = 2183345) B2183345
theorem B767435 : Blo 507795 767435 := bstep (se 1 (by rfl) ⟨575576, by rfl⟩ : syracuseStep 767435 = 1151153) B1151153
theorem B767447 : Blo 507795 767447 := bstep (se 1 (by rfl) ⟨575585, by rfl⟩ : syracuseStep 767447 = 1151171) B1151171
theorem B964057 : Blo 507795 964057 := bstep (se 2 (by rfl) ⟨361521, by rfl⟩ : syracuseStep 964057 = 723043) B723043
theorem B767513 : Blo 507795 767513 := bstep (se 2 (by rfl) ⟨287817, by rfl⟩ : syracuseStep 767513 = 575635) B575635
theorem B767627 : Blo 507795 767627 := bstep (se 1 (by rfl) ⟨575720, by rfl⟩ : syracuseStep 767627 = 1151441) B1151441
theorem B997015 : Blo 507795 997015 := bstep (se 1 (by rfl) ⟨747761, by rfl⟩ : syracuseStep 997015 = 1495523) B1495523
theorem B767639 : Blo 507795 767639 := bstep (se 1 (by rfl) ⟨575729, by rfl⟩ : syracuseStep 767639 = 1151459) B1151459
theorem B2176733 : Blo 507795 2176733 := bstep (se 3 (by rfl) ⟨408137, by rfl⟩ : syracuseStep 2176733 = 816275) B816275
theorem B3880709 : Blo 507795 3880709 := bstep (se 4 (by rfl) ⟨363816, by rfl⟩ : syracuseStep 3880709 = 727633) B727633
theorem B1292183 : Blo 507795 1292183 := bstep (se 1 (by rfl) ⟨969137, by rfl⟩ : syracuseStep 1292183 = 1938275) B1938275
theorem B571351 : Blo 507795 571351 := bstep (se 1 (by rfl) ⟨428513, by rfl⟩ : syracuseStep 571351 = 857027) B857027
theorem B964619 : Blo 507795 964619 := bstep (se 1 (by rfl) ⟨723464, by rfl⟩ : syracuseStep 964619 = 1446929) B1446929
theorem B571531 : Blo 507795 571531 := bstep (se 1 (by rfl) ⟨428648, by rfl⟩ : syracuseStep 571531 = 857297) B857297
theorem B964801 : Blo 507795 964801 := bstep (se 2 (by rfl) ⟨361800, by rfl⟩ : syracuseStep 964801 = 723601) B723601
theorem B571639 : Blo 507795 571639 := bstep (se 1 (by rfl) ⟨428729, by rfl⟩ : syracuseStep 571639 = 857459) B857459
theorem B1718603 : Blo 507795 1718603 := bstep (se 1 (by rfl) ⟨1288952, by rfl⟩ : syracuseStep 1718603 = 2577905) B2577905
theorem B571819 : Blo 507795 571819 := bstep (se 1 (by rfl) ⟨428864, by rfl⟩ : syracuseStep 571819 = 857729) B857729
theorem B571927 : Blo 507795 571927 := bstep (se 1 (by rfl) ⟨428945, by rfl⟩ : syracuseStep 571927 = 857891) B857891
theorem B1227287 : Blo 507795 1227287 := bstep (se 1 (by rfl) ⟨920465, by rfl⟩ : syracuseStep 1227287 = 1840931) B1840931
theorem B1718873 : Blo 507795 1718873 := bstep (se 2 (by rfl) ⟨644577, by rfl⟩ : syracuseStep 1718873 = 1289155) B1289155
theorem B4340375 : Blo 507795 4340375 := bstep (se 1 (by rfl) ⟨3255281, by rfl⟩ : syracuseStep 4340375 = 6510563) B6510563
theorem B1292993 : Blo 507795 1292993 := bstep (se 2 (by rfl) ⟨484872, by rfl⟩ : syracuseStep 1292993 = 969745) B969745
theorem B572107 : Blo 507795 572107 := bstep (se 1 (by rfl) ⟨429080, by rfl⟩ : syracuseStep 572107 = 858161) B858161
theorem B1456861 : Blo 507795 1456861 := bstep (se 3 (by rfl) ⟨273161, by rfl⟩ : syracuseStep 1456861 = 546323) B546323
theorem B572215 : Blo 507795 572215 := bstep (se 1 (by rfl) ⟨429161, by rfl⟩ : syracuseStep 572215 = 858323) B858323
theorem B2571101 : Blo 507795 2571101 := bstep (se 3 (by rfl) ⟨482081, by rfl⟩ : syracuseStep 2571101 = 964163) B964163
theorem B965515 : Blo 507795 965515 := bstep (se 1 (by rfl) ⟨724136, by rfl⟩ : syracuseStep 965515 = 1448273) B1448273
theorem B965591 : Blo 507795 965591 := bstep (se 1 (by rfl) ⟨724193, by rfl⟩ : syracuseStep 965591 = 1448387) B1448387
theorem B572395 : Blo 507795 572395 := bstep (se 1 (by rfl) ⟨429296, by rfl⟩ : syracuseStep 572395 = 858593) B858593
theorem B1457203 : Blo 507795 1457203 := bstep (se 1 (by rfl) ⟨1092902, by rfl⟩ : syracuseStep 1457203 = 2185805) B2185805
theorem B572503 : Blo 507795 572503 := bstep (se 1 (by rfl) ⟨429377, by rfl⟩ : syracuseStep 572503 = 858755) B858755
theorem B1293529 : Blo 507795 1293529 := bstep (se 2 (by rfl) ⟨485073, by rfl⟩ : syracuseStep 1293529 = 970147) B970147
theorem B572683 : Blo 507795 572683 := bstep (se 1 (by rfl) ⟨429512, by rfl⟩ : syracuseStep 572683 = 859025) B859025
theorem B1719575 : Blo 507795 1719575 := bstep (se 1 (by rfl) ⟨1289681, by rfl⟩ : syracuseStep 1719575 = 2579363) B2579363
theorem B572791 : Blo 507795 572791 := bstep (se 1 (by rfl) ⟨429593, by rfl⟩ : syracuseStep 572791 = 859187) B859187
theorem B572971 : Blo 507795 572971 := bstep (se 1 (by rfl) ⟨429728, by rfl⟩ : syracuseStep 572971 = 859457) B859457
theorem B3259997 : Blo 507795 3259997 := bstep (se 3 (by rfl) ⟨611249, by rfl⟩ : syracuseStep 3259997 = 1222499) B1222499
theorem B966259 : Blo 507795 966259 := bstep (se 1 (by rfl) ⟨724694, by rfl⟩ : syracuseStep 966259 = 1449389) B1449389
theorem B573079 : Blo 507795 573079 := bstep (se 1 (by rfl) ⟨429809, by rfl⟩ : syracuseStep 573079 = 859619) B859619
theorem B3489581 : Blo 507795 3489581 := bstep (se 3 (by rfl) ⟨654296, by rfl⟩ : syracuseStep 3489581 = 1308593) B1308593
theorem B1720115 : Blo 507795 1720115 := bstep (se 1 (by rfl) ⟨1290086, by rfl⟩ : syracuseStep 1720115 = 2580173) B2580173
theorem B573259 : Blo 507795 573259 := bstep (se 1 (by rfl) ⟨429944, by rfl⟩ : syracuseStep 573259 = 859889) B859889
theorem B966487 : Blo 507795 966487 := bstep (se 1 (by rfl) ⟨724865, by rfl⟩ : syracuseStep 966487 = 1449731) B1449731
theorem B507799 : Blo 507795 507799 := bstep (se 1 (by rfl) ⟨380849, by rfl⟩ : syracuseStep 507799 = 761699) B761699
theorem B507819 : Blo 507795 507819 := bstep (se 1 (by rfl) ⟨380864, by rfl⟩ : syracuseStep 507819 = 761729) B761729
theorem B507831 : Blo 507795 507831 := bstep (se 1 (by rfl) ⟨380873, by rfl⟩ : syracuseStep 507831 = 761747) B761747
theorem B573367 : Blo 507795 573367 := bstep (se 1 (by rfl) ⟨430025, by rfl⟩ : syracuseStep 573367 = 860051) B860051
theorem B966593 : Blo 507795 966593 := bstep (se 2 (by rfl) ⟨362472, by rfl⟩ : syracuseStep 966593 = 724945) B724945
theorem B507851 : Blo 507795 507851 := bstep (se 1 (by rfl) ⟨380888, by rfl⟩ : syracuseStep 507851 = 761777) B761777
theorem B507863 : Blo 507795 507863 := bstep (se 1 (by rfl) ⟨380897, by rfl⟩ : syracuseStep 507863 = 761795) B761795
theorem B507883 : Blo 507795 507883 := bstep (se 1 (by rfl) ⟨380912, by rfl⟩ : syracuseStep 507883 = 761825) B761825
theorem B507895 : Blo 507795 507895 := bstep (se 1 (by rfl) ⟨380921, by rfl⟩ : syracuseStep 507895 = 761843) B761843
theorem B507915 : Blo 507795 507915 := bstep (se 1 (by rfl) ⟨380936, by rfl⟩ : syracuseStep 507915 = 761873) B761873
theorem B507927 : Blo 507795 507927 := bstep (se 1 (by rfl) ⟨380945, by rfl⟩ : syracuseStep 507927 = 761891) B761891
theorem B507947 : Blo 507795 507947 := bstep (se 1 (by rfl) ⟨380960, by rfl⟩ : syracuseStep 507947 = 761921) B761921
theorem B507959 : Blo 507795 507959 := bstep (se 1 (by rfl) ⟨380969, by rfl⟩ : syracuseStep 507959 = 761939) B761939
theorem B1032257 : Blo 507795 1032257 := bstep (se 2 (by rfl) ⟨387096, by rfl⟩ : syracuseStep 1032257 = 774193) B774193
theorem B1720385 : Blo 507795 1720385 := bstep (se 2 (by rfl) ⟨645144, by rfl⟩ : syracuseStep 1720385 = 1290289) B1290289
theorem B507979 : Blo 507795 507979 := bstep (se 1 (by rfl) ⟨380984, by rfl⟩ : syracuseStep 507979 = 761969) B761969
theorem B507991 : Blo 507795 507991 := bstep (se 1 (by rfl) ⟨380993, by rfl⟩ : syracuseStep 507991 = 761987) B761987
theorem B966745 : Blo 507795 966745 := bstep (se 2 (by rfl) ⟨362529, by rfl⟩ : syracuseStep 966745 = 725059) B725059
theorem B508011 : Blo 507795 508011 := bstep (se 1 (by rfl) ⟨381008, by rfl⟩ : syracuseStep 508011 = 762017) B762017
theorem B573547 : Blo 507795 573547 := bstep (se 1 (by rfl) ⟨430160, by rfl⟩ : syracuseStep 573547 = 860321) B860321
theorem B508023 : Blo 507795 508023 := bstep (se 1 (by rfl) ⟨381017, by rfl⟩ : syracuseStep 508023 = 762035) B762035
theorem B3883139 : Blo 507795 3883139 := bstep (se 1 (by rfl) ⟨2912354, by rfl⟩ : syracuseStep 3883139 = 5824709) B5824709
theorem B508043 : Blo 507795 508043 := bstep (se 1 (by rfl) ⟨381032, by rfl⟩ : syracuseStep 508043 = 762065) B762065
theorem B2474135 : Blo 507795 2474135 := bstep (se 1 (by rfl) ⟨1855601, by rfl⟩ : syracuseStep 2474135 = 3711203) B3711203
theorem B508055 : Blo 507795 508055 := bstep (se 1 (by rfl) ⟨381041, by rfl⟩ : syracuseStep 508055 = 762083) B762083
theorem B508075 : Blo 507795 508075 := bstep (se 1 (by rfl) ⟨381056, by rfl⟩ : syracuseStep 508075 = 762113) B762113
theorem B508087 : Blo 507795 508087 := bstep (se 1 (by rfl) ⟨381065, by rfl⟩ : syracuseStep 508087 = 762131) B762131
theorem B508107 : Blo 507795 508107 := bstep (se 1 (by rfl) ⟨381080, by rfl⟩ : syracuseStep 508107 = 762161) B762161
theorem B508119 : Blo 507795 508119 := bstep (se 1 (by rfl) ⟨381089, by rfl⟩ : syracuseStep 508119 = 762179) B762179
theorem B573655 : Blo 507795 573655 := bstep (se 1 (by rfl) ⟨430241, by rfl⟩ : syracuseStep 573655 = 860483) B860483
theorem B508139 : Blo 507795 508139 := bstep (se 1 (by rfl) ⟨381104, by rfl⟩ : syracuseStep 508139 = 762209) B762209
theorem B508151 : Blo 507795 508151 := bstep (se 1 (by rfl) ⟨381113, by rfl⟩ : syracuseStep 508151 = 762227) B762227
theorem B2179331 : Blo 507795 2179331 := bstep (se 1 (by rfl) ⟨1634498, by rfl⟩ : syracuseStep 2179331 = 3268997) B3268997
theorem B508171 : Blo 507795 508171 := bstep (se 1 (by rfl) ⟨381128, by rfl⟩ : syracuseStep 508171 = 762257) B762257
theorem B508183 : Blo 507795 508183 := bstep (se 1 (by rfl) ⟨381137, by rfl⟩ : syracuseStep 508183 = 762275) B762275
theorem B508203 : Blo 507795 508203 := bstep (se 1 (by rfl) ⟨381152, by rfl⟩ : syracuseStep 508203 = 762305) B762305
theorem B1294643 : Blo 507795 1294643 := bstep (se 1 (by rfl) ⟨970982, by rfl⟩ : syracuseStep 1294643 = 1941965) B1941965
theorem B508215 : Blo 507795 508215 := bstep (se 1 (by rfl) ⟨381161, by rfl⟩ : syracuseStep 508215 = 762323) B762323
theorem B508235 : Blo 507795 508235 := bstep (se 1 (by rfl) ⟨381176, by rfl⟩ : syracuseStep 508235 = 762353) B762353
theorem B508247 : Blo 507795 508247 := bstep (se 1 (by rfl) ⟨381185, by rfl⟩ : syracuseStep 508247 = 762371) B762371
theorem B508267 : Blo 507795 508267 := bstep (se 1 (by rfl) ⟨381200, by rfl⟩ : syracuseStep 508267 = 762401) B762401
theorem B508279 : Blo 507795 508279 := bstep (se 1 (by rfl) ⟨381209, by rfl⟩ : syracuseStep 508279 = 762419) B762419
theorem B508299 : Blo 507795 508299 := bstep (se 1 (by rfl) ⟨381224, by rfl⟩ : syracuseStep 508299 = 762449) B762449
theorem B573835 : Blo 507795 573835 := bstep (se 1 (by rfl) ⟨430376, by rfl⟩ : syracuseStep 573835 = 860753) B860753
theorem B508311 : Blo 507795 508311 := bstep (se 1 (by rfl) ⟨381233, by rfl⟩ : syracuseStep 508311 = 762467) B762467
theorem B508331 : Blo 507795 508331 := bstep (se 1 (by rfl) ⟨381248, by rfl⟩ : syracuseStep 508331 = 762497) B762497
theorem B508343 : Blo 507795 508343 := bstep (se 1 (by rfl) ⟨381257, by rfl⟩ : syracuseStep 508343 = 762515) B762515
theorem B508363 : Blo 507795 508363 := bstep (se 1 (by rfl) ⟨381272, by rfl⟩ : syracuseStep 508363 = 762545) B762545
theorem B508375 : Blo 507795 508375 := bstep (se 1 (by rfl) ⟨381281, by rfl⟩ : syracuseStep 508375 = 762563) B762563
theorem B508395 : Blo 507795 508395 := bstep (se 1 (by rfl) ⟨381296, by rfl⟩ : syracuseStep 508395 = 762593) B762593
theorem B508407 : Blo 507795 508407 := bstep (se 1 (by rfl) ⟨381305, by rfl⟩ : syracuseStep 508407 = 762611) B762611
theorem B573943 : Blo 507795 573943 := bstep (se 1 (by rfl) ⟨430457, by rfl⟩ : syracuseStep 573943 = 860915) B860915
theorem B508427 : Blo 507795 508427 := bstep (se 1 (by rfl) ⟨381320, by rfl⟩ : syracuseStep 508427 = 762641) B762641
theorem B508439 : Blo 507795 508439 := bstep (se 1 (by rfl) ⟨381329, by rfl⟩ : syracuseStep 508439 = 762659) B762659
theorem B508459 : Blo 507795 508459 := bstep (se 1 (by rfl) ⟨381344, by rfl⟩ : syracuseStep 508459 = 762689) B762689
theorem B1229363 : Blo 507795 1229363 := bstep (se 1 (by rfl) ⟨922022, by rfl⟩ : syracuseStep 1229363 = 1844045) B1844045
theorem B508471 : Blo 507795 508471 := bstep (se 1 (by rfl) ⟨381353, by rfl⟩ : syracuseStep 508471 = 762707) B762707
theorem B508491 : Blo 507795 508491 := bstep (se 1 (by rfl) ⟨381368, by rfl⟩ : syracuseStep 508491 = 762737) B762737
theorem B2900555 : Blo 507795 2900555 := bstep (se 1 (by rfl) ⟨2175416, by rfl⟩ : syracuseStep 2900555 = 4350833) B4350833
theorem B508503 : Blo 507795 508503 := bstep (se 1 (by rfl) ⟨381377, by rfl⟩ : syracuseStep 508503 = 762755) B762755
theorem B1294937 : Blo 507795 1294937 := bstep (se 2 (by rfl) ⟨485601, by rfl⟩ : syracuseStep 1294937 = 971203) B971203
theorem B1720925 : Blo 507795 1720925 := bstep (se 3 (by rfl) ⟨322673, by rfl⟩ : syracuseStep 1720925 = 645347) B645347
theorem B508523 : Blo 507795 508523 := bstep (se 1 (by rfl) ⟨381392, by rfl⟩ : syracuseStep 508523 = 762785) B762785
theorem B508535 : Blo 507795 508535 := bstep (se 1 (by rfl) ⟨381401, by rfl⟩ : syracuseStep 508535 = 762803) B762803
theorem B508555 : Blo 507795 508555 := bstep (se 1 (by rfl) ⟨381416, by rfl⟩ : syracuseStep 508555 = 762833) B762833
theorem B508567 : Blo 507795 508567 := bstep (se 1 (by rfl) ⟨381425, by rfl⟩ : syracuseStep 508567 = 762851) B762851
theorem B508587 : Blo 507795 508587 := bstep (se 1 (by rfl) ⟨381440, by rfl⟩ : syracuseStep 508587 = 762881) B762881
theorem B574123 : Blo 507795 574123 := bstep (se 1 (by rfl) ⟨430592, by rfl⟩ : syracuseStep 574123 = 861185) B861185
theorem B508599 : Blo 507795 508599 := bstep (se 1 (by rfl) ⟨381449, by rfl⟩ : syracuseStep 508599 = 762899) B762899
theorem B508619 : Blo 507795 508619 := bstep (se 1 (by rfl) ⟨381464, by rfl⟩ : syracuseStep 508619 = 762929) B762929
theorem B508631 : Blo 507795 508631 := bstep (se 1 (by rfl) ⟨381473, by rfl⟩ : syracuseStep 508631 = 762947) B762947
theorem B508651 : Blo 507795 508651 := bstep (se 1 (by rfl) ⟨381488, by rfl⟩ : syracuseStep 508651 = 762977) B762977
theorem B508663 : Blo 507795 508663 := bstep (se 1 (by rfl) ⟨381497, by rfl⟩ : syracuseStep 508663 = 762995) B762995
theorem B508683 : Blo 507795 508683 := bstep (se 1 (by rfl) ⟨381512, by rfl⟩ : syracuseStep 508683 = 763025) B763025
theorem B508695 : Blo 507795 508695 := bstep (se 1 (by rfl) ⟨381521, by rfl⟩ : syracuseStep 508695 = 763043) B763043
theorem B574231 : Blo 507795 574231 := bstep (se 1 (by rfl) ⟨430673, by rfl⟩ : syracuseStep 574231 = 861347) B861347
theorem B508715 : Blo 507795 508715 := bstep (se 1 (by rfl) ⟨381536, by rfl⟩ : syracuseStep 508715 = 763073) B763073
theorem B508727 : Blo 507795 508727 := bstep (se 1 (by rfl) ⟨381545, by rfl⟩ : syracuseStep 508727 = 763091) B763091
theorem B2442059 : Blo 507795 2442059 := bstep (se 1 (by rfl) ⟨1831544, by rfl⟩ : syracuseStep 2442059 = 3663089) B3663089
theorem B508747 : Blo 507795 508747 := bstep (se 1 (by rfl) ⟨381560, by rfl⟩ : syracuseStep 508747 = 763121) B763121
theorem B508759 : Blo 507795 508759 := bstep (se 1 (by rfl) ⟨381569, by rfl⟩ : syracuseStep 508759 = 763139) B763139
theorem B508779 : Blo 507795 508779 := bstep (se 1 (by rfl) ⟨381584, by rfl⟩ : syracuseStep 508779 = 763169) B763169
theorem B508791 : Blo 507795 508791 := bstep (se 1 (by rfl) ⟨381593, by rfl⟩ : syracuseStep 508791 = 763187) B763187
theorem B508811 : Blo 507795 508811 := bstep (se 1 (by rfl) ⟨381608, by rfl⟩ : syracuseStep 508811 = 763217) B763217
theorem B2573207 : Blo 507795 2573207 := bstep (se 1 (by rfl) ⟨1929905, by rfl⟩ : syracuseStep 2573207 = 3859811) B3859811
theorem B508823 : Blo 507795 508823 := bstep (se 1 (by rfl) ⟨381617, by rfl⟩ : syracuseStep 508823 = 763235) B763235
theorem B508843 : Blo 507795 508843 := bstep (se 1 (by rfl) ⟨381632, by rfl⟩ : syracuseStep 508843 = 763265) B763265
theorem B508855 : Blo 507795 508855 := bstep (se 1 (by rfl) ⟨381641, by rfl⟩ : syracuseStep 508855 = 763283) B763283
theorem B508875 : Blo 507795 508875 := bstep (se 1 (by rfl) ⟨381656, by rfl⟩ : syracuseStep 508875 = 763313) B763313
theorem B574411 : Blo 507795 574411 := bstep (se 1 (by rfl) ⟨430808, by rfl⟩ : syracuseStep 574411 = 861617) B861617
theorem B508887 : Blo 507795 508887 := bstep (se 1 (by rfl) ⟨381665, by rfl⟩ : syracuseStep 508887 = 763331) B763331
theorem B508907 : Blo 507795 508907 := bstep (se 1 (by rfl) ⟨381680, by rfl⟩ : syracuseStep 508907 = 763361) B763361
theorem B508919 : Blo 507795 508919 := bstep (se 1 (by rfl) ⟨381689, by rfl⟩ : syracuseStep 508919 = 763379) B763379
theorem B508939 : Blo 507795 508939 := bstep (se 1 (by rfl) ⟨381704, by rfl⟩ : syracuseStep 508939 = 763409) B763409
theorem B508951 : Blo 507795 508951 := bstep (se 1 (by rfl) ⟨381713, by rfl⟩ : syracuseStep 508951 = 763427) B763427
theorem B508971 : Blo 507795 508971 := bstep (se 1 (by rfl) ⟨381728, by rfl⟩ : syracuseStep 508971 = 763457) B763457
theorem B3261485 : Blo 507795 3261485 := bstep (se 3 (by rfl) ⟨611528, by rfl⟩ : syracuseStep 3261485 = 1223057) B1223057
theorem B508983 : Blo 507795 508983 := bstep (se 1 (by rfl) ⟨381737, by rfl⟩ : syracuseStep 508983 = 763475) B763475
theorem B574519 : Blo 507795 574519 := bstep (se 1 (by rfl) ⟨430889, by rfl⟩ : syracuseStep 574519 = 861779) B861779
theorem B509003 : Blo 507795 509003 := bstep (se 1 (by rfl) ⟨381752, by rfl⟩ : syracuseStep 509003 = 763505) B763505
theorem B5817419 : Blo 507795 5817419 := bstep (se 1 (by rfl) ⟨4363064, by rfl⟩ : syracuseStep 5817419 = 8726129) B8726129
theorem B509015 : Blo 507795 509015 := bstep (se 1 (by rfl) ⟨381761, by rfl⟩ : syracuseStep 509015 = 763523) B763523
theorem B509035 : Blo 507795 509035 := bstep (se 1 (by rfl) ⟨381776, by rfl⟩ : syracuseStep 509035 = 763553) B763553
theorem B509047 : Blo 507795 509047 := bstep (se 1 (by rfl) ⟨381785, by rfl⟩ : syracuseStep 509047 = 763571) B763571
theorem B509067 : Blo 507795 509067 := bstep (se 1 (by rfl) ⟨381800, by rfl⟩ : syracuseStep 509067 = 763601) B763601
theorem B509079 : Blo 507795 509079 := bstep (se 1 (by rfl) ⟨381809, by rfl⟩ : syracuseStep 509079 = 763619) B763619
theorem B509099 : Blo 507795 509099 := bstep (se 1 (by rfl) ⟨381824, by rfl⟩ : syracuseStep 509099 = 763649) B763649
theorem B509111 : Blo 507795 509111 := bstep (se 1 (by rfl) ⟨381833, by rfl⟩ : syracuseStep 509111 = 763667) B763667
theorem B509131 : Blo 507795 509131 := bstep (se 1 (by rfl) ⟨381848, by rfl⟩ : syracuseStep 509131 = 763697) B763697
theorem B509143 : Blo 507795 509143 := bstep (se 1 (by rfl) ⟨381857, by rfl⟩ : syracuseStep 509143 = 763715) B763715
theorem B509163 : Blo 507795 509163 := bstep (se 1 (by rfl) ⟨381872, by rfl⟩ : syracuseStep 509163 = 763745) B763745
theorem B574699 : Blo 507795 574699 := bstep (se 1 (by rfl) ⟨431024, by rfl⟩ : syracuseStep 574699 = 862049) B862049
theorem B509175 : Blo 507795 509175 := bstep (se 1 (by rfl) ⟨381881, by rfl⟩ : syracuseStep 509175 = 763763) B763763
theorem B509195 : Blo 507795 509195 := bstep (se 1 (by rfl) ⟨381896, by rfl⟩ : syracuseStep 509195 = 763793) B763793
theorem B509207 : Blo 507795 509207 := bstep (se 1 (by rfl) ⟨381905, by rfl⟩ : syracuseStep 509207 = 763811) B763811
theorem B509227 : Blo 507795 509227 := bstep (se 1 (by rfl) ⟨381920, by rfl⟩ : syracuseStep 509227 = 763841) B763841
theorem B509239 : Blo 507795 509239 := bstep (se 1 (by rfl) ⟨381929, by rfl⟩ : syracuseStep 509239 = 763859) B763859
theorem B509259 : Blo 507795 509259 := bstep (se 1 (by rfl) ⟨381944, by rfl⟩ : syracuseStep 509259 = 763889) B763889
theorem B574807 : Blo 507795 574807 := bstep (se 1 (by rfl) ⟨431105, by rfl⟩ : syracuseStep 574807 = 862211) B862211
theorem B509271 : Blo 507795 509271 := bstep (se 1 (by rfl) ⟨381953, by rfl⟩ : syracuseStep 509271 = 763907) B763907
theorem B509291 : Blo 507795 509291 := bstep (se 1 (by rfl) ⟨381968, by rfl⟩ : syracuseStep 509291 = 763937) B763937
theorem B968051 : Blo 507795 968051 := bstep (se 1 (by rfl) ⟨726038, by rfl⟩ : syracuseStep 968051 = 1452077) B1452077
theorem B509303 : Blo 507795 509303 := bstep (se 1 (by rfl) ⟨381977, by rfl⟩ : syracuseStep 509303 = 763955) B763955
theorem B509323 : Blo 507795 509323 := bstep (se 1 (by rfl) ⟨381992, by rfl⟩ : syracuseStep 509323 = 763985) B763985
theorem B509335 : Blo 507795 509335 := bstep (se 1 (by rfl) ⟨382001, by rfl⟩ : syracuseStep 509335 = 764003) B764003
theorem B509355 : Blo 507795 509355 := bstep (se 1 (by rfl) ⟨382016, by rfl⟩ : syracuseStep 509355 = 764033) B764033
theorem B509367 : Blo 507795 509367 := bstep (se 1 (by rfl) ⟨382025, by rfl⟩ : syracuseStep 509367 = 764051) B764051
theorem B509387 : Blo 507795 509387 := bstep (se 1 (by rfl) ⟨382040, by rfl⟩ : syracuseStep 509387 = 764081) B764081
theorem B509399 : Blo 507795 509399 := bstep (se 1 (by rfl) ⟨382049, by rfl⟩ : syracuseStep 509399 = 764099) B764099
theorem B509419 : Blo 507795 509419 := bstep (se 1 (by rfl) ⟨382064, by rfl⟩ : syracuseStep 509419 = 764129) B764129
theorem B509431 : Blo 507795 509431 := bstep (se 1 (by rfl) ⟨382073, by rfl⟩ : syracuseStep 509431 = 764147) B764147
theorem B509451 : Blo 507795 509451 := bstep (se 1 (by rfl) ⟨382088, by rfl⟩ : syracuseStep 509451 = 764177) B764177
theorem B968203 : Blo 507795 968203 := bstep (se 1 (by rfl) ⟨726152, by rfl⟩ : syracuseStep 968203 = 1452305) B1452305
theorem B574987 : Blo 507795 574987 := bstep (se 1 (by rfl) ⟨431240, by rfl⟩ : syracuseStep 574987 = 862481) B862481
theorem B509463 : Blo 507795 509463 := bstep (se 1 (by rfl) ⟨382097, by rfl⟩ : syracuseStep 509463 = 764195) B764195
theorem B509483 : Blo 507795 509483 := bstep (se 1 (by rfl) ⟨382112, by rfl⟩ : syracuseStep 509483 = 764225) B764225
theorem B509495 : Blo 507795 509495 := bstep (se 1 (by rfl) ⟨382121, by rfl⟩ : syracuseStep 509495 = 764243) B764243
theorem B3688001 : Blo 507795 3688001 := bstep (se 2 (by rfl) ⟨1383000, by rfl⟩ : syracuseStep 3688001 = 2766001) B2766001
theorem B509515 : Blo 507795 509515 := bstep (se 1 (by rfl) ⟨382136, by rfl⟩ : syracuseStep 509515 = 764273) B764273
theorem B509527 : Blo 507795 509527 := bstep (se 1 (by rfl) ⟨382145, by rfl⟩ : syracuseStep 509527 = 764291) B764291
theorem B2442845 : Blo 507795 2442845 := bstep (se 3 (by rfl) ⟨458033, by rfl⟩ : syracuseStep 2442845 = 916067) B916067
theorem B509547 : Blo 507795 509547 := bstep (se 1 (by rfl) ⟨382160, by rfl⟩ : syracuseStep 509547 = 764321) B764321
theorem B509559 : Blo 507795 509559 := bstep (se 1 (by rfl) ⟨382169, by rfl⟩ : syracuseStep 509559 = 764339) B764339
theorem B575095 : Blo 507795 575095 := bstep (se 1 (by rfl) ⟨431321, by rfl⟩ : syracuseStep 575095 = 862643) B862643
theorem B509579 : Blo 507795 509579 := bstep (se 1 (by rfl) ⟨382184, by rfl⟩ : syracuseStep 509579 = 764369) B764369
theorem B542359 : Blo 507795 542359 := bstep (se 1 (by rfl) ⟨406769, by rfl⟩ : syracuseStep 542359 = 813539) B813539
theorem B509591 : Blo 507795 509591 := bstep (se 1 (by rfl) ⟨382193, by rfl⟩ : syracuseStep 509591 = 764387) B764387
theorem B509611 : Blo 507795 509611 := bstep (se 1 (by rfl) ⟨382208, by rfl⟩ : syracuseStep 509611 = 764417) B764417
theorem B509623 : Blo 507795 509623 := bstep (se 1 (by rfl) ⟨382217, by rfl⟩ : syracuseStep 509623 = 764435) B764435
theorem B509643 : Blo 507795 509643 := bstep (se 1 (by rfl) ⟨382232, by rfl⟩ : syracuseStep 509643 = 764465) B764465
theorem B1722059 : Blo 507795 1722059 := bstep (se 1 (by rfl) ⟨1291544, by rfl⟩ : syracuseStep 1722059 = 2583089) B2583089
theorem B509655 : Blo 507795 509655 := bstep (se 1 (by rfl) ⟨382241, by rfl⟩ : syracuseStep 509655 = 764483) B764483
theorem B509675 : Blo 507795 509675 := bstep (se 1 (by rfl) ⟨382256, by rfl⟩ : syracuseStep 509675 = 764513) B764513
theorem B509687 : Blo 507795 509687 := bstep (se 1 (by rfl) ⟨382265, by rfl⟩ : syracuseStep 509687 = 764531) B764531
theorem B509707 : Blo 507795 509707 := bstep (se 1 (by rfl) ⟨382280, by rfl⟩ : syracuseStep 509707 = 764561) B764561
theorem B509719 : Blo 507795 509719 := bstep (se 1 (by rfl) ⟨382289, by rfl⟩ : syracuseStep 509719 = 764579) B764579
theorem B509739 : Blo 507795 509739 := bstep (se 1 (by rfl) ⟨382304, by rfl⟩ : syracuseStep 509739 = 764609) B764609
theorem B575275 : Blo 507795 575275 := bstep (se 1 (by rfl) ⟨431456, by rfl⟩ : syracuseStep 575275 = 862913) B862913
theorem B509751 : Blo 507795 509751 := bstep (se 1 (by rfl) ⟨382313, by rfl⟩ : syracuseStep 509751 = 764627) B764627
theorem B509771 : Blo 507795 509771 := bstep (se 1 (by rfl) ⟨382328, by rfl⟩ : syracuseStep 509771 = 764657) B764657
theorem B509783 : Blo 507795 509783 := bstep (se 1 (by rfl) ⟨382337, by rfl⟩ : syracuseStep 509783 = 764675) B764675
theorem B968537 : Blo 507795 968537 := bstep (se 2 (by rfl) ⟨363201, by rfl⟩ : syracuseStep 968537 = 726403) B726403
theorem B509803 : Blo 507795 509803 := bstep (se 1 (by rfl) ⟨382352, by rfl⟩ : syracuseStep 509803 = 764705) B764705
theorem B509815 : Blo 507795 509815 := bstep (se 1 (by rfl) ⟨382361, by rfl⟩ : syracuseStep 509815 = 764723) B764723
theorem B509835 : Blo 507795 509835 := bstep (se 1 (by rfl) ⟨382376, by rfl⟩ : syracuseStep 509835 = 764753) B764753
theorem B509847 : Blo 507795 509847 := bstep (se 1 (by rfl) ⟨382385, by rfl⟩ : syracuseStep 509847 = 764771) B764771
theorem B575383 : Blo 507795 575383 := bstep (se 1 (by rfl) ⟨431537, by rfl⟩ : syracuseStep 575383 = 863075) B863075
theorem B509867 : Blo 507795 509867 := bstep (se 1 (by rfl) ⟨382400, by rfl⟩ : syracuseStep 509867 = 764801) B764801
theorem B509879 : Blo 507795 509879 := bstep (se 1 (by rfl) ⟨382409, by rfl⟩ : syracuseStep 509879 = 764819) B764819
theorem B509899 : Blo 507795 509899 := bstep (se 1 (by rfl) ⟨382424, by rfl⟩ : syracuseStep 509899 = 764849) B764849
theorem B509911 : Blo 507795 509911 := bstep (se 1 (by rfl) ⟨382433, by rfl⟩ : syracuseStep 509911 = 764867) B764867
theorem B1722329 : Blo 507795 1722329 := bstep (se 2 (by rfl) ⟨645873, by rfl⟩ : syracuseStep 1722329 = 1291747) B1291747
theorem B509931 : Blo 507795 509931 := bstep (se 1 (by rfl) ⟨382448, by rfl⟩ : syracuseStep 509931 = 764897) B764897
theorem B509943 : Blo 507795 509943 := bstep (se 1 (by rfl) ⟨382457, by rfl⟩ : syracuseStep 509943 = 764915) B764915
theorem B509963 : Blo 507795 509963 := bstep (se 1 (by rfl) ⟨382472, by rfl⟩ : syracuseStep 509963 = 764945) B764945
theorem B509975 : Blo 507795 509975 := bstep (se 1 (by rfl) ⟨382481, by rfl⟩ : syracuseStep 509975 = 764963) B764963
theorem B509995 : Blo 507795 509995 := bstep (se 1 (by rfl) ⟨382496, by rfl⟩ : syracuseStep 509995 = 764993) B764993
theorem B510007 : Blo 507795 510007 := bstep (se 1 (by rfl) ⟨382505, by rfl⟩ : syracuseStep 510007 = 765011) B765011
theorem B510027 : Blo 507795 510027 := bstep (se 1 (by rfl) ⟨382520, by rfl⟩ : syracuseStep 510027 = 765041) B765041
theorem B575563 : Blo 507795 575563 := bstep (se 1 (by rfl) ⟨431672, by rfl⟩ : syracuseStep 575563 = 863345) B863345
theorem B510039 : Blo 507795 510039 := bstep (se 1 (by rfl) ⟨382529, by rfl⟩ : syracuseStep 510039 = 765059) B765059
theorem B510059 : Blo 507795 510059 := bstep (se 1 (by rfl) ⟨382544, by rfl⟩ : syracuseStep 510059 = 765089) B765089
theorem B510071 : Blo 507795 510071 := bstep (se 1 (by rfl) ⟨382553, by rfl⟩ : syracuseStep 510071 = 765107) B765107
theorem B510091 : Blo 507795 510091 := bstep (se 1 (by rfl) ⟨382568, by rfl⟩ : syracuseStep 510091 = 765137) B765137
theorem B772247 : Blo 507795 772247 := bstep (se 1 (by rfl) ⟨579185, by rfl⟩ : syracuseStep 772247 = 1158371) B1158371
theorem B510103 : Blo 507795 510103 := bstep (se 1 (by rfl) ⟨382577, by rfl⟩ : syracuseStep 510103 = 765155) B765155
theorem B510123 : Blo 507795 510123 := bstep (se 1 (by rfl) ⟨382592, by rfl⟩ : syracuseStep 510123 = 765185) B765185
theorem B510135 : Blo 507795 510135 := bstep (se 1 (by rfl) ⟨382601, by rfl⟩ : syracuseStep 510135 = 765203) B765203
theorem B575671 : Blo 507795 575671 := bstep (se 1 (by rfl) ⟨431753, by rfl⟩ : syracuseStep 575671 = 863507) B863507
theorem B510155 : Blo 507795 510155 := bstep (se 1 (by rfl) ⟨382616, by rfl⟩ : syracuseStep 510155 = 765233) B765233
theorem B510167 : Blo 507795 510167 := bstep (se 1 (by rfl) ⟨382625, by rfl⟩ : syracuseStep 510167 = 765251) B765251
theorem B510187 : Blo 507795 510187 := bstep (se 1 (by rfl) ⟨382640, by rfl⟩ : syracuseStep 510187 = 765281) B765281
theorem B510199 : Blo 507795 510199 := bstep (se 1 (by rfl) ⟨382649, by rfl⟩ : syracuseStep 510199 = 765299) B765299
theorem B510219 : Blo 507795 510219 := bstep (se 1 (by rfl) ⟨382664, by rfl⟩ : syracuseStep 510219 = 765329) B765329
theorem B510231 : Blo 507795 510231 := bstep (se 1 (by rfl) ⟨382673, by rfl⟩ : syracuseStep 510231 = 765347) B765347
theorem B510251 : Blo 507795 510251 := bstep (se 1 (by rfl) ⟨382688, by rfl⟩ : syracuseStep 510251 = 765377) B765377
theorem B510263 : Blo 507795 510263 := bstep (se 1 (by rfl) ⟨382697, by rfl⟩ : syracuseStep 510263 = 765395) B765395
theorem B510283 : Blo 507795 510283 := bstep (se 1 (by rfl) ⟨382712, by rfl⟩ : syracuseStep 510283 = 765425) B765425
theorem B510295 : Blo 507795 510295 := bstep (se 1 (by rfl) ⟨382721, by rfl⟩ : syracuseStep 510295 = 765443) B765443
theorem B510315 : Blo 507795 510315 := bstep (se 1 (by rfl) ⟨382736, by rfl⟩ : syracuseStep 510315 = 765473) B765473
theorem B510327 : Blo 507795 510327 := bstep (se 1 (by rfl) ⟨382745, by rfl⟩ : syracuseStep 510327 = 765491) B765491
theorem B510347 : Blo 507795 510347 := bstep (se 1 (by rfl) ⟨382760, by rfl⟩ : syracuseStep 510347 = 765521) B765521
theorem B510359 : Blo 507795 510359 := bstep (se 1 (by rfl) ⟨382769, by rfl⟩ : syracuseStep 510359 = 765539) B765539
theorem B510379 : Blo 507795 510379 := bstep (se 1 (by rfl) ⟨382784, by rfl⟩ : syracuseStep 510379 = 765569) B765569
theorem B510391 : Blo 507795 510391 := bstep (se 1 (by rfl) ⟨382793, by rfl⟩ : syracuseStep 510391 = 765587) B765587
theorem B510411 : Blo 507795 510411 := bstep (se 1 (by rfl) ⟨382808, by rfl⟩ : syracuseStep 510411 = 765617) B765617
theorem B510423 : Blo 507795 510423 := bstep (se 1 (by rfl) ⟨382817, by rfl⟩ : syracuseStep 510423 = 765635) B765635
theorem B969175 : Blo 507795 969175 := bstep (se 1 (by rfl) ⟨726881, by rfl⟩ : syracuseStep 969175 = 1453763) B1453763
theorem B510443 : Blo 507795 510443 := bstep (se 1 (by rfl) ⟨382832, by rfl⟩ : syracuseStep 510443 = 765665) B765665
theorem B510455 : Blo 507795 510455 := bstep (se 1 (by rfl) ⟨382841, by rfl⟩ : syracuseStep 510455 = 765683) B765683
theorem B510475 : Blo 507795 510475 := bstep (se 1 (by rfl) ⟨382856, by rfl⟩ : syracuseStep 510475 = 765713) B765713
theorem B510487 : Blo 507795 510487 := bstep (se 1 (by rfl) ⟨382865, by rfl⟩ : syracuseStep 510487 = 765731) B765731
theorem B510507 : Blo 507795 510507 := bstep (se 1 (by rfl) ⟨382880, by rfl⟩ : syracuseStep 510507 = 765761) B765761
theorem B510519 : Blo 507795 510519 := bstep (se 1 (by rfl) ⟨382889, by rfl⟩ : syracuseStep 510519 = 765779) B765779
theorem B510539 : Blo 507795 510539 := bstep (se 1 (by rfl) ⟨382904, by rfl⟩ : syracuseStep 510539 = 765809) B765809
theorem B510551 : Blo 507795 510551 := bstep (se 1 (by rfl) ⟨382913, by rfl⟩ : syracuseStep 510551 = 765827) B765827
theorem B510571 : Blo 507795 510571 := bstep (se 1 (by rfl) ⟨382928, by rfl⟩ : syracuseStep 510571 = 765857) B765857
theorem B510583 : Blo 507795 510583 := bstep (se 1 (by rfl) ⟨382937, by rfl⟩ : syracuseStep 510583 = 765875) B765875
theorem B510603 : Blo 507795 510603 := bstep (se 1 (by rfl) ⟨382952, by rfl⟩ : syracuseStep 510603 = 765905) B765905
theorem B1723031 : Blo 507795 1723031 := bstep (se 1 (by rfl) ⟨1292273, by rfl⟩ : syracuseStep 1723031 = 2584547) B2584547
theorem B510615 : Blo 507795 510615 := bstep (se 1 (by rfl) ⟨382961, by rfl⟩ : syracuseStep 510615 = 765923) B765923
theorem B510635 : Blo 507795 510635 := bstep (se 1 (by rfl) ⟨382976, by rfl⟩ : syracuseStep 510635 = 765953) B765953
theorem B510647 : Blo 507795 510647 := bstep (se 1 (by rfl) ⟨382985, by rfl⟩ : syracuseStep 510647 = 765971) B765971
theorem B510667 : Blo 507795 510667 := bstep (se 1 (by rfl) ⟨383000, by rfl⟩ : syracuseStep 510667 = 766001) B766001
theorem B510679 : Blo 507795 510679 := bstep (se 1 (by rfl) ⟨383009, by rfl⟩ : syracuseStep 510679 = 766019) B766019
theorem B510699 : Blo 507795 510699 := bstep (se 1 (by rfl) ⟨383024, by rfl⟩ : syracuseStep 510699 = 766049) B766049
theorem B510711 : Blo 507795 510711 := bstep (se 1 (by rfl) ⟨383033, by rfl⟩ : syracuseStep 510711 = 766067) B766067
theorem B510731 : Blo 507795 510731 := bstep (se 1 (by rfl) ⟨383048, by rfl⟩ : syracuseStep 510731 = 766097) B766097
theorem B510743 : Blo 507795 510743 := bstep (se 1 (by rfl) ⟨383057, by rfl⟩ : syracuseStep 510743 = 766115) B766115
theorem B510763 : Blo 507795 510763 := bstep (se 1 (by rfl) ⟨383072, by rfl⟩ : syracuseStep 510763 = 766145) B766145
theorem B510775 : Blo 507795 510775 := bstep (se 1 (by rfl) ⟨383081, by rfl⟩ : syracuseStep 510775 = 766163) B766163
theorem B510795 : Blo 507795 510795 := bstep (se 1 (by rfl) ⟨383096, by rfl⟩ : syracuseStep 510795 = 766193) B766193
theorem B510807 : Blo 507795 510807 := bstep (se 1 (by rfl) ⟨383105, by rfl⟩ : syracuseStep 510807 = 766211) B766211
theorem B510827 : Blo 507795 510827 := bstep (se 1 (by rfl) ⟨383120, by rfl⟩ : syracuseStep 510827 = 766241) B766241
theorem B510839 : Blo 507795 510839 := bstep (se 1 (by rfl) ⟨383129, by rfl⟩ : syracuseStep 510839 = 766259) B766259
theorem B510859 : Blo 507795 510859 := bstep (se 1 (by rfl) ⟨383144, by rfl⟩ : syracuseStep 510859 = 766289) B766289
theorem B510871 : Blo 507795 510871 := bstep (se 1 (by rfl) ⟨383153, by rfl⟩ : syracuseStep 510871 = 766307) B766307
theorem B510891 : Blo 507795 510891 := bstep (se 1 (by rfl) ⟨383168, by rfl⟩ : syracuseStep 510891 = 766337) B766337
theorem B510903 : Blo 507795 510903 := bstep (se 1 (by rfl) ⟨383177, by rfl⟩ : syracuseStep 510903 = 766355) B766355
theorem B510923 : Blo 507795 510923 := bstep (se 1 (by rfl) ⟨383192, by rfl⟩ : syracuseStep 510923 = 766385) B766385
theorem B510935 : Blo 507795 510935 := bstep (se 1 (by rfl) ⟨383201, by rfl⟩ : syracuseStep 510935 = 766403) B766403
theorem B510955 : Blo 507795 510955 := bstep (se 1 (by rfl) ⟨383216, by rfl⟩ : syracuseStep 510955 = 766433) B766433
theorem B510967 : Blo 507795 510967 := bstep (se 1 (by rfl) ⟨383225, by rfl⟩ : syracuseStep 510967 = 766451) B766451
theorem B510987 : Blo 507795 510987 := bstep (se 1 (by rfl) ⟨383240, by rfl⟩ : syracuseStep 510987 = 766481) B766481
theorem B510999 : Blo 507795 510999 := bstep (se 1 (by rfl) ⟨383249, by rfl⟩ : syracuseStep 510999 = 766499) B766499
theorem B511019 : Blo 507795 511019 := bstep (se 1 (by rfl) ⟨383264, by rfl⟩ : syracuseStep 511019 = 766529) B766529
theorem B511031 : Blo 507795 511031 := bstep (se 1 (by rfl) ⟨383273, by rfl⟩ : syracuseStep 511031 = 766547) B766547
theorem B511051 : Blo 507795 511051 := bstep (se 1 (by rfl) ⟨383288, by rfl⟩ : syracuseStep 511051 = 766577) B766577
theorem B511063 : Blo 507795 511063 := bstep (se 1 (by rfl) ⟨383297, by rfl⟩ : syracuseStep 511063 = 766595) B766595
theorem B511083 : Blo 507795 511083 := bstep (se 1 (by rfl) ⟨383312, by rfl⟩ : syracuseStep 511083 = 766625) B766625
theorem B511095 : Blo 507795 511095 := bstep (se 1 (by rfl) ⟨383321, by rfl⟩ : syracuseStep 511095 = 766643) B766643
theorem B511115 : Blo 507795 511115 := bstep (se 1 (by rfl) ⟨383336, by rfl⟩ : syracuseStep 511115 = 766673) B766673
theorem B511127 : Blo 507795 511127 := bstep (se 1 (by rfl) ⟨383345, by rfl⟩ : syracuseStep 511127 = 766691) B766691
theorem B773273 : Blo 507795 773273 := bstep (se 2 (by rfl) ⟨289977, by rfl⟩ : syracuseStep 773273 = 579955) B579955
theorem B511147 : Blo 507795 511147 := bstep (se 1 (by rfl) ⟨383360, by rfl⟩ : syracuseStep 511147 = 766721) B766721
theorem B1723571 : Blo 507795 1723571 := bstep (se 1 (by rfl) ⟨1292678, by rfl⟩ : syracuseStep 1723571 = 2585357) B2585357
theorem B1035443 : Blo 507795 1035443 := bstep (se 1 (by rfl) ⟨776582, by rfl⟩ : syracuseStep 1035443 = 1553165) B1553165
theorem B511159 : Blo 507795 511159 := bstep (se 1 (by rfl) ⟨383369, by rfl⟩ : syracuseStep 511159 = 766739) B766739
theorem B511179 : Blo 507795 511179 := bstep (se 1 (by rfl) ⟨383384, by rfl⟩ : syracuseStep 511179 = 766769) B766769
theorem B511191 : Blo 507795 511191 := bstep (se 1 (by rfl) ⟨383393, by rfl⟩ : syracuseStep 511191 = 766787) B766787
theorem B511211 : Blo 507795 511211 := bstep (se 1 (by rfl) ⟨383408, by rfl⟩ : syracuseStep 511211 = 766817) B766817
theorem B543991 : Blo 507795 543991 := bstep (se 1 (by rfl) ⟨407993, by rfl⟩ : syracuseStep 543991 = 815987) B815987
theorem B511223 : Blo 507795 511223 := bstep (se 1 (by rfl) ⟨383417, by rfl⟩ : syracuseStep 511223 = 766835) B766835
theorem B969995 : Blo 507795 969995 := bstep (se 1 (by rfl) ⟨727496, by rfl⟩ : syracuseStep 969995 = 1454993) B1454993
theorem B511243 : Blo 507795 511243 := bstep (se 1 (by rfl) ⟨383432, by rfl⟩ : syracuseStep 511243 = 766865) B766865
theorem B511255 : Blo 507795 511255 := bstep (se 1 (by rfl) ⟨383441, by rfl⟩ : syracuseStep 511255 = 766883) B766883
theorem B544043 : Blo 507795 544043 := bstep (se 1 (by rfl) ⟨408032, by rfl⟩ : syracuseStep 544043 = 816065) B816065
theorem B511275 : Blo 507795 511275 := bstep (se 1 (by rfl) ⟨383456, by rfl⟩ : syracuseStep 511275 = 766913) B766913
theorem B511287 : Blo 507795 511287 := bstep (se 1 (by rfl) ⟨383465, by rfl⟩ : syracuseStep 511287 = 766931) B766931
theorem B970049 : Blo 507795 970049 := bstep (se 2 (by rfl) ⟨363768, by rfl⟩ : syracuseStep 970049 = 727537) B727537
theorem B511307 : Blo 507795 511307 := bstep (se 1 (by rfl) ⟨383480, by rfl⟩ : syracuseStep 511307 = 766961) B766961
theorem B511319 : Blo 507795 511319 := bstep (se 1 (by rfl) ⟨383489, by rfl⟩ : syracuseStep 511319 = 766979) B766979
theorem B511339 : Blo 507795 511339 := bstep (se 1 (by rfl) ⟨383504, by rfl⟩ : syracuseStep 511339 = 767009) B767009
theorem B511351 : Blo 507795 511351 := bstep (se 1 (by rfl) ⟨383513, by rfl⟩ : syracuseStep 511351 = 767027) B767027
theorem B511371 : Blo 507795 511371 := bstep (se 1 (by rfl) ⟨383528, by rfl⟩ : syracuseStep 511371 = 767057) B767057
theorem B511383 : Blo 507795 511383 := bstep (se 1 (by rfl) ⟨383537, by rfl⟩ : syracuseStep 511383 = 767075) B767075
theorem B511403 : Blo 507795 511403 := bstep (se 1 (by rfl) ⟨383552, by rfl⟩ : syracuseStep 511403 = 767105) B767105
theorem B511415 : Blo 507795 511415 := bstep (se 1 (by rfl) ⟨383561, by rfl⟩ : syracuseStep 511415 = 767123) B767123
theorem B1723841 : Blo 507795 1723841 := bstep (se 2 (by rfl) ⟨646440, by rfl⟩ : syracuseStep 1723841 = 1292881) B1292881
theorem B511435 : Blo 507795 511435 := bstep (se 1 (by rfl) ⟨383576, by rfl⟩ : syracuseStep 511435 = 767153) B767153
theorem B511447 : Blo 507795 511447 := bstep (se 1 (by rfl) ⟨383585, by rfl⟩ : syracuseStep 511447 = 767171) B767171
theorem B511467 : Blo 507795 511467 := bstep (se 1 (by rfl) ⟨383600, by rfl⟩ : syracuseStep 511467 = 767201) B767201
theorem B511479 : Blo 507795 511479 := bstep (se 1 (by rfl) ⟨383609, by rfl⟩ : syracuseStep 511479 = 767219) B767219
theorem B511499 : Blo 507795 511499 := bstep (se 1 (by rfl) ⟨383624, by rfl⟩ : syracuseStep 511499 = 767249) B767249
theorem B511511 : Blo 507795 511511 := bstep (se 1 (by rfl) ⟨383633, by rfl⟩ : syracuseStep 511511 = 767267) B767267
theorem B511531 : Blo 507795 511531 := bstep (se 1 (by rfl) ⟨383648, by rfl⟩ : syracuseStep 511531 = 767297) B767297
theorem B511543 : Blo 507795 511543 := bstep (se 1 (by rfl) ⟨383657, by rfl⟩ : syracuseStep 511543 = 767315) B767315
theorem B511563 : Blo 507795 511563 := bstep (se 1 (by rfl) ⟨383672, by rfl⟩ : syracuseStep 511563 = 767345) B767345
theorem B511575 : Blo 507795 511575 := bstep (se 1 (by rfl) ⟨383681, by rfl⟩ : syracuseStep 511575 = 767363) B767363
theorem B511595 : Blo 507795 511595 := bstep (se 1 (by rfl) ⟨383696, by rfl⟩ : syracuseStep 511595 = 767393) B767393
theorem B511607 : Blo 507795 511607 := bstep (se 1 (by rfl) ⟨383705, by rfl⟩ : syracuseStep 511607 = 767411) B767411
theorem B511627 : Blo 507795 511627 := bstep (se 1 (by rfl) ⟨383720, by rfl⟩ : syracuseStep 511627 = 767441) B767441
theorem B511639 : Blo 507795 511639 := bstep (se 1 (by rfl) ⟨383729, by rfl⟩ : syracuseStep 511639 = 767459) B767459
theorem B511659 : Blo 507795 511659 := bstep (se 1 (by rfl) ⟨383744, by rfl⟩ : syracuseStep 511659 = 767489) B767489
theorem B511671 : Blo 507795 511671 := bstep (se 1 (by rfl) ⟨383753, by rfl⟩ : syracuseStep 511671 = 767507) B767507
theorem B511691 : Blo 507795 511691 := bstep (se 1 (by rfl) ⟨383768, by rfl⟩ : syracuseStep 511691 = 767537) B767537
theorem B511703 : Blo 507795 511703 := bstep (se 1 (by rfl) ⟨383777, by rfl⟩ : syracuseStep 511703 = 767555) B767555
theorem B511723 : Blo 507795 511723 := bstep (se 1 (by rfl) ⟨383792, by rfl⟩ : syracuseStep 511723 = 767585) B767585
theorem B511735 : Blo 507795 511735 := bstep (se 1 (by rfl) ⟨383801, by rfl⟩ : syracuseStep 511735 = 767603) B767603
theorem B511755 : Blo 507795 511755 := bstep (se 1 (by rfl) ⟨383816, by rfl⟩ : syracuseStep 511755 = 767633) B767633
theorem B511767 : Blo 507795 511767 := bstep (se 1 (by rfl) ⟨383825, by rfl⟩ : syracuseStep 511767 = 767651) B767651
theorem B511787 : Blo 507795 511787 := bstep (se 1 (by rfl) ⟨383840, by rfl⟩ : syracuseStep 511787 = 767681) B767681
theorem B3264407 : Blo 507795 3264407 := bstep (se 1 (by rfl) ⟨2448305, by rfl⟩ : syracuseStep 3264407 = 4896611) B4896611
theorem B2183105 : Blo 507795 2183105 := bstep (se 2 (by rfl) ⟨818664, by rfl⟩ : syracuseStep 2183105 = 1637329) B1637329
theorem B1724381 : Blo 507795 1724381 := bstep (se 3 (by rfl) ⟨323321, by rfl⟩ : syracuseStep 1724381 = 646643) B646643
theorem B610327 : Blo 507795 610327 := bstep (se 1 (by rfl) ⟨457745, by rfl⟩ : syracuseStep 610327 = 915491) B915491
theorem B544811 : Blo 507795 544811 := bstep (se 1 (by rfl) ⟨408608, by rfl⟩ : syracuseStep 544811 = 817217) B817217
theorem B970967 : Blo 507795 970967 := bstep (se 1 (by rfl) ⟨728225, by rfl⟩ : syracuseStep 970967 = 1456451) B1456451
theorem B643403 : Blo 507795 643403 := bstep (se 1 (by rfl) ⟨482552, by rfl⟩ : syracuseStep 643403 = 965105) B965105
theorem B2576771 : Blo 507795 2576771 := bstep (se 1 (by rfl) ⟨1932578, by rfl⟩ : syracuseStep 2576771 = 3865157) B3865157
theorem B5493379 : Blo 507795 5493379 := bstep (se 1 (by rfl) ⟨4120034, by rfl⟩ : syracuseStep 5493379 = 8240069) B8240069
theorem B971507 : Blo 507795 971507 := bstep (se 1 (by rfl) ⟨728630, by rfl⟩ : syracuseStep 971507 = 1457261) B1457261
theorem B2184029 : Blo 507795 2184029 := bstep (se 3 (by rfl) ⟨409505, by rfl⟩ : syracuseStep 2184029 = 819011) B819011
theorem B644107 : Blo 507795 644107 := bstep (se 1 (by rfl) ⟨483080, by rfl⟩ : syracuseStep 644107 = 966161) B966161
theorem B1037323 : Blo 507795 1037323 := bstep (se 1 (by rfl) ⟨777992, by rfl⟩ : syracuseStep 1037323 = 1555985) B1555985
theorem B1725515 : Blo 507795 1725515 := bstep (se 1 (by rfl) ⟨1294136, by rfl⟩ : syracuseStep 1725515 = 2588273) B2588273
theorem B545879 : Blo 507795 545879 := bstep (se 1 (by rfl) ⟨409409, by rfl⟩ : syracuseStep 545879 = 818819) B818819
theorem B644375 : Blo 507795 644375 := bstep (se 1 (by rfl) ⟨483281, by rfl⟩ : syracuseStep 644375 = 966563) B966563
theorem B1725785 : Blo 507795 1725785 := bstep (se 2 (by rfl) ⟨647169, by rfl⟩ : syracuseStep 1725785 = 1294339) B1294339
theorem B2119115 : Blo 507795 2119115 := bstep (se 1 (by rfl) ⟨1589336, by rfl⟩ : syracuseStep 2119115 = 3178673) B3178673
theorem B9557597 : Blo 507795 9557597 := bstep (se 3 (by rfl) ⟨1792049, by rfl⟩ : syracuseStep 9557597 = 3584099) B3584099
theorem B645079 : Blo 507795 645079 := bstep (se 1 (by rfl) ⟨483809, by rfl⟩ : syracuseStep 645079 = 967619) B967619
theorem B1726487 : Blo 507795 1726487 := bstep (se 1 (by rfl) ⟨1294865, by rfl⟩ : syracuseStep 1726487 = 2589731) B2589731
theorem B874585 : Blo 507795 874585 := bstep (se 2 (by rfl) ⟨327969, by rfl⟩ : syracuseStep 874585 = 655939) B655939
theorem B579991 : Blo 507795 579991 := bstep (se 1 (by rfl) ⟨434993, by rfl⟩ : syracuseStep 579991 = 869987) B869987
theorem B8739251 : Blo 507795 8739251 := bstep (se 1 (by rfl) ⟨6554438, by rfl⟩ : syracuseStep 8739251 = 13108877) B13108877
theorem B1727027 : Blo 507795 1727027 := bstep (se 1 (by rfl) ⟨1295270, by rfl⟩ : syracuseStep 1727027 = 2590541) B2590541
theorem B1727297 : Blo 507795 1727297 := bstep (se 2 (by rfl) ⟨647736, by rfl⟩ : syracuseStep 1727297 = 1295473) B1295473
theorem B4348849 : Blo 507795 4348849 := bstep (se 2 (by rfl) ⟨1630818, by rfl⟩ : syracuseStep 4348849 = 3261637) B3261637
theorem B613451 : Blo 507795 613451 := bstep (se 1 (by rfl) ⟨460088, by rfl⟩ : syracuseStep 613451 = 920177) B920177
theorem B3267971 : Blo 507795 3267971 := bstep (se 1 (by rfl) ⟨2450978, by rfl⟩ : syracuseStep 3267971 = 4901957) B4901957
theorem B3137069 : Blo 507795 3137069 := bstep (se 3 (by rfl) ⟨588200, by rfl⟩ : syracuseStep 3137069 = 1176401) B1176401
theorem B613975 : Blo 507795 613975 := bstep (se 1 (by rfl) ⟨460481, by rfl⟩ : syracuseStep 613975 = 920963) B920963
theorem B646795 : Blo 507795 646795 := bstep (se 1 (by rfl) ⟨485096, by rfl⟩ : syracuseStep 646795 = 970193) B970193
theorem B2612915 : Blo 507795 2612915 := bstep (se 1 (by rfl) ⟨1959686, by rfl⟩ : syracuseStep 2612915 = 3919373) B3919373
theorem B2449075 : Blo 507795 2449075 := bstep (se 1 (by rfl) ⟨1836806, by rfl⟩ : syracuseStep 2449075 = 3673613) B3673613
theorem B3858353 : Blo 507795 3858353 := bstep (se 2 (by rfl) ⟨1446882, by rfl⟩ : syracuseStep 3858353 = 2893765) B2893765
theorem B2580497 : Blo 507795 2580497 := bstep (se 2 (by rfl) ⟨967686, by rfl⟩ : syracuseStep 2580497 = 1935373) B1935373
theorem B5529617 : Blo 507795 5529617 := bstep (se 2 (by rfl) ⟨2073606, by rfl⟩ : syracuseStep 5529617 = 4147213) B4147213
theorem B11952197 : Blo 507795 11952197 := bstep (se 4 (by rfl) ⟨1120518, by rfl⟩ : syracuseStep 11952197 = 2241037) B2241037
theorem B2580659 : Blo 507795 2580659 := bstep (se 1 (by rfl) ⟨1935494, by rfl⟩ : syracuseStep 2580659 = 3870989) B3870989
theorem B516343 : Blo 507795 516343 := bstep (se 1 (by rfl) ⟨387257, by rfl⟩ : syracuseStep 516343 = 774515) B774515
theorem B5497093 : Blo 507795 5497093 := bstep (se 4 (by rfl) ⟨515352, by rfl⟩ : syracuseStep 5497093 = 1030705) B1030705
theorem B3858839 : Blo 507795 3858839 := bstep (se 1 (by rfl) ⟨2894129, by rfl⟩ : syracuseStep 3858839 = 5788259) B5788259
theorem B582071 : Blo 507795 582071 := bstep (se 1 (by rfl) ⟨436553, by rfl⟩ : syracuseStep 582071 = 873107) B873107
theorem B1860275 : Blo 507795 1860275 := bstep (se 1 (by rfl) ⟨1395206, by rfl⟩ : syracuseStep 1860275 = 2790413) B2790413
theorem B3662657 : Blo 507795 3662657 := bstep (se 2 (by rfl) ⟨1373496, by rfl⟩ : syracuseStep 3662657 = 2746993) B2746993
theorem B2319511 : Blo 507795 2319511 := bstep (se 1 (by rfl) ⟨1739633, by rfl⟩ : syracuseStep 2319511 = 3479267) B3479267
theorem B1631639 : Blo 507795 1631639 := bstep (se 1 (by rfl) ⟨1223729, by rfl⟩ : syracuseStep 1631639 = 2447459) B2447459
theorem B1631947 : Blo 507795 1631947 := bstep (se 1 (by rfl) ⟨1223960, by rfl⟩ : syracuseStep 1631947 = 2447921) B2447921
theorem B2582603 : Blo 507795 2582603 := bstep (se 1 (by rfl) ⟨1936952, by rfl⟩ : syracuseStep 2582603 = 3873905) B3873905
theorem B1830289 : Blo 507795 1830289 := bstep (se 2 (by rfl) ⟨686358, by rfl⟩ : syracuseStep 1830289 = 1372717) B1372717
theorem B4353497 : Blo 507795 4353497 := bstep (se 2 (by rfl) ⟨1632561, by rfl⟩ : syracuseStep 4353497 = 3265123) B3265123
theorem B7368209 : Blo 507795 7368209 := bstep (se 2 (by rfl) ⟨2763078, by rfl⟩ : syracuseStep 7368209 = 5526157) B5526157
theorem B2944613 : Blo 507795 2944613 := bstep (se 4 (by rfl) ⟨276057, by rfl⟩ : syracuseStep 2944613 = 552115) B552115
theorem B978611 : Blo 507795 978611 := bstep (se 1 (by rfl) ⟨733958, by rfl⟩ : syracuseStep 978611 = 1467917) B1467917
theorem B1994419 : Blo 507795 1994419 := bstep (se 1 (by rfl) ⟨1495814, by rfl⟩ : syracuseStep 1994419 = 2991629) B2991629
theorem B1634099 : Blo 507795 1634099 := bstep (se 1 (by rfl) ⟨1225574, by rfl⟩ : syracuseStep 1634099 = 2451149) B2451149
theorem B2584385 : Blo 507795 2584385 := bstep (se 2 (by rfl) ⟨969144, by rfl⟩ : syracuseStep 2584385 = 1938289) B1938289
theorem B1142603 : Blo 507795 1142603 := bstep (se 1 (by rfl) ⟨856952, by rfl⟩ : syracuseStep 1142603 = 1713905) B1713905
theorem B1142657 : Blo 507795 1142657 := bstep (se 2 (by rfl) ⟨428496, by rfl⟩ : syracuseStep 1142657 = 856993) B856993
theorem B815051 : Blo 507795 815051 := bstep (se 1 (by rfl) ⟨611288, by rfl⟩ : syracuseStep 815051 = 1222577) B1222577
theorem B815179 : Blo 507795 815179 := bstep (se 1 (by rfl) ⟨611384, by rfl⟩ : syracuseStep 815179 = 1222769) B1222769
theorem B1142873 : Blo 507795 1142873 := bstep (se 2 (by rfl) ⟨428577, by rfl⟩ : syracuseStep 1142873 = 857155) B857155
theorem B1831085 : Blo 507795 1831085 := bstep (se 3 (by rfl) ⟨343328, by rfl⟩ : syracuseStep 1831085 = 686657) B686657
theorem B1142963 : Blo 507795 1142963 := bstep (se 1 (by rfl) ⟨857222, by rfl⟩ : syracuseStep 1142963 = 1714445) B1714445
theorem B1142999 : Blo 507795 1142999 := bstep (se 1 (by rfl) ⟨857249, by rfl⟩ : syracuseStep 1142999 = 1714499) B1714499
theorem B815321 : Blo 507795 815321 := bstep (se 2 (by rfl) ⟨305745, by rfl⟩ : syracuseStep 815321 = 611491) B611491
theorem B2060633 : Blo 507795 2060633 := bstep (se 2 (by rfl) ⟨772737, by rfl⟩ : syracuseStep 2060633 = 1545475) B1545475
theorem B33616241 : Blo 507795 33616241 := bstep (se 2 (by rfl) ⟨12606090, by rfl⟩ : syracuseStep 33616241 = 25212181) B25212181
theorem B1143179 : Blo 507795 1143179 := bstep (se 1 (by rfl) ⟨857384, by rfl⟩ : syracuseStep 1143179 = 1714769) B1714769
theorem B1143233 : Blo 507795 1143233 := bstep (se 2 (by rfl) ⟨428712, by rfl⟩ : syracuseStep 1143233 = 857425) B857425
theorem B1831385 : Blo 507795 1831385 := bstep (se 2 (by rfl) ⟨686769, by rfl⟩ : syracuseStep 1831385 = 1373539) B1373539
theorem B2683523 : Blo 507795 2683523 := bstep (se 1 (by rfl) ⟨2012642, by rfl⟩ : syracuseStep 2683523 = 4025285) B4025285
theorem B1962641 : Blo 507795 1962641 := bstep (se 2 (by rfl) ⟨735990, by rfl⟩ : syracuseStep 1962641 = 1471981) B1471981
theorem B1143449 : Blo 507795 1143449 := bstep (se 2 (by rfl) ⟨428793, by rfl⟩ : syracuseStep 1143449 = 857587) B857587
theorem B6976205 : Blo 507795 6976205 := bstep (se 3 (by rfl) ⟨1308038, by rfl⟩ : syracuseStep 6976205 = 2616077) B2616077
theorem B1143539 : Blo 507795 1143539 := bstep (se 1 (by rfl) ⟨857654, by rfl⟩ : syracuseStep 1143539 = 1715309) B1715309
theorem B1143575 : Blo 507795 1143575 := bstep (se 1 (by rfl) ⟨857681, by rfl⟩ : syracuseStep 1143575 = 1715363) B1715363
theorem B1307443 : Blo 507795 1307443 := bstep (se 1 (by rfl) ⟨980582, by rfl⟩ : syracuseStep 1307443 = 1961165) B1961165
theorem B1373021 : Blo 507795 1373021 := bstep (se 3 (by rfl) ⟨257441, by rfl⟩ : syracuseStep 1373021 = 514883) B514883
theorem B1143755 : Blo 507795 1143755 := bstep (se 1 (by rfl) ⟨857816, by rfl⟩ : syracuseStep 1143755 = 1715633) B1715633
theorem B1143809 : Blo 507795 1143809 := bstep (se 2 (by rfl) ⟨428928, by rfl⟩ : syracuseStep 1143809 = 857857) B857857
theorem B1144025 : Blo 507795 1144025 := bstep (se 2 (by rfl) ⟨429009, by rfl⟩ : syracuseStep 1144025 = 858019) B858019
theorem B1930499 : Blo 507795 1930499 := bstep (se 1 (by rfl) ⟨1447874, by rfl⟩ : syracuseStep 1930499 = 2895749) B2895749
theorem B1930513 : Blo 507795 1930513 := bstep (se 2 (by rfl) ⟨723942, by rfl⟩ : syracuseStep 1930513 = 1447885) B1447885
theorem B816409 : Blo 507795 816409 := bstep (se 2 (by rfl) ⟨306153, by rfl⟩ : syracuseStep 816409 = 612307) B612307
theorem B1144115 : Blo 507795 1144115 := bstep (se 1 (by rfl) ⟨858086, by rfl⟩ : syracuseStep 1144115 = 1716173) B1716173
theorem B1144151 : Blo 507795 1144151 := bstep (se 1 (by rfl) ⟨858113, by rfl⟩ : syracuseStep 1144151 = 1716227) B1716227
theorem B1144331 : Blo 507795 1144331 := bstep (se 1 (by rfl) ⟨858248, by rfl⟩ : syracuseStep 1144331 = 1716497) B1716497
theorem B1930817 : Blo 507795 1930817 := bstep (se 2 (by rfl) ⟨724056, by rfl⟩ : syracuseStep 1930817 = 1448113) B1448113
theorem B1144385 : Blo 507795 1144385 := bstep (se 2 (by rfl) ⟨429144, by rfl⟩ : syracuseStep 1144385 = 858289) B858289
theorem B2586329 : Blo 507795 2586329 := bstep (se 2 (by rfl) ⟨969873, by rfl⟩ : syracuseStep 2586329 = 1939747) B1939747
theorem B2062045 : Blo 507795 2062045 := bstep (se 3 (by rfl) ⟨386633, by rfl⟩ : syracuseStep 2062045 = 773267) B773267
theorem B1144601 : Blo 507795 1144601 := bstep (se 2 (by rfl) ⟨429225, by rfl⟩ : syracuseStep 1144601 = 858451) B858451
theorem B2094913 : Blo 507795 2094913 := bstep (se 2 (by rfl) ⟨785592, by rfl⟩ : syracuseStep 2094913 = 1571185) B1571185
theorem B1144691 : Blo 507795 1144691 := bstep (se 1 (by rfl) ⟨858518, by rfl⟩ : syracuseStep 1144691 = 1717037) B1717037
theorem B1144727 : Blo 507795 1144727 := bstep (se 1 (by rfl) ⟨858545, by rfl⟩ : syracuseStep 1144727 = 1717091) B1717091
theorem B5502937 : Blo 507795 5502937 := bstep (se 2 (by rfl) ⟨2063601, by rfl⟩ : syracuseStep 5502937 = 4127203) B4127203
theorem B1144907 : Blo 507795 1144907 := bstep (se 1 (by rfl) ⟨858680, by rfl⟩ : syracuseStep 1144907 = 1717361) B1717361
theorem B1144961 : Blo 507795 1144961 := bstep (se 2 (by rfl) ⟨429360, by rfl⟩ : syracuseStep 1144961 = 858721) B858721
theorem B1931485 : Blo 507795 1931485 := bstep (se 3 (by rfl) ⟨362153, by rfl⟩ : syracuseStep 1931485 = 724307) B724307
theorem B1145177 : Blo 507795 1145177 := bstep (se 2 (by rfl) ⟨429441, by rfl⟩ : syracuseStep 1145177 = 858883) B858883
theorem B1145267 : Blo 507795 1145267 := bstep (se 1 (by rfl) ⟨858950, by rfl⟩ : syracuseStep 1145267 = 1717901) B1717901
theorem B1145303 : Blo 507795 1145303 := bstep (se 1 (by rfl) ⟨858977, by rfl⟩ : syracuseStep 1145303 = 1717955) B1717955
theorem B1145483 : Blo 507795 1145483 := bstep (se 1 (by rfl) ⟨859112, by rfl⟩ : syracuseStep 1145483 = 1718225) B1718225
theorem B1833623 : Blo 507795 1833623 := bstep (se 1 (by rfl) ⟨1375217, by rfl⟩ : syracuseStep 1833623 = 2750435) B2750435
theorem B1145537 : Blo 507795 1145537 := bstep (se 2 (by rfl) ⟨429576, by rfl⟩ : syracuseStep 1145537 = 859153) B859153
theorem B1374923 : Blo 507795 1374923 := bstep (se 1 (by rfl) ⟨1031192, by rfl⟩ : syracuseStep 1374923 = 2062385) B2062385
theorem B654103 : Blo 507795 654103 := bstep (se 1 (by rfl) ⟨490577, by rfl⟩ : syracuseStep 654103 = 981155) B981155
theorem B1145753 : Blo 507795 1145753 := bstep (se 2 (by rfl) ⟨429657, by rfl⟩ : syracuseStep 1145753 = 859315) B859315
theorem B1145843 : Blo 507795 1145843 := bstep (se 1 (by rfl) ⟨859382, by rfl⟩ : syracuseStep 1145843 = 1718765) B1718765
theorem B1145879 : Blo 507795 1145879 := bstep (se 1 (by rfl) ⟨859409, by rfl⟩ : syracuseStep 1145879 = 1718819) B1718819
theorem B6290507 : Blo 507795 6290507 := bstep (se 1 (by rfl) ⟨4717880, by rfl⟩ : syracuseStep 6290507 = 9435761) B9435761
theorem B2456669 : Blo 507795 2456669 := bstep (se 3 (by rfl) ⟨460625, by rfl⟩ : syracuseStep 2456669 = 921251) B921251
theorem B3112067 : Blo 507795 3112067 := bstep (se 1 (by rfl) ⟨2334050, by rfl⟩ : syracuseStep 3112067 = 4668101) B4668101
theorem B1146059 : Blo 507795 1146059 := bstep (se 1 (by rfl) ⟨859544, by rfl⟩ : syracuseStep 1146059 = 1719089) B1719089
theorem B1146113 : Blo 507795 1146113 := bstep (se 2 (by rfl) ⟨429792, by rfl⟩ : syracuseStep 1146113 = 859585) B859585
theorem B2587949 : Blo 507795 2587949 := bstep (se 3 (by rfl) ⟨485240, by rfl⟩ : syracuseStep 2587949 = 970481) B970481
theorem B1932761 : Blo 507795 1932761 := bstep (se 2 (by rfl) ⟨724785, by rfl⟩ : syracuseStep 1932761 = 1449571) B1449571
theorem B1146329 : Blo 507795 1146329 := bstep (se 2 (by rfl) ⟨429873, by rfl⟩ : syracuseStep 1146329 = 859747) B859747
theorem B3866129 : Blo 507795 3866129 := bstep (se 2 (by rfl) ⟨1449798, by rfl⟩ : syracuseStep 3866129 = 2899597) B2899597
theorem B654871 : Blo 507795 654871 := bstep (se 1 (by rfl) ⟨491153, by rfl⟩ : syracuseStep 654871 = 982307) B982307
theorem B1146419 : Blo 507795 1146419 := bstep (se 1 (by rfl) ⟨859814, by rfl⟩ : syracuseStep 1146419 = 1719629) B1719629
theorem B1146455 : Blo 507795 1146455 := bstep (se 1 (by rfl) ⟨859841, by rfl⟩ : syracuseStep 1146455 = 1719683) B1719683
theorem B9797213 : Blo 507795 9797213 := bstep (se 3 (by rfl) ⟨1836977, by rfl⟩ : syracuseStep 9797213 = 3673955) B3673955
theorem B1146635 : Blo 507795 1146635 := bstep (se 1 (by rfl) ⟨859976, by rfl⟩ : syracuseStep 1146635 = 1719953) B1719953
theorem B1834775 : Blo 507795 1834775 := bstep (se 1 (by rfl) ⟨1376081, by rfl⟩ : syracuseStep 1834775 = 2752163) B2752163
theorem B1146689 : Blo 507795 1146689 := bstep (se 2 (by rfl) ⟨430008, by rfl⟩ : syracuseStep 1146689 = 860017) B860017
theorem B18087857 : Blo 507795 18087857 := bstep (se 2 (by rfl) ⟨6782946, by rfl⟩ : syracuseStep 18087857 = 13565893) B13565893
theorem B688171 : Blo 507795 688171 := bstep (se 1 (by rfl) ⟨516128, by rfl⟩ : syracuseStep 688171 = 1032257) B1032257
theorem B1146923 : Blo 507795 1146923 := bstep (se 1 (by rfl) ⟨860192, by rfl⟩ : syracuseStep 1146923 = 1720385) B1720385
theorem B2588759 : Blo 507795 2588759 := bstep (se 1 (by rfl) ⟨1941569, by rfl⟩ : syracuseStep 2588759 = 3883139) B3883139
theorem B688457 : Blo 507795 688457 := bstep (se 2 (by rfl) ⟨258171, by rfl⟩ : syracuseStep 688457 = 516343) B516343
theorem B819575 : Blo 507795 819575 := bstep (se 1 (by rfl) ⟨614681, by rfl⟩ : syracuseStep 819575 = 1229363) B1229363
theorem B1933703 : Blo 507795 1933703 := bstep (se 1 (by rfl) ⟨1450277, by rfl⟩ : syracuseStep 1933703 = 2900555) B2900555
theorem B23462291 : Blo 507795 23462291 := bstep (se 1 (by rfl) ⟨17596718, by rfl⟩ : syracuseStep 23462291 = 35193437) B35193437
theorem B11010451 : Blo 507795 11010451 := bstep (se 1 (by rfl) ⟨8257838, by rfl⟩ : syracuseStep 11010451 = 16515677) B16515677
theorem B1147283 : Blo 507795 1147283 := bstep (se 1 (by rfl) ⟨860462, by rfl⟩ : syracuseStep 1147283 = 1720925) B1720925
theorem B1147337 : Blo 507795 1147337 := bstep (se 2 (by rfl) ⟨430251, by rfl⟩ : syracuseStep 1147337 = 860503) B860503
theorem B3867101 : Blo 507795 3867101 := bstep (se 3 (by rfl) ⟨725081, by rfl⟩ : syracuseStep 3867101 = 1450163) B1450163
theorem B3932675 : Blo 507795 3932675 := bstep (se 1 (by rfl) ⟨2949506, by rfl⟩ : syracuseStep 3932675 = 5899013) B5899013
theorem B2589245 : Blo 507795 2589245 := bstep (se 3 (by rfl) ⟨485483, by rfl⟩ : syracuseStep 2589245 = 970967) B970967
theorem B2654893 : Blo 507795 2654893 := bstep (se 3 (by rfl) ⟨497792, by rfl⟩ : syracuseStep 2654893 = 995585) B995585
theorem B787499 : Blo 507795 787499 := bstep (se 1 (by rfl) ⟨590624, by rfl⟩ : syracuseStep 787499 = 1181249) B1181249
theorem B2458667 : Blo 507795 2458667 := bstep (se 1 (by rfl) ⟨1844000, by rfl⟩ : syracuseStep 2458667 = 3688001) B3688001
theorem B12583997 : Blo 507795 12583997 := bstep (se 3 (by rfl) ⟨2359499, by rfl⟩ : syracuseStep 12583997 = 4718999) B4718999
theorem B1148039 : Blo 507795 1148039 := bstep (se 1 (by rfl) ⟨861029, by rfl⟩ : syracuseStep 1148039 = 1722059) B1722059
theorem B1148219 : Blo 507795 1148219 := bstep (se 1 (by rfl) ⟨861164, by rfl⟩ : syracuseStep 1148219 = 1722329) B1722329
theorem B1967507 : Blo 507795 1967507 := bstep (se 1 (by rfl) ⟨1475630, by rfl⟩ : syracuseStep 1967507 = 2951261) B2951261
theorem B1148345 : Blo 507795 1148345 := bstep (se 2 (by rfl) ⟨430629, by rfl⟩ : syracuseStep 1148345 = 861259) B861259
theorem B4130347 : Blo 507795 4130347 := bstep (se 1 (by rfl) ⟨3097760, by rfl⟩ : syracuseStep 4130347 = 6195521) B6195521
theorem B2361089 : Blo 507795 2361089 := bstep (se 2 (by rfl) ⟨885408, by rfl⟩ : syracuseStep 2361089 = 1770817) B1770817
theorem B1148687 : Blo 507795 1148687 := bstep (se 1 (by rfl) ⟨861515, by rfl⟩ : syracuseStep 1148687 = 1723031) B1723031
theorem B1148705 : Blo 507795 1148705 := bstep (se 2 (by rfl) ⟨430764, by rfl⟩ : syracuseStep 1148705 = 861529) B861529
theorem B1312697 : Blo 507795 1312697 := bstep (se 2 (by rfl) ⟨492261, by rfl⟩ : syracuseStep 1312697 = 984523) B984523
theorem B1149047 : Blo 507795 1149047 := bstep (se 1 (by rfl) ⟨861785, by rfl⟩ : syracuseStep 1149047 = 1723571) B1723571
theorem B690295 : Blo 507795 690295 := bstep (se 1 (by rfl) ⟨517721, by rfl⟩ : syracuseStep 690295 = 1035443) B1035443
theorem B1837313 : Blo 507795 1837313 := bstep (se 2 (by rfl) ⟨688992, by rfl⟩ : syracuseStep 1837313 = 1377985) B1377985
theorem B1149227 : Blo 507795 1149227 := bstep (se 1 (by rfl) ⟨861920, by rfl⟩ : syracuseStep 1149227 = 1723841) B1723841
theorem B723259 : Blo 507795 723259 := bstep (se 1 (by rfl) ⟨542444, by rfl⟩ : syracuseStep 723259 = 1084889) B1084889
theorem B1313111 : Blo 507795 1313111 := bstep (se 1 (by rfl) ⟨984833, by rfl⟩ : syracuseStep 1313111 = 1969667) B1969667
theorem B2066897 : Blo 507795 2066897 := bstep (se 2 (by rfl) ⟨775086, by rfl⟩ : syracuseStep 2066897 = 1550173) B1550173
theorem B1149587 : Blo 507795 1149587 := bstep (se 1 (by rfl) ⟨862190, by rfl⟩ : syracuseStep 1149587 = 1724381) B1724381
theorem B920249 : Blo 507795 920249 := bstep (se 2 (by rfl) ⟨345093, by rfl⟩ : syracuseStep 920249 = 690187) B690187
theorem B1149641 : Blo 507795 1149641 := bstep (se 2 (by rfl) ⟨431115, by rfl⟩ : syracuseStep 1149641 = 862231) B862231
theorem B6523685 : Blo 507795 6523685 := bstep (se 4 (by rfl) ⟨611595, by rfl⟩ : syracuseStep 6523685 = 1223191) B1223191
theorem B723755 : Blo 507795 723755 := bstep (se 1 (by rfl) ⟨542816, by rfl⟩ : syracuseStep 723755 = 1085633) B1085633
theorem B4655987 : Blo 507795 4655987 := bstep (se 1 (by rfl) ⟨3491990, by rfl⟩ : syracuseStep 4655987 = 6983981) B6983981
theorem B1150343 : Blo 507795 1150343 := bstep (se 1 (by rfl) ⟨862757, by rfl⟩ : syracuseStep 1150343 = 1725515) B1725515
theorem B1150523 : Blo 507795 1150523 := bstep (se 1 (by rfl) ⟨862892, by rfl⟩ : syracuseStep 1150523 = 1725785) B1725785
theorem B1412743 : Blo 507795 1412743 := bstep (se 1 (by rfl) ⟨1059557, by rfl⟩ : syracuseStep 1412743 = 2119115) B2119115
theorem B1150649 : Blo 507795 1150649 := bstep (se 2 (by rfl) ⟨431493, by rfl⟩ : syracuseStep 1150649 = 862987) B862987
theorem B4034393 : Blo 507795 4034393 := bstep (se 2 (by rfl) ⟨1512897, by rfl⟩ : syracuseStep 4034393 = 3025795) B3025795
theorem B1150991 : Blo 507795 1150991 := bstep (se 1 (by rfl) ⟨863243, by rfl⟩ : syracuseStep 1150991 = 1726487) B1726487
theorem B6557719 : Blo 507795 6557719 := bstep (se 1 (by rfl) ⟨4918289, by rfl⟩ : syracuseStep 6557719 = 9836579) B9836579
theorem B1151009 : Blo 507795 1151009 := bstep (se 2 (by rfl) ⟨431628, by rfl⟩ : syracuseStep 1151009 = 863257) B863257
theorem B2101315 : Blo 507795 2101315 := bstep (se 1 (by rfl) ⟨1575986, by rfl⟩ : syracuseStep 2101315 = 3151973) B3151973
theorem B725321 : Blo 507795 725321 := bstep (se 2 (by rfl) ⟨271995, by rfl⟩ : syracuseStep 725321 = 543991) B543991
theorem B1151351 : Blo 507795 1151351 := bstep (se 1 (by rfl) ⟨863513, by rfl⟩ : syracuseStep 1151351 = 1727027) B1727027
theorem B1151531 : Blo 507795 1151531 := bstep (se 1 (by rfl) ⟨863648, by rfl⟩ : syracuseStep 1151531 = 1727297) B1727297
theorem B725879 : Blo 507795 725879 := bstep (se 1 (by rfl) ⟨544409, by rfl⟩ : syracuseStep 725879 = 1088819) B1088819
theorem B2659225 : Blo 507795 2659225 := bstep (se 2 (by rfl) ⟨997209, by rfl⟩ : syracuseStep 2659225 = 1994419) B1994419
theorem B1741943 : Blo 507795 1741943 := bstep (se 1 (by rfl) ⟨1306457, by rfl⟩ : syracuseStep 1741943 = 2612915) B2612915
theorem B726187 : Blo 507795 726187 := bstep (se 1 (by rfl) ⟨544640, by rfl⟩ : syracuseStep 726187 = 1089281) B1089281
theorem B7968131 : Blo 507795 7968131 := bstep (se 1 (by rfl) ⟨5976098, by rfl⟩ : syracuseStep 7968131 = 11952197) B11952197
theorem B857479 : Blo 507795 857479 := bstep (se 1 (by rfl) ⟨643109, by rfl⟩ : syracuseStep 857479 = 1286219) B1286219
theorem B1086905 : Blo 507795 1086905 := bstep (se 2 (by rfl) ⟨407589, by rfl⟩ : syracuseStep 1086905 = 815179) B815179
theorem B726671 : Blo 507795 726671 := bstep (se 1 (by rfl) ⟨545003, by rfl⟩ : syracuseStep 726671 = 1090007) B1090007
theorem B858127 : Blo 507795 858127 := bstep (se 1 (by rfl) ⟨643595, by rfl⟩ : syracuseStep 858127 = 1287191) B1287191
theorem B1087759 : Blo 507795 1087759 := bstep (se 1 (by rfl) ⟨815819, by rfl⟩ : syracuseStep 1087759 = 1631639) B1631639
theorem B5970235 : Blo 507795 5970235 := bstep (se 1 (by rfl) ⟨4477676, by rfl⟩ : syracuseStep 5970235 = 8955353) B8955353
theorem B1743257 : Blo 507795 1743257 := bstep (se 2 (by rfl) ⟨653721, by rfl⟩ : syracuseStep 1743257 = 1307443) B1307443
theorem B858667 : Blo 507795 858667 := bstep (se 1 (by rfl) ⟨644000, by rfl⟩ : syracuseStep 858667 = 1288001) B1288001
theorem B1841707 : Blo 507795 1841707 := bstep (se 1 (by rfl) ⟨1381280, by rfl⟩ : syracuseStep 1841707 = 2762561) B2762561
theorem B858809 : Blo 507795 858809 := bstep (se 2 (by rfl) ⟨322053, by rfl⟩ : syracuseStep 858809 = 644107) B644107
theorem B1383097 : Blo 507795 1383097 := bstep (se 2 (by rfl) ⟨518661, by rfl⟩ : syracuseStep 1383097 = 1037323) B1037323
theorem B1448705 : Blo 507795 1448705 := bstep (se 2 (by rfl) ⟨543264, by rfl⟩ : syracuseStep 1448705 = 1086529) B1086529
theorem B1383227 : Blo 507795 1383227 := bstep (se 1 (by rfl) ⟨1037420, by rfl⟩ : syracuseStep 1383227 = 2074841) B2074841
theorem B2202553 : Blo 507795 2202553 := bstep (se 2 (by rfl) ⟨825957, by rfl⟩ : syracuseStep 2202553 = 1651915) B1651915
theorem B2169899 : Blo 507795 2169899 := bstep (se 1 (by rfl) ⟨1627424, by rfl⟩ : syracuseStep 2169899 = 3254849) B3254849
theorem B15735869 : Blo 507795 15735869 := bstep (se 3 (by rfl) ⟨2950475, by rfl⟩ : syracuseStep 15735869 = 5900951) B5900951
theorem B1449161 : Blo 507795 1449161 := bstep (se 2 (by rfl) ⟨543435, by rfl⟩ : syracuseStep 1449161 = 1086871) B1086871
theorem B1285409 : Blo 507795 1285409 := bstep (se 2 (by rfl) ⟨482028, by rfl⟩ : syracuseStep 1285409 = 964057) B964057
theorem B859511 : Blo 507795 859511 := bstep (se 1 (by rfl) ⟨644633, by rfl⟩ : syracuseStep 859511 = 1289267) B1289267
theorem B4660739 : Blo 507795 4660739 := bstep (se 1 (by rfl) ⟨3495554, by rfl⟩ : syracuseStep 4660739 = 6991109) B6991109
theorem B1449515 : Blo 507795 1449515 := bstep (se 1 (by rfl) ⟨1087136, by rfl⟩ : syracuseStep 1449515 = 2174273) B2174273
theorem B2760311 : Blo 507795 2760311 := bstep (se 1 (by rfl) ⟨2070233, by rfl⟩ : syracuseStep 2760311 = 4140467) B4140467
theorem B2793217 : Blo 507795 2793217 := bstep (se 2 (by rfl) ⟨1047456, by rfl⟩ : syracuseStep 2793217 = 2094913) B2094913
theorem B859963 : Blo 507795 859963 := bstep (se 1 (by rfl) ⟨644972, by rfl⟩ : syracuseStep 859963 = 1289945) B1289945
theorem B761735 : Blo 507795 761735 := bstep (se 1 (by rfl) ⟨571301, by rfl⟩ : syracuseStep 761735 = 1142603) B1142603
theorem B1843091 : Blo 507795 1843091 := bstep (se 1 (by rfl) ⟨1382318, by rfl⟩ : syracuseStep 1843091 = 2764637) B2764637
theorem B761771 : Blo 507795 761771 := bstep (se 1 (by rfl) ⟨571328, by rfl⟩ : syracuseStep 761771 = 1142657) B1142657
theorem B1449913 : Blo 507795 1449913 := bstep (se 2 (by rfl) ⟨543717, by rfl⟩ : syracuseStep 1449913 = 1087435) B1087435
theorem B761801 : Blo 507795 761801 := bstep (se 2 (by rfl) ⟨285675, by rfl⟩ : syracuseStep 761801 = 571351) B571351
theorem B860105 : Blo 507795 860105 := bstep (se 2 (by rfl) ⟨322539, by rfl⟩ : syracuseStep 860105 = 645079) B645079
theorem B761915 : Blo 507795 761915 := bstep (se 1 (by rfl) ⟨571436, by rfl⟩ : syracuseStep 761915 = 1142873) B1142873
theorem B3874877 : Blo 507795 3874877 := bstep (se 3 (by rfl) ⟨726539, by rfl⟩ : syracuseStep 3874877 = 1453079) B1453079
theorem B1220723 : Blo 507795 1220723 := bstep (se 1 (by rfl) ⟨915542, by rfl⟩ : syracuseStep 1220723 = 1831085) B1831085
theorem B761975 : Blo 507795 761975 := bstep (se 1 (by rfl) ⟨571481, by rfl⟩ : syracuseStep 761975 = 1142963) B1142963
theorem B761999 : Blo 507795 761999 := bstep (se 1 (by rfl) ⟨571499, by rfl⟩ : syracuseStep 761999 = 1142999) B1142999
theorem B762041 : Blo 507795 762041 := bstep (se 2 (by rfl) ⟨285765, by rfl⟩ : syracuseStep 762041 = 571531) B571531
theorem B1286401 : Blo 507795 1286401 := bstep (se 2 (by rfl) ⟨482400, by rfl⟩ : syracuseStep 1286401 = 964801) B964801
theorem B762119 : Blo 507795 762119 := bstep (se 1 (by rfl) ⟨571589, by rfl⟩ : syracuseStep 762119 = 1143179) B1143179
theorem B762155 : Blo 507795 762155 := bstep (se 1 (by rfl) ⟨571616, by rfl⟩ : syracuseStep 762155 = 1143233) B1143233
theorem B1220923 : Blo 507795 1220923 := bstep (se 1 (by rfl) ⟨915692, by rfl⟩ : syracuseStep 1220923 = 1831385) B1831385
theorem B762185 : Blo 507795 762185 := bstep (se 2 (by rfl) ⟨285819, by rfl⟩ : syracuseStep 762185 = 571639) B571639
theorem B8298845 : Blo 507795 8298845 := bstep (se 3 (by rfl) ⟨1556033, by rfl⟩ : syracuseStep 8298845 = 3112067) B3112067
theorem B762299 : Blo 507795 762299 := bstep (se 1 (by rfl) ⟨571724, by rfl⟩ : syracuseStep 762299 = 1143449) B1143449
theorem B762359 : Blo 507795 762359 := bstep (se 1 (by rfl) ⟨571769, by rfl⟩ : syracuseStep 762359 = 1143539) B1143539
theorem B762383 : Blo 507795 762383 := bstep (se 1 (by rfl) ⟨571787, by rfl⟩ : syracuseStep 762383 = 1143575) B1143575
theorem B762425 : Blo 507795 762425 := bstep (se 2 (by rfl) ⟨285909, by rfl⟩ : syracuseStep 762425 = 571819) B571819
theorem B762503 : Blo 507795 762503 := bstep (se 1 (by rfl) ⟨571877, by rfl⟩ : syracuseStep 762503 = 1143755) B1143755
theorem B860807 : Blo 507795 860807 := bstep (se 1 (by rfl) ⟨645605, by rfl⟩ : syracuseStep 860807 = 1291211) B1291211
theorem B762539 : Blo 507795 762539 := bstep (se 1 (by rfl) ⟨571904, by rfl⟩ : syracuseStep 762539 = 1143809) B1143809
theorem B762569 : Blo 507795 762569 := bstep (se 2 (by rfl) ⟨285963, by rfl⟩ : syracuseStep 762569 = 571927) B571927
theorem B1450781 : Blo 507795 1450781 := bstep (se 3 (by rfl) ⟨272021, by rfl⟩ : syracuseStep 1450781 = 544043) B544043
theorem B2892581 : Blo 507795 2892581 := bstep (se 4 (by rfl) ⟨271179, by rfl⟩ : syracuseStep 2892581 = 542359) B542359
theorem B762683 : Blo 507795 762683 := bstep (se 1 (by rfl) ⟨572012, by rfl⟩ : syracuseStep 762683 = 1144025) B1144025
theorem B1286999 : Blo 507795 1286999 := bstep (se 1 (by rfl) ⟨965249, by rfl⟩ : syracuseStep 1286999 = 1930499) B1930499
theorem B762743 : Blo 507795 762743 := bstep (se 1 (by rfl) ⟨572057, by rfl⟩ : syracuseStep 762743 = 1144115) B1144115
theorem B762767 : Blo 507795 762767 := bstep (se 1 (by rfl) ⟨572075, by rfl⟩ : syracuseStep 762767 = 1144151) B1144151
theorem B762809 : Blo 507795 762809 := bstep (se 2 (by rfl) ⟨286053, by rfl⟩ : syracuseStep 762809 = 572107) B572107
theorem B1942481 : Blo 507795 1942481 := bstep (se 2 (by rfl) ⟨728430, by rfl⟩ : syracuseStep 1942481 = 1456861) B1456861
theorem B762887 : Blo 507795 762887 := bstep (se 1 (by rfl) ⟨572165, by rfl⟩ : syracuseStep 762887 = 1144331) B1144331
theorem B1287211 : Blo 507795 1287211 := bstep (se 1 (by rfl) ⟨965408, by rfl⟩ : syracuseStep 1287211 = 1930817) B1930817
theorem B762923 : Blo 507795 762923 := bstep (se 1 (by rfl) ⟨572192, by rfl⟩ : syracuseStep 762923 = 1144385) B1144385
theorem B762953 : Blo 507795 762953 := bstep (se 2 (by rfl) ⟨286107, by rfl⟩ : syracuseStep 762953 = 572215) B572215
theorem B1451155 : Blo 507795 1451155 := bstep (se 1 (by rfl) ⟨1088366, by rfl⟩ : syracuseStep 1451155 = 2176733) B2176733
theorem B1287353 : Blo 507795 1287353 := bstep (se 2 (by rfl) ⟨482757, by rfl⟩ : syracuseStep 1287353 = 965515) B965515
theorem B763067 : Blo 507795 763067 := bstep (se 1 (by rfl) ⟨572300, by rfl⟩ : syracuseStep 763067 = 1144601) B1144601
theorem B1844461 : Blo 507795 1844461 := bstep (se 3 (by rfl) ⟨345836, by rfl⟩ : syracuseStep 1844461 = 691673) B691673
theorem B763127 : Blo 507795 763127 := bstep (se 1 (by rfl) ⟨572345, by rfl⟩ : syracuseStep 763127 = 1144691) B1144691
theorem B763151 : Blo 507795 763151 := bstep (se 1 (by rfl) ⟨572363, by rfl⟩ : syracuseStep 763151 = 1144727) B1144727
theorem B861455 : Blo 507795 861455 := bstep (se 1 (by rfl) ⟨646091, by rfl⟩ : syracuseStep 861455 = 1292183) B1292183
theorem B763193 : Blo 507795 763193 := bstep (se 2 (by rfl) ⟨286197, by rfl⟩ : syracuseStep 763193 = 572395) B572395
theorem B763271 : Blo 507795 763271 := bstep (se 1 (by rfl) ⟨572453, by rfl⟩ : syracuseStep 763271 = 1144907) B1144907
theorem B1942937 : Blo 507795 1942937 := bstep (se 2 (by rfl) ⟨728601, by rfl⟩ : syracuseStep 1942937 = 1457203) B1457203
theorem B763307 : Blo 507795 763307 := bstep (se 1 (by rfl) ⟨572480, by rfl⟩ : syracuseStep 763307 = 1144961) B1144961
theorem B763337 : Blo 507795 763337 := bstep (se 2 (by rfl) ⟨286251, by rfl⟩ : syracuseStep 763337 = 572503) B572503
theorem B8365517 : Blo 507795 8365517 := bstep (se 3 (by rfl) ⟨1568534, by rfl⟩ : syracuseStep 8365517 = 3137069) B3137069
theorem B2893265 : Blo 507795 2893265 := bstep (se 2 (by rfl) ⟨1084974, by rfl⟩ : syracuseStep 2893265 = 2169949) B2169949
theorem B763451 : Blo 507795 763451 := bstep (se 1 (by rfl) ⟨572588, by rfl⟩ : syracuseStep 763451 = 1145177) B1145177
theorem B22029893 : Blo 507795 22029893 := bstep (se 4 (by rfl) ⟨2065302, by rfl⟩ : syracuseStep 22029893 = 4130605) B4130605
theorem B763511 : Blo 507795 763511 := bstep (se 1 (by rfl) ⟨572633, by rfl⟩ : syracuseStep 763511 = 1145267) B1145267
theorem B763535 : Blo 507795 763535 := bstep (se 1 (by rfl) ⟨572651, by rfl⟩ : syracuseStep 763535 = 1145303) B1145303
theorem B763577 : Blo 507795 763577 := bstep (se 2 (by rfl) ⟨286341, by rfl⟩ : syracuseStep 763577 = 572683) B572683
theorem B763655 : Blo 507795 763655 := bstep (se 1 (by rfl) ⟨572741, by rfl⟩ : syracuseStep 763655 = 1145483) B1145483
theorem B2893583 : Blo 507795 2893583 := bstep (se 1 (by rfl) ⟨2170187, by rfl⟩ : syracuseStep 2893583 = 4340375) B4340375
theorem B1222415 : Blo 507795 1222415 := bstep (se 1 (by rfl) ⟨916811, by rfl⟩ : syracuseStep 1222415 = 1833623) B1833623
theorem B763691 : Blo 507795 763691 := bstep (se 1 (by rfl) ⟨572768, by rfl⟩ : syracuseStep 763691 = 1145537) B1145537
theorem B861995 : Blo 507795 861995 := bstep (se 1 (by rfl) ⟨646496, by rfl⟩ : syracuseStep 861995 = 1292993) B1292993
theorem B763721 : Blo 507795 763721 := bstep (se 2 (by rfl) ⟨286395, by rfl⟩ : syracuseStep 763721 = 572791) B572791
theorem B1714067 : Blo 507795 1714067 := bstep (se 1 (by rfl) ⟨1285550, by rfl⟩ : syracuseStep 1714067 = 2571101) B2571101
theorem B763835 : Blo 507795 763835 := bstep (se 1 (by rfl) ⟨572876, by rfl⟩ : syracuseStep 763835 = 1145753) B1145753
theorem B763895 : Blo 507795 763895 := bstep (se 1 (by rfl) ⟨572921, by rfl⟩ : syracuseStep 763895 = 1145843) B1145843
theorem B763919 : Blo 507795 763919 := bstep (se 1 (by rfl) ⟨572939, by rfl⟩ : syracuseStep 763919 = 1145879) B1145879
theorem B763961 : Blo 507795 763961 := bstep (se 2 (by rfl) ⟨286485, by rfl⟩ : syracuseStep 763961 = 572971) B572971
theorem B764039 : Blo 507795 764039 := bstep (se 1 (by rfl) ⟨573029, by rfl⟩ : syracuseStep 764039 = 1146059) B1146059
theorem B1288345 : Blo 507795 1288345 := bstep (se 2 (by rfl) ⟨483129, by rfl⟩ : syracuseStep 1288345 = 966259) B966259
theorem B764075 : Blo 507795 764075 := bstep (se 1 (by rfl) ⟨573056, by rfl⟩ : syracuseStep 764075 = 1146113) B1146113
theorem B1321145 : Blo 507795 1321145 := bstep (se 2 (by rfl) ⟨495429, by rfl⟩ : syracuseStep 1321145 = 990859) B990859
theorem B862393 : Blo 507795 862393 := bstep (se 2 (by rfl) ⟨323397, by rfl⟩ : syracuseStep 862393 = 646795) B646795
theorem B764105 : Blo 507795 764105 := bstep (se 2 (by rfl) ⟨286539, by rfl⟩ : syracuseStep 764105 = 573079) B573079
theorem B1288507 : Blo 507795 1288507 := bstep (se 1 (by rfl) ⟨966380, by rfl⟩ : syracuseStep 1288507 = 1932761) B1932761
theorem B764219 : Blo 507795 764219 := bstep (se 1 (by rfl) ⟨573164, by rfl⟩ : syracuseStep 764219 = 1146329) B1146329
theorem B764279 : Blo 507795 764279 := bstep (se 1 (by rfl) ⟨573209, by rfl⟩ : syracuseStep 764279 = 1146419) B1146419
theorem B764303 : Blo 507795 764303 := bstep (se 1 (by rfl) ⟨573227, by rfl⟩ : syracuseStep 764303 = 1146455) B1146455
theorem B2173331 : Blo 507795 2173331 := bstep (se 1 (by rfl) ⟨1629998, by rfl⟩ : syracuseStep 2173331 = 3259997) B3259997
theorem B6531475 : Blo 507795 6531475 := bstep (se 1 (by rfl) ⟨4898606, by rfl⟩ : syracuseStep 6531475 = 9797213) B9797213
theorem B764345 : Blo 507795 764345 := bstep (se 2 (by rfl) ⟨286629, by rfl⟩ : syracuseStep 764345 = 573259) B573259
theorem B1288649 : Blo 507795 1288649 := bstep (se 2 (by rfl) ⟨483243, by rfl⟩ : syracuseStep 1288649 = 966487) B966487
theorem B764423 : Blo 507795 764423 := bstep (se 1 (by rfl) ⟨573317, by rfl⟩ : syracuseStep 764423 = 1146635) B1146635
theorem B1223183 : Blo 507795 1223183 := bstep (se 1 (by rfl) ⟨917387, by rfl⟩ : syracuseStep 1223183 = 1834775) B1834775
theorem B764459 : Blo 507795 764459 := bstep (se 1 (by rfl) ⟨573344, by rfl⟩ : syracuseStep 764459 = 1146689) B1146689
theorem B764489 : Blo 507795 764489 := bstep (se 2 (by rfl) ⟨286683, by rfl⟩ : syracuseStep 764489 = 573367) B573367
theorem B764603 : Blo 507795 764603 := bstep (se 1 (by rfl) ⟨573452, by rfl⟩ : syracuseStep 764603 = 1146905) B1146905
theorem B764663 : Blo 507795 764663 := bstep (se 1 (by rfl) ⟨573497, by rfl⟩ : syracuseStep 764663 = 1146995) B1146995
theorem B1649423 : Blo 507795 1649423 := bstep (se 1 (by rfl) ⟨1237067, by rfl⟩ : syracuseStep 1649423 = 2474135) B2474135
theorem B764687 : Blo 507795 764687 := bstep (se 1 (by rfl) ⟨573515, by rfl⟩ : syracuseStep 764687 = 1147031) B1147031
theorem B1452829 : Blo 507795 1452829 := bstep (se 3 (by rfl) ⟨272405, by rfl⟩ : syracuseStep 1452829 = 544811) B544811
theorem B1288993 : Blo 507795 1288993 := bstep (se 2 (by rfl) ⟨483372, by rfl⟩ : syracuseStep 1288993 = 966745) B966745
theorem B764729 : Blo 507795 764729 := bstep (se 2 (by rfl) ⟨286773, by rfl⟩ : syracuseStep 764729 = 573547) B573547
theorem B1452887 : Blo 507795 1452887 := bstep (se 1 (by rfl) ⟨1089665, by rfl⟩ : syracuseStep 1452887 = 2179331) B2179331
theorem B863095 : Blo 507795 863095 := bstep (se 1 (by rfl) ⟨647321, by rfl⟩ : syracuseStep 863095 = 1294643) B1294643
theorem B764807 : Blo 507795 764807 := bstep (se 1 (by rfl) ⟨573605, by rfl⟩ : syracuseStep 764807 = 1147211) B1147211
theorem B764843 : Blo 507795 764843 := bstep (se 1 (by rfl) ⟨573632, by rfl⟩ : syracuseStep 764843 = 1147265) B1147265
theorem B764873 : Blo 507795 764873 := bstep (se 2 (by rfl) ⟨286827, by rfl⟩ : syracuseStep 764873 = 573655) B573655
theorem B764987 : Blo 507795 764987 := bstep (se 1 (by rfl) ⟨573740, by rfl⟩ : syracuseStep 764987 = 1147481) B1147481
theorem B863291 : Blo 507795 863291 := bstep (se 1 (by rfl) ⟨647468, by rfl⟩ : syracuseStep 863291 = 1294937) B1294937
theorem B765047 : Blo 507795 765047 := bstep (se 1 (by rfl) ⟨573785, by rfl⟩ : syracuseStep 765047 = 1147571) B1147571
theorem B765071 : Blo 507795 765071 := bstep (se 1 (by rfl) ⟨573803, by rfl⟩ : syracuseStep 765071 = 1147607) B1147607
theorem B765113 : Blo 507795 765113 := bstep (se 2 (by rfl) ⟨286917, by rfl⟩ : syracuseStep 765113 = 573835) B573835
theorem B2895041 : Blo 507795 2895041 := bstep (se 2 (by rfl) ⟨1085640, by rfl⟩ : syracuseStep 2895041 = 2171281) B2171281
theorem B765191 : Blo 507795 765191 := bstep (se 1 (by rfl) ⟨573893, by rfl⟩ : syracuseStep 765191 = 1147787) B1147787
theorem B1715471 : Blo 507795 1715471 := bstep (se 1 (by rfl) ⟨1286603, by rfl⟩ : syracuseStep 1715471 = 2573207) B2573207
theorem B765227 : Blo 507795 765227 := bstep (se 1 (by rfl) ⟨573920, by rfl⟩ : syracuseStep 765227 = 1147841) B1147841
theorem B765257 : Blo 507795 765257 := bstep (se 2 (by rfl) ⟨286971, by rfl⟩ : syracuseStep 765257 = 573943) B573943
theorem B2174323 : Blo 507795 2174323 := bstep (se 1 (by rfl) ⟨1630742, by rfl⟩ : syracuseStep 2174323 = 3261485) B3261485
theorem B1289591 : Blo 507795 1289591 := bstep (se 1 (by rfl) ⟨967193, by rfl⟩ : syracuseStep 1289591 = 1934387) B1934387
theorem B5811587 : Blo 507795 5811587 := bstep (se 1 (by rfl) ⟨4358690, by rfl⟩ : syracuseStep 5811587 = 8717381) B8717381
theorem B3878279 : Blo 507795 3878279 := bstep (se 1 (by rfl) ⟨2908709, by rfl⟩ : syracuseStep 3878279 = 5817419) B5817419
theorem B765371 : Blo 507795 765371 := bstep (se 1 (by rfl) ⟨574028, by rfl⟩ : syracuseStep 765371 = 1148057) B1148057
theorem B765431 : Blo 507795 765431 := bstep (se 1 (by rfl) ⟨574073, by rfl⟩ : syracuseStep 765431 = 1148147) B1148147
theorem B765455 : Blo 507795 765455 := bstep (se 1 (by rfl) ⟨574091, by rfl⟩ : syracuseStep 765455 = 1148183) B1148183
theorem B1715741 : Blo 507795 1715741 := bstep (se 3 (by rfl) ⟨321701, by rfl⟩ : syracuseStep 1715741 = 643403) B643403
theorem B765497 : Blo 507795 765497 := bstep (se 2 (by rfl) ⟨287061, by rfl⟩ : syracuseStep 765497 = 574123) B574123
theorem B3255875 : Blo 507795 3255875 := bstep (se 1 (by rfl) ⟨2441906, by rfl⟩ : syracuseStep 3255875 = 4883813) B4883813
theorem B765575 : Blo 507795 765575 := bstep (se 1 (by rfl) ⟨574181, by rfl⟩ : syracuseStep 765575 = 1148363) B1148363
theorem B765611 : Blo 507795 765611 := bstep (se 1 (by rfl) ⟨574208, by rfl⟩ : syracuseStep 765611 = 1148417) B1148417
theorem B765641 : Blo 507795 765641 := bstep (se 2 (by rfl) ⟨287115, by rfl⟩ : syracuseStep 765641 = 574231) B574231
theorem B765755 : Blo 507795 765755 := bstep (se 1 (by rfl) ⟨574316, by rfl⟩ : syracuseStep 765755 = 1148633) B1148633
theorem B765815 : Blo 507795 765815 := bstep (se 1 (by rfl) ⟨574361, by rfl⟩ : syracuseStep 765815 = 1148723) B1148723
theorem B765839 : Blo 507795 765839 := bstep (se 1 (by rfl) ⟨574379, by rfl⟩ : syracuseStep 765839 = 1148759) B1148759
theorem B1224595 : Blo 507795 1224595 := bstep (se 1 (by rfl) ⟨918446, by rfl⟩ : syracuseStep 1224595 = 1836893) B1836893
theorem B765881 : Blo 507795 765881 := bstep (se 2 (by rfl) ⟨287205, by rfl⟩ : syracuseStep 765881 = 574411) B574411
theorem B765959 : Blo 507795 765959 := bstep (se 1 (by rfl) ⟨574469, by rfl⟩ : syracuseStep 765959 = 1148939) B1148939
theorem B765995 : Blo 507795 765995 := bstep (se 1 (by rfl) ⟨574496, by rfl⟩ : syracuseStep 765995 = 1148993) B1148993
theorem B766025 : Blo 507795 766025 := bstep (se 2 (by rfl) ⟨287259, by rfl⟩ : syracuseStep 766025 = 574519) B574519
theorem B766139 : Blo 507795 766139 := bstep (se 1 (by rfl) ⟨574604, by rfl⟩ : syracuseStep 766139 = 1149209) B1149209
theorem B3092681 : Blo 507795 3092681 := bstep (se 2 (by rfl) ⟨1159755, by rfl⟩ : syracuseStep 3092681 = 2319511) B2319511
theorem B766199 : Blo 507795 766199 := bstep (se 1 (by rfl) ⟨574649, by rfl⟩ : syracuseStep 766199 = 1149299) B1149299
theorem B766223 : Blo 507795 766223 := bstep (se 1 (by rfl) ⟨574667, by rfl⟩ : syracuseStep 766223 = 1149335) B1149335
theorem B766265 : Blo 507795 766265 := bstep (se 2 (by rfl) ⟨287349, by rfl⟩ : syracuseStep 766265 = 574699) B574699
theorem B766343 : Blo 507795 766343 := bstep (se 1 (by rfl) ⟨574757, by rfl⟩ : syracuseStep 766343 = 1149515) B1149515
theorem B766379 : Blo 507795 766379 := bstep (se 1 (by rfl) ⟨574784, by rfl⟩ : syracuseStep 766379 = 1149569) B1149569
theorem B1454537 : Blo 507795 1454537 := bstep (se 2 (by rfl) ⟨545451, by rfl⟩ : syracuseStep 1454537 = 1090903) B1090903
theorem B766409 : Blo 507795 766409 := bstep (se 2 (by rfl) ⟨287403, by rfl⟩ : syracuseStep 766409 = 574807) B574807
theorem B766523 : Blo 507795 766523 := bstep (se 1 (by rfl) ⟨574892, by rfl⟩ : syracuseStep 766523 = 1149785) B1149785
theorem B766583 : Blo 507795 766583 := bstep (se 1 (by rfl) ⟨574937, by rfl⟩ : syracuseStep 766583 = 1149875) B1149875
theorem B1290887 : Blo 507795 1290887 := bstep (se 1 (by rfl) ⟨968165, by rfl⟩ : syracuseStep 1290887 = 1936331) B1936331
theorem B766607 : Blo 507795 766607 := bstep (se 1 (by rfl) ⟨574955, by rfl⟩ : syracuseStep 766607 = 1149911) B1149911
theorem B1290937 : Blo 507795 1290937 := bstep (se 2 (by rfl) ⟨484101, by rfl⟩ : syracuseStep 1290937 = 968203) B968203
theorem B766649 : Blo 507795 766649 := bstep (se 2 (by rfl) ⟨287493, by rfl⟩ : syracuseStep 766649 = 574987) B574987
theorem B766727 : Blo 507795 766727 := bstep (se 1 (by rfl) ⟨575045, by rfl⟩ : syracuseStep 766727 = 1150091) B1150091
theorem B5223203 : Blo 507795 5223203 := bstep (se 1 (by rfl) ⟨3917402, by rfl⟩ : syracuseStep 5223203 = 7834805) B7834805
theorem B8237861 : Blo 507795 8237861 := bstep (se 4 (by rfl) ⟨772299, by rfl⟩ : syracuseStep 8237861 = 1544599) B1544599
theorem B766763 : Blo 507795 766763 := bstep (se 1 (by rfl) ⟨575072, by rfl⟩ : syracuseStep 766763 = 1150145) B1150145
theorem B766793 : Blo 507795 766793 := bstep (se 2 (by rfl) ⟨287547, by rfl⟩ : syracuseStep 766793 = 575095) B575095
theorem B1717145 : Blo 507795 1717145 := bstep (se 2 (by rfl) ⟨643929, by rfl⟩ : syracuseStep 1717145 = 1287859) B1287859
theorem B2175929 : Blo 507795 2175929 := bstep (se 2 (by rfl) ⟨815973, by rfl⟩ : syracuseStep 2175929 = 1631947) B1631947
theorem B766907 : Blo 507795 766907 := bstep (se 1 (by rfl) ⟨575180, by rfl⟩ : syracuseStep 766907 = 1150361) B1150361
theorem B766967 : Blo 507795 766967 := bstep (se 1 (by rfl) ⟨575225, by rfl⟩ : syracuseStep 766967 = 1150451) B1150451
theorem B766991 : Blo 507795 766991 := bstep (se 1 (by rfl) ⟨575243, by rfl⟩ : syracuseStep 766991 = 1150487) B1150487
theorem B767033 : Blo 507795 767033 := bstep (se 2 (by rfl) ⟨287637, by rfl⟩ : syracuseStep 767033 = 575275) B575275
theorem B767111 : Blo 507795 767111 := bstep (se 1 (by rfl) ⟨575333, by rfl⟩ : syracuseStep 767111 = 1150667) B1150667
theorem B767147 : Blo 507795 767147 := bstep (se 1 (by rfl) ⟨575360, by rfl⟩ : syracuseStep 767147 = 1150721) B1150721
theorem B767177 : Blo 507795 767177 := bstep (se 2 (by rfl) ⟨287691, by rfl⟩ : syracuseStep 767177 = 575383) B575383
theorem B2176271 : Blo 507795 2176271 := bstep (se 1 (by rfl) ⟨1632203, by rfl⟩ : syracuseStep 2176271 = 3264407) B3264407
theorem B1291535 : Blo 507795 1291535 := bstep (se 1 (by rfl) ⟨968651, by rfl⟩ : syracuseStep 1291535 = 1937303) B1937303
theorem B1455403 : Blo 507795 1455403 := bstep (se 1 (by rfl) ⟨1091552, by rfl⟩ : syracuseStep 1455403 = 2183105) B2183105
theorem B767291 : Blo 507795 767291 := bstep (se 1 (by rfl) ⟨575468, by rfl⟩ : syracuseStep 767291 = 1150937) B1150937
theorem B767351 : Blo 507795 767351 := bstep (se 1 (by rfl) ⟨575513, by rfl⟩ : syracuseStep 767351 = 1151027) B1151027
theorem B767375 : Blo 507795 767375 := bstep (se 1 (by rfl) ⟨575531, by rfl⟩ : syracuseStep 767375 = 1151063) B1151063
theorem B767417 : Blo 507795 767417 := bstep (se 2 (by rfl) ⟨287781, by rfl⟩ : syracuseStep 767417 = 575563) B575563
theorem B767495 : Blo 507795 767495 := bstep (se 1 (by rfl) ⟨575621, by rfl⟩ : syracuseStep 767495 = 1151243) B1151243
theorem B767531 : Blo 507795 767531 := bstep (se 1 (by rfl) ⟨575648, by rfl⟩ : syracuseStep 767531 = 1151297) B1151297
theorem B1455677 : Blo 507795 1455677 := bstep (se 3 (by rfl) ⟨272939, by rfl⟩ : syracuseStep 1455677 = 545879) B545879
theorem B767561 : Blo 507795 767561 := bstep (se 2 (by rfl) ⟨287835, by rfl⟩ : syracuseStep 767561 = 575671) B575671
theorem B1717847 : Blo 507795 1717847 := bstep (se 1 (by rfl) ⟨1288385, by rfl⟩ : syracuseStep 1717847 = 2576771) B2576771
theorem B767675 : Blo 507795 767675 := bstep (se 1 (by rfl) ⟨575756, by rfl⟩ : syracuseStep 767675 = 1151513) B1151513
theorem B1226441 : Blo 507795 1226441 := bstep (se 2 (by rfl) ⟨459915, by rfl⟩ : syracuseStep 1226441 = 919831) B919831
theorem B571279 : Blo 507795 571279 := bstep (se 1 (by rfl) ⟨428459, by rfl⟩ : syracuseStep 571279 = 856919) B856919
theorem B1456019 : Blo 507795 1456019 := bstep (se 1 (by rfl) ⟨1092014, by rfl⟩ : syracuseStep 1456019 = 2184029) B2184029
theorem B1292233 : Blo 507795 1292233 := bstep (se 2 (by rfl) ⟨484587, by rfl⟩ : syracuseStep 1292233 = 969175) B969175
theorem B1226767 : Blo 507795 1226767 := bstep (se 1 (by rfl) ⟨920075, by rfl⟩ : syracuseStep 1226767 = 1840151) B1840151
theorem B6273047 : Blo 507795 6273047 := bstep (se 1 (by rfl) ⟨4704785, by rfl⟩ : syracuseStep 6273047 = 9409571) B9409571
theorem B1718333 : Blo 507795 1718333 := bstep (se 3 (by rfl) ⟨322187, by rfl⟩ : syracuseStep 1718333 = 644375) B644375
theorem B1292375 : Blo 507795 1292375 := bstep (se 1 (by rfl) ⟨969281, by rfl⟩ : syracuseStep 1292375 = 1938563) B1938563
theorem B571783 : Blo 507795 571783 := bstep (se 1 (by rfl) ⟨428837, by rfl⟩ : syracuseStep 571783 = 857675) B857675
theorem B3979655 : Blo 507795 3979655 := bstep (se 1 (by rfl) ⟨2984741, by rfl⟩ : syracuseStep 3979655 = 5969483) B5969483
theorem B6371731 : Blo 507795 6371731 := bstep (se 1 (by rfl) ⟨4778798, by rfl⟩ : syracuseStep 6371731 = 9557597) B9557597
theorem B965135 : Blo 507795 965135 := bstep (se 1 (by rfl) ⟨723851, by rfl⟩ : syracuseStep 965135 = 1447703) B1447703
theorem B571963 : Blo 507795 571963 := bstep (se 1 (by rfl) ⟨428972, by rfl⟩ : syracuseStep 571963 = 857945) B857945
theorem B1227383 : Blo 507795 1227383 := bstep (se 1 (by rfl) ⟨920537, by rfl⟩ : syracuseStep 1227383 = 1841075) B1841075
theorem B572431 : Blo 507795 572431 := bstep (se 1 (by rfl) ⟨429323, by rfl⟩ : syracuseStep 572431 = 858647) B858647
theorem B965675 : Blo 507795 965675 := bstep (se 1 (by rfl) ⟨724256, by rfl⟩ : syracuseStep 965675 = 1448513) B1448513
theorem B1555499 : Blo 507795 1555499 := bstep (se 1 (by rfl) ⟨1166624, by rfl⟩ : syracuseStep 1555499 = 2333249) B2333249
theorem B2440385 : Blo 507795 2440385 := bstep (se 2 (by rfl) ⟨915144, by rfl⟩ : syracuseStep 2440385 = 1830289) B1830289
theorem B6208757 : Blo 507795 6208757 := bstep (se 5 (by rfl) ⟨291035, by rfl⟩ : syracuseStep 6208757 = 582071) B582071
theorem B2800955 : Blo 507795 2800955 := bstep (se 1 (by rfl) ⟨2100716, by rfl⟩ : syracuseStep 2800955 = 4201433) B4201433
theorem B1719737 : Blo 507795 1719737 := bstep (se 2 (by rfl) ⟨644901, by rfl⟩ : syracuseStep 1719737 = 1289803) B1289803
theorem B572935 : Blo 507795 572935 := bstep (se 1 (by rfl) ⟨429701, by rfl⟩ : syracuseStep 572935 = 859403) B859403
theorem B2178647 : Blo 507795 2178647 := bstep (se 1 (by rfl) ⟨1633985, by rfl⟩ : syracuseStep 2178647 = 3267971) B3267971
theorem B573115 : Blo 507795 573115 := bstep (se 1 (by rfl) ⟨429836, by rfl⟩ : syracuseStep 573115 = 859673) B859673
theorem B507835 : Blo 507795 507835 := bstep (se 1 (by rfl) ⟨380876, by rfl⟩ : syracuseStep 507835 = 761753) B761753
theorem B2572235 : Blo 507795 2572235 := bstep (se 1 (by rfl) ⟨1929176, by rfl⟩ : syracuseStep 2572235 = 3858353) B3858353
theorem B507911 : Blo 507795 507911 := bstep (se 1 (by rfl) ⟨380933, by rfl⟩ : syracuseStep 507911 = 761867) B761867
theorem B1720331 : Blo 507795 1720331 := bstep (se 1 (by rfl) ⟨1290248, by rfl⟩ : syracuseStep 1720331 = 2580497) B2580497
theorem B2211851 : Blo 507795 2211851 := bstep (se 1 (by rfl) ⟨1658888, by rfl⟩ : syracuseStep 2211851 = 3317777) B3317777
theorem B3686411 : Blo 507795 3686411 := bstep (se 1 (by rfl) ⟨2764808, by rfl⟩ : syracuseStep 3686411 = 5529617) B5529617
theorem B507919 : Blo 507795 507919 := bstep (se 1 (by rfl) ⟨380939, by rfl⟩ : syracuseStep 507919 = 761879) B761879
theorem B507963 : Blo 507795 507963 := bstep (se 1 (by rfl) ⟨380972, by rfl⟩ : syracuseStep 507963 = 761945) B761945
theorem B1294451 : Blo 507795 1294451 := bstep (se 1 (by rfl) ⟨970838, by rfl⟩ : syracuseStep 1294451 = 1941677) B1941677
theorem B1720439 : Blo 507795 1720439 := bstep (se 1 (by rfl) ⟨1290329, by rfl⟩ : syracuseStep 1720439 = 2580659) B2580659
theorem B508039 : Blo 507795 508039 := bstep (se 1 (by rfl) ⟨381029, by rfl⟩ : syracuseStep 508039 = 762059) B762059
theorem B966791 : Blo 507795 966791 := bstep (se 1 (by rfl) ⟨725093, by rfl⟩ : syracuseStep 966791 = 1450187) B1450187
theorem B508047 : Blo 507795 508047 := bstep (se 1 (by rfl) ⟨381035, by rfl⟩ : syracuseStep 508047 = 762071) B762071
theorem B573583 : Blo 507795 573583 := bstep (se 1 (by rfl) ⟨430187, by rfl⟩ : syracuseStep 573583 = 860375) B860375
theorem B508091 : Blo 507795 508091 := bstep (se 1 (by rfl) ⟨381068, by rfl⟩ : syracuseStep 508091 = 762137) B762137
theorem B508167 : Blo 507795 508167 := bstep (se 1 (by rfl) ⟨381125, by rfl⟩ : syracuseStep 508167 = 762251) B762251
theorem B2572559 : Blo 507795 2572559 := bstep (se 1 (by rfl) ⟨1929419, by rfl⟩ : syracuseStep 2572559 = 3858839) B3858839
theorem B508175 : Blo 507795 508175 := bstep (se 1 (by rfl) ⟨381131, by rfl⟩ : syracuseStep 508175 = 762263) B762263
theorem B508219 : Blo 507795 508219 := bstep (se 1 (by rfl) ⟨381164, by rfl⟩ : syracuseStep 508219 = 762329) B762329
theorem B508295 : Blo 507795 508295 := bstep (se 1 (by rfl) ⟨381221, by rfl⟩ : syracuseStep 508295 = 762443) B762443
theorem B508303 : Blo 507795 508303 := bstep (se 1 (by rfl) ⟨381227, by rfl⟩ : syracuseStep 508303 = 762455) B762455
theorem B508347 : Blo 507795 508347 := bstep (se 1 (by rfl) ⟨381260, by rfl⟩ : syracuseStep 508347 = 762521) B762521
theorem B508423 : Blo 507795 508423 := bstep (se 1 (by rfl) ⟨381317, by rfl⟩ : syracuseStep 508423 = 762635) B762635
theorem B508431 : Blo 507795 508431 := bstep (se 1 (by rfl) ⟨381323, by rfl⟩ : syracuseStep 508431 = 762647) B762647
theorem B2441771 : Blo 507795 2441771 := bstep (se 1 (by rfl) ⟨1831328, by rfl⟩ : syracuseStep 2441771 = 3662657) B3662657
theorem B508475 : Blo 507795 508475 := bstep (se 1 (by rfl) ⟨381356, by rfl⟩ : syracuseStep 508475 = 762713) B762713
theorem B1294967 : Blo 507795 1294967 := bstep (se 1 (by rfl) ⟨971225, by rfl⟩ : syracuseStep 1294967 = 1942451) B1942451
theorem B508551 : Blo 507795 508551 := bstep (se 1 (by rfl) ⟨381413, by rfl⟩ : syracuseStep 508551 = 762827) B762827
theorem B574087 : Blo 507795 574087 := bstep (se 1 (by rfl) ⟨430565, by rfl⟩ : syracuseStep 574087 = 861131) B861131
theorem B508559 : Blo 507795 508559 := bstep (se 1 (by rfl) ⟨381419, by rfl⟩ : syracuseStep 508559 = 762839) B762839
theorem B967315 : Blo 507795 967315 := bstep (se 1 (by rfl) ⟨725486, by rfl⟩ : syracuseStep 967315 = 1450973) B1450973
theorem B508603 : Blo 507795 508603 := bstep (se 1 (by rfl) ⟨381452, by rfl⟩ : syracuseStep 508603 = 762905) B762905
theorem B1721033 : Blo 507795 1721033 := bstep (se 2 (by rfl) ⟨645387, by rfl⟩ : syracuseStep 1721033 = 1290775) B1290775
theorem B508679 : Blo 507795 508679 := bstep (se 1 (by rfl) ⟨381509, by rfl⟩ : syracuseStep 508679 = 763019) B763019
theorem B508687 : Blo 507795 508687 := bstep (se 1 (by rfl) ⟨381515, by rfl⟩ : syracuseStep 508687 = 763031) B763031
theorem B508731 : Blo 507795 508731 := bstep (se 1 (by rfl) ⟨381548, by rfl⟩ : syracuseStep 508731 = 763097) B763097
theorem B574267 : Blo 507795 574267 := bstep (se 1 (by rfl) ⟨430700, by rfl⟩ : syracuseStep 574267 = 861401) B861401
theorem B7324505 : Blo 507795 7324505 := bstep (se 2 (by rfl) ⟨2746689, by rfl⟩ : syracuseStep 7324505 = 5493379) B5493379
theorem B508807 : Blo 507795 508807 := bstep (se 1 (by rfl) ⟨381605, by rfl⟩ : syracuseStep 508807 = 763211) B763211
theorem B508815 : Blo 507795 508815 := bstep (se 1 (by rfl) ⟨381611, by rfl⟩ : syracuseStep 508815 = 763223) B763223
theorem B1164179 : Blo 507795 1164179 := bstep (se 1 (by rfl) ⟨873134, by rfl⟩ : syracuseStep 1164179 = 1746269) B1746269
theorem B508859 : Blo 507795 508859 := bstep (se 1 (by rfl) ⟨381644, by rfl⟩ : syracuseStep 508859 = 763289) B763289
theorem B508935 : Blo 507795 508935 := bstep (se 1 (by rfl) ⟨381701, by rfl⟩ : syracuseStep 508935 = 763403) B763403
theorem B508943 : Blo 507795 508943 := bstep (se 1 (by rfl) ⟨381707, by rfl⟩ : syracuseStep 508943 = 763415) B763415
theorem B508987 : Blo 507795 508987 := bstep (se 1 (by rfl) ⟨381740, by rfl⟩ : syracuseStep 508987 = 763481) B763481
theorem B509063 : Blo 507795 509063 := bstep (se 1 (by rfl) ⟨381797, by rfl⟩ : syracuseStep 509063 = 763595) B763595
theorem B509071 : Blo 507795 509071 := bstep (se 1 (by rfl) ⟨381803, by rfl⟩ : syracuseStep 509071 = 763607) B763607
theorem B509115 : Blo 507795 509115 := bstep (se 1 (by rfl) ⟨381836, by rfl⟩ : syracuseStep 509115 = 763673) B763673
theorem B509191 : Blo 507795 509191 := bstep (se 1 (by rfl) ⟨381893, by rfl⟩ : syracuseStep 509191 = 763787) B763787
theorem B509199 : Blo 507795 509199 := bstep (se 1 (by rfl) ⟨381899, by rfl⟩ : syracuseStep 509199 = 763799) B763799
theorem B574735 : Blo 507795 574735 := bstep (se 1 (by rfl) ⟨431051, by rfl⟩ : syracuseStep 574735 = 862103) B862103
theorem B509243 : Blo 507795 509243 := bstep (se 1 (by rfl) ⟨381932, by rfl⟩ : syracuseStep 509243 = 763865) B763865
theorem B509319 : Blo 507795 509319 := bstep (se 1 (by rfl) ⟨381989, by rfl⟩ : syracuseStep 509319 = 763979) B763979
theorem B1721735 : Blo 507795 1721735 := bstep (se 1 (by rfl) ⟨1291301, by rfl⟩ : syracuseStep 1721735 = 2582603) B2582603
theorem B509327 : Blo 507795 509327 := bstep (se 1 (by rfl) ⟨381995, by rfl⟩ : syracuseStep 509327 = 763991) B763991
theorem B509371 : Blo 507795 509371 := bstep (se 1 (by rfl) ⟨382028, by rfl⟩ : syracuseStep 509371 = 764057) B764057
theorem B509447 : Blo 507795 509447 := bstep (se 1 (by rfl) ⟨382085, by rfl⟩ : syracuseStep 509447 = 764171) B764171
theorem B509455 : Blo 507795 509455 := bstep (se 1 (by rfl) ⟨382091, by rfl⟩ : syracuseStep 509455 = 764183) B764183
theorem B509499 : Blo 507795 509499 := bstep (se 1 (by rfl) ⟨382124, by rfl⟩ : syracuseStep 509499 = 764249) B764249
theorem B509575 : Blo 507795 509575 := bstep (se 1 (by rfl) ⟨382181, by rfl⟩ : syracuseStep 509575 = 764363) B764363
theorem B509583 : Blo 507795 509583 := bstep (se 1 (by rfl) ⟨382187, by rfl⟩ : syracuseStep 509583 = 764375) B764375
theorem B509627 : Blo 507795 509627 := bstep (se 1 (by rfl) ⟨382220, by rfl⟩ : syracuseStep 509627 = 764441) B764441
theorem B2574017 : Blo 507795 2574017 := bstep (se 2 (by rfl) ⟨965256, by rfl⟩ : syracuseStep 2574017 = 1930513) B1930513
theorem B1722113 : Blo 507795 1722113 := bstep (se 2 (by rfl) ⟨645792, by rfl⟩ : syracuseStep 1722113 = 1291585) B1291585
theorem B509703 : Blo 507795 509703 := bstep (se 1 (by rfl) ⟨382277, by rfl⟩ : syracuseStep 509703 = 764555) B764555
theorem B575239 : Blo 507795 575239 := bstep (se 1 (by rfl) ⟨431429, by rfl⟩ : syracuseStep 575239 = 862859) B862859
theorem B509711 : Blo 507795 509711 := bstep (se 1 (by rfl) ⟨382283, by rfl⟩ : syracuseStep 509711 = 764567) B764567
theorem B509755 : Blo 507795 509755 := bstep (se 1 (by rfl) ⟨382316, by rfl⟩ : syracuseStep 509755 = 764633) B764633
theorem B968507 : Blo 507795 968507 := bstep (se 1 (by rfl) ⟨726380, by rfl⟩ : syracuseStep 968507 = 1452761) B1452761
theorem B10438517 : Blo 507795 10438517 := bstep (se 5 (by rfl) ⟨489305, by rfl⟩ : syracuseStep 10438517 = 978611) B978611
theorem B509831 : Blo 507795 509831 := bstep (se 1 (by rfl) ⟨382373, by rfl⟩ : syracuseStep 509831 = 764747) B764747
theorem B509839 : Blo 507795 509839 := bstep (se 1 (by rfl) ⟨382379, by rfl⟩ : syracuseStep 509839 = 764759) B764759
theorem B4638617 : Blo 507795 4638617 := bstep (se 2 (by rfl) ⟨1739481, by rfl⟩ : syracuseStep 4638617 = 3478963) B3478963
theorem B509883 : Blo 507795 509883 := bstep (se 1 (by rfl) ⟨382412, by rfl⟩ : syracuseStep 509883 = 764825) B764825
theorem B575419 : Blo 507795 575419 := bstep (se 1 (by rfl) ⟨431564, by rfl⟩ : syracuseStep 575419 = 863129) B863129
theorem B509959 : Blo 507795 509959 := bstep (se 1 (by rfl) ⟨382469, by rfl⟩ : syracuseStep 509959 = 764939) B764939
theorem B509967 : Blo 507795 509967 := bstep (se 1 (by rfl) ⟨382475, by rfl⟩ : syracuseStep 509967 = 764951) B764951
theorem B510011 : Blo 507795 510011 := bstep (se 1 (by rfl) ⟨382508, by rfl⟩ : syracuseStep 510011 = 765017) B765017
theorem B510087 : Blo 507795 510087 := bstep (se 1 (by rfl) ⟨382565, by rfl⟩ : syracuseStep 510087 = 765131) B765131
theorem B1165447 : Blo 507795 1165447 := bstep (se 1 (by rfl) ⟨874085, by rfl⟩ : syracuseStep 1165447 = 1748171) B1748171
theorem B510095 : Blo 507795 510095 := bstep (se 1 (by rfl) ⟨382571, by rfl⟩ : syracuseStep 510095 = 765143) B765143
theorem B510139 : Blo 507795 510139 := bstep (se 1 (by rfl) ⟨382604, by rfl⟩ : syracuseStep 510139 = 765209) B765209
theorem B1329353 : Blo 507795 1329353 := bstep (se 2 (by rfl) ⟨498507, by rfl⟩ : syracuseStep 1329353 = 997015) B997015
theorem B510215 : Blo 507795 510215 := bstep (se 1 (by rfl) ⟨382661, by rfl⟩ : syracuseStep 510215 = 765323) B765323
theorem B510223 : Blo 507795 510223 := bstep (se 1 (by rfl) ⟨382667, by rfl⟩ : syracuseStep 510223 = 765335) B765335
theorem B968993 : Blo 507795 968993 := bstep (se 2 (by rfl) ⟨363372, by rfl⟩ : syracuseStep 968993 = 726745) B726745
theorem B2902331 : Blo 507795 2902331 := bstep (se 1 (by rfl) ⟨2176748, by rfl⟩ : syracuseStep 2902331 = 4353497) B4353497
theorem B510267 : Blo 507795 510267 := bstep (se 1 (by rfl) ⟨382700, by rfl⟩ : syracuseStep 510267 = 765401) B765401
theorem B510343 : Blo 507795 510343 := bstep (se 1 (by rfl) ⟨382757, by rfl⟩ : syracuseStep 510343 = 765515) B765515
theorem B510351 : Blo 507795 510351 := bstep (se 1 (by rfl) ⟨382763, by rfl⟩ : syracuseStep 510351 = 765527) B765527
theorem B510395 : Blo 507795 510395 := bstep (se 1 (by rfl) ⟨382796, by rfl⟩ : syracuseStep 510395 = 765593) B765593
theorem B510471 : Blo 507795 510471 := bstep (se 1 (by rfl) ⟨382853, by rfl⟩ : syracuseStep 510471 = 765707) B765707
theorem B510479 : Blo 507795 510479 := bstep (se 1 (by rfl) ⟨382859, by rfl⟩ : syracuseStep 510479 = 765719) B765719
theorem B1722923 : Blo 507795 1722923 := bstep (se 1 (by rfl) ⟨1292192, by rfl⟩ : syracuseStep 1722923 = 2584385) B2584385
theorem B969259 : Blo 507795 969259 := bstep (se 1 (by rfl) ⟨726944, by rfl⟩ : syracuseStep 969259 = 1453889) B1453889
theorem B510523 : Blo 507795 510523 := bstep (se 1 (by rfl) ⟨382892, by rfl⟩ : syracuseStep 510523 = 765785) B765785
theorem B543367 : Blo 507795 543367 := bstep (se 1 (by rfl) ⟨407525, by rfl⟩ : syracuseStep 543367 = 815051) B815051
theorem B510599 : Blo 507795 510599 := bstep (se 1 (by rfl) ⟨382949, by rfl⟩ : syracuseStep 510599 = 765899) B765899
theorem B510607 : Blo 507795 510607 := bstep (se 1 (by rfl) ⟨382955, by rfl⟩ : syracuseStep 510607 = 765911) B765911
theorem B510651 : Blo 507795 510651 := bstep (se 1 (by rfl) ⟨382988, by rfl⟩ : syracuseStep 510651 = 765977) B765977
theorem B510727 : Blo 507795 510727 := bstep (se 1 (by rfl) ⟨383045, by rfl⟩ : syracuseStep 510727 = 766091) B766091
theorem B510735 : Blo 507795 510735 := bstep (se 1 (by rfl) ⟨383051, by rfl⟩ : syracuseStep 510735 = 766103) B766103
theorem B1166113 : Blo 507795 1166113 := bstep (se 2 (by rfl) ⟨437292, by rfl⟩ : syracuseStep 1166113 = 874585) B874585
theorem B543547 : Blo 507795 543547 := bstep (se 1 (by rfl) ⟨407660, by rfl⟩ : syracuseStep 543547 = 815321) B815321
theorem B510779 : Blo 507795 510779 := bstep (se 1 (by rfl) ⟨383084, by rfl⟩ : syracuseStep 510779 = 766169) B766169
theorem B510855 : Blo 507795 510855 := bstep (se 1 (by rfl) ⟨383141, by rfl⟩ : syracuseStep 510855 = 766283) B766283
theorem B510863 : Blo 507795 510863 := bstep (se 1 (by rfl) ⟨383147, by rfl⟩ : syracuseStep 510863 = 766295) B766295
theorem B510907 : Blo 507795 510907 := bstep (se 1 (by rfl) ⟨383180, by rfl⟩ : syracuseStep 510907 = 766361) B766361
theorem B2575313 : Blo 507795 2575313 := bstep (se 2 (by rfl) ⟨965742, by rfl⟩ : syracuseStep 2575313 = 1931485) B1931485
theorem B510983 : Blo 507795 510983 := bstep (se 1 (by rfl) ⟨383237, by rfl⟩ : syracuseStep 510983 = 766475) B766475
theorem B510991 : Blo 507795 510991 := bstep (se 1 (by rfl) ⟨383243, by rfl⟩ : syracuseStep 510991 = 766487) B766487
theorem B511035 : Blo 507795 511035 := bstep (se 1 (by rfl) ⟨383276, by rfl⟩ : syracuseStep 511035 = 766553) B766553
theorem B1789015 : Blo 507795 1789015 := bstep (se 1 (by rfl) ⟨1341761, by rfl⟩ : syracuseStep 1789015 = 2683523) B2683523
theorem B511111 : Blo 507795 511111 := bstep (se 1 (by rfl) ⟨383333, by rfl⟩ : syracuseStep 511111 = 766667) B766667
theorem B511119 : Blo 507795 511119 := bstep (se 1 (by rfl) ⟨383339, by rfl⟩ : syracuseStep 511119 = 766679) B766679
theorem B511163 : Blo 507795 511163 := bstep (se 1 (by rfl) ⟨383372, by rfl⟩ : syracuseStep 511163 = 766745) B766745
theorem B773321 : Blo 507795 773321 := bstep (se 2 (by rfl) ⟨289995, by rfl⟩ : syracuseStep 773321 = 579991) B579991
theorem B773383 : Blo 507795 773383 := bstep (se 1 (by rfl) ⟨580037, by rfl⟩ : syracuseStep 773383 = 1160075) B1160075
theorem B511239 : Blo 507795 511239 := bstep (se 1 (by rfl) ⟨383429, by rfl⟩ : syracuseStep 511239 = 766859) B766859
theorem B511247 : Blo 507795 511247 := bstep (se 1 (by rfl) ⟨383435, by rfl⟩ : syracuseStep 511247 = 766871) B766871
theorem B511291 : Blo 507795 511291 := bstep (se 1 (by rfl) ⟨383468, by rfl⟩ : syracuseStep 511291 = 766937) B766937
theorem B511367 : Blo 507795 511367 := bstep (se 1 (by rfl) ⟨383525, by rfl⟩ : syracuseStep 511367 = 767051) B767051
theorem B511375 : Blo 507795 511375 := bstep (se 1 (by rfl) ⟨383531, by rfl⟩ : syracuseStep 511375 = 767063) B767063
theorem B511419 : Blo 507795 511419 := bstep (se 1 (by rfl) ⟨383564, by rfl⟩ : syracuseStep 511419 = 767129) B767129
theorem B511495 : Blo 507795 511495 := bstep (se 1 (by rfl) ⟨383621, by rfl⟩ : syracuseStep 511495 = 767243) B767243
theorem B511503 : Blo 507795 511503 := bstep (se 1 (by rfl) ⟨383627, by rfl⟩ : syracuseStep 511503 = 767255) B767255
theorem B511547 : Blo 507795 511547 := bstep (se 1 (by rfl) ⟨383660, by rfl⟩ : syracuseStep 511547 = 767321) B767321
theorem B1035895 : Blo 507795 1035895 := bstep (se 1 (by rfl) ⟨776921, by rfl⟩ : syracuseStep 1035895 = 1553843) B1553843
theorem B970375 : Blo 507795 970375 := bstep (se 1 (by rfl) ⟨727781, by rfl⟩ : syracuseStep 970375 = 1455563) B1455563
theorem B511623 : Blo 507795 511623 := bstep (se 1 (by rfl) ⟨383717, by rfl⟩ : syracuseStep 511623 = 767435) B767435
theorem B511631 : Blo 507795 511631 := bstep (se 1 (by rfl) ⟨383723, by rfl⟩ : syracuseStep 511631 = 767447) B767447
theorem B511675 : Blo 507795 511675 := bstep (se 1 (by rfl) ⟨383756, by rfl⟩ : syracuseStep 511675 = 767513) B767513
theorem B872137 : Blo 507795 872137 := bstep (se 2 (by rfl) ⟨327051, by rfl⟩ : syracuseStep 872137 = 654103) B654103
theorem B2903789 : Blo 507795 2903789 := bstep (se 3 (by rfl) ⟨544460, by rfl⟩ : syracuseStep 2903789 = 1088921) B1088921
theorem B511751 : Blo 507795 511751 := bstep (se 1 (by rfl) ⟨383813, by rfl⟩ : syracuseStep 511751 = 767627) B767627
theorem B511759 : Blo 507795 511759 := bstep (se 1 (by rfl) ⟨383819, by rfl⟩ : syracuseStep 511759 = 767639) B767639
theorem B1724219 : Blo 507795 1724219 := bstep (se 1 (by rfl) ⟨1293164, by rfl⟩ : syracuseStep 1724219 = 2586329) B2586329
theorem B643079 : Blo 507795 643079 := bstep (se 1 (by rfl) ⟨482309, by rfl⟩ : syracuseStep 643079 = 964619) B964619
theorem B970937 : Blo 507795 970937 := bstep (se 2 (by rfl) ⟨364101, by rfl⟩ : syracuseStep 970937 = 728203) B728203
theorem B7852301 : Blo 507795 7852301 := bstep (se 3 (by rfl) ⟨1472306, by rfl⟩ : syracuseStep 7852301 = 2944613) B2944613
theorem B1724705 : Blo 507795 1724705 := bstep (se 2 (by rfl) ⟨646764, by rfl⟩ : syracuseStep 1724705 = 1293529) B1293529
theorem B643727 : Blo 507795 643727 := bstep (se 1 (by rfl) ⟨482795, by rfl⟩ : syracuseStep 643727 = 965591) B965591
theorem B873161 : Blo 507795 873161 := bstep (se 2 (by rfl) ⟨327435, by rfl⟩ : syracuseStep 873161 = 654871) B654871
theorem B1725299 : Blo 507795 1725299 := bstep (se 1 (by rfl) ⟨1293974, by rfl⟩ : syracuseStep 1725299 = 2587949) B2587949
theorem B3265433 : Blo 507795 3265433 := bstep (se 2 (by rfl) ⟨1224537, by rfl⟩ : syracuseStep 3265433 = 2449075) B2449075
theorem B2577419 : Blo 507795 2577419 := bstep (se 1 (by rfl) ⟨1933064, by rfl⟩ : syracuseStep 2577419 = 3866129) B3866129
theorem B2577581 : Blo 507795 2577581 := bstep (se 3 (by rfl) ⟨483296, by rfl⟩ : syracuseStep 2577581 = 966593) B966593
theorem B4904225 : Blo 507795 4904225 := bstep (se 2 (by rfl) ⟨1839084, by rfl⟩ : syracuseStep 4904225 = 3678169) B3678169
theorem B7329457 : Blo 507795 7329457 := bstep (se 2 (by rfl) ⟨2748546, by rfl⟩ : syracuseStep 7329457 = 5497093) B5497093
theorem B2185019 : Blo 507795 2185019 := bstep (se 1 (by rfl) ⟨1638764, by rfl⟩ : syracuseStep 2185019 = 3277529) B3277529
theorem B1628039 : Blo 507795 1628039 := bstep (se 1 (by rfl) ⟨1221029, by rfl⟩ : syracuseStep 1628039 = 2442059) B2442059
theorem B2448073 : Blo 507795 2448073 := bstep (se 2 (by rfl) ⟨918027, by rfl⟩ : syracuseStep 2448073 = 1836055) B1836055
theorem B2579201 : Blo 507795 2579201 := bstep (se 2 (by rfl) ⟨967200, by rfl⟩ : syracuseStep 2579201 = 1934401) B1934401
theorem B514831 : Blo 507795 514831 := bstep (se 1 (by rfl) ⟨386123, by rfl⟩ : syracuseStep 514831 = 772247) B772247
theorem B5233709 : Blo 507795 5233709 := bstep (se 3 (by rfl) ⟨981320, by rfl⟩ : syracuseStep 5233709 = 1962641) B1962641
theorem B2580011 : Blo 507795 2580011 := bstep (se 1 (by rfl) ⟨1935008, by rfl⟩ : syracuseStep 2580011 = 3870017) B3870017
theorem B646699 : Blo 507795 646699 := bstep (se 1 (by rfl) ⟨485024, by rfl⟩ : syracuseStep 646699 = 970049) B970049
theorem B1007239 : Blo 507795 1007239 := bstep (se 1 (by rfl) ⟨755429, by rfl⟩ : syracuseStep 1007239 = 1510859) B1510859
theorem B2908163 : Blo 507795 2908163 := bstep (se 1 (by rfl) ⟨2181122, by rfl⟩ : syracuseStep 2908163 = 4362245) B4362245
theorem B614671 : Blo 507795 614671 := bstep (se 1 (by rfl) ⟨461003, by rfl⟩ : syracuseStep 614671 = 922007) B922007
theorem B2908619 : Blo 507795 2908619 := bstep (se 1 (by rfl) ⟨2181464, by rfl⟩ : syracuseStep 2908619 = 4362929) B4362929
theorem B647671 : Blo 507795 647671 := bstep (se 1 (by rfl) ⟨485753, by rfl⟩ : syracuseStep 647671 = 971507) B971507
theorem B2581307 : Blo 507795 2581307 := bstep (se 1 (by rfl) ⟨1935980, by rfl⟩ : syracuseStep 2581307 = 3871961) B3871961
theorem B2581469 : Blo 507795 2581469 := bstep (se 3 (by rfl) ⟨484025, by rfl⟩ : syracuseStep 2581469 = 968051) B968051
theorem B2450519 : Blo 507795 2450519 := bstep (se 1 (by rfl) ⟨1837889, by rfl⟩ : syracuseStep 2450519 = 3675779) B3675779
theorem B2909303 : Blo 507795 2909303 := bstep (se 1 (by rfl) ⟨2181977, by rfl⟩ : syracuseStep 2909303 = 4363955) B4363955
theorem B20997251 : Blo 507795 20997251 := bstep (se 1 (by rfl) ⟨15747938, by rfl⟩ : syracuseStep 20997251 = 31495877) B31495877
theorem B3105985 : Blo 507795 3105985 := bstep (se 2 (by rfl) ⟨1164744, by rfl⟩ : syracuseStep 3105985 = 2329489) B2329489
theorem B2581793 : Blo 507795 2581793 := bstep (se 2 (by rfl) ⟨968172, by rfl⟩ : syracuseStep 2581793 = 1936345) B1936345
theorem B6514253 : Blo 507795 6514253 := bstep (se 3 (by rfl) ⟨1221422, by rfl⟩ : syracuseStep 6514253 = 2442845) B2442845
theorem B5826167 : Blo 507795 5826167 := bstep (se 1 (by rfl) ⟨4369625, by rfl⟩ : syracuseStep 5826167 = 8739251) B8739251
theorem B4908721 : Blo 507795 4908721 := bstep (se 2 (by rfl) ⟨1840770, by rfl⟩ : syracuseStep 4908721 = 3681541) B3681541
theorem B2582765 : Blo 507795 2582765 := bstep (se 3 (by rfl) ⟨484268, by rfl⟩ : syracuseStep 2582765 = 968537) B968537
theorem B813769 : Blo 507795 813769 := bstep (se 2 (by rfl) ⟨305163, by rfl⟩ : syracuseStep 813769 = 610327) B610327
theorem B1928083 : Blo 507795 1928083 := bstep (se 1 (by rfl) ⟨1446062, by rfl⟩ : syracuseStep 1928083 = 2892125) B2892125
theorem B2583575 : Blo 507795 2583575 := bstep (se 1 (by rfl) ⟨1937681, by rfl⟩ : syracuseStep 2583575 = 3875363) B3875363
theorem B2911261 : Blo 507795 2911261 := bstep (se 3 (by rfl) ⟨545861, by rfl⟩ : syracuseStep 2911261 = 1091723) B1091723
theorem B1240183 : Blo 507795 1240183 := bstep (se 1 (by rfl) ⟨930137, by rfl⟩ : syracuseStep 1240183 = 1860275) B1860275
theorem B2911787 : Blo 507795 2911787 := bstep (se 1 (by rfl) ⟨2183840, by rfl⟩ : syracuseStep 2911787 = 4367681) B4367681
theorem B1142675 : Blo 507795 1142675 := bstep (se 1 (by rfl) ⟨857006, by rfl⟩ : syracuseStep 1142675 = 1714013) B1714013
theorem B1142729 : Blo 507795 1142729 := bstep (se 2 (by rfl) ⟨428523, by rfl⟩ : syracuseStep 1142729 = 857047) B857047
theorem B4354181 : Blo 507795 4354181 := bstep (se 4 (by rfl) ⟨408204, by rfl⟩ : syracuseStep 4354181 = 816409) B816409
theorem B1929815 : Blo 507795 1929815 := bstep (se 1 (by rfl) ⟨1447361, by rfl⟩ : syracuseStep 1929815 = 2894723) B2894723
theorem B1143431 : Blo 507795 1143431 := bstep (se 1 (by rfl) ⟨857573, by rfl⟩ : syracuseStep 1143431 = 1715147) B1715147
theorem B2454209 : Blo 507795 2454209 := bstep (se 2 (by rfl) ⟨920328, by rfl⟩ : syracuseStep 2454209 = 1840657) B1840657
theorem B1143611 : Blo 507795 1143611 := bstep (se 1 (by rfl) ⟨857708, by rfl⟩ : syracuseStep 1143611 = 1715417) B1715417
theorem B1143737 : Blo 507795 1143737 := bstep (se 2 (by rfl) ⟨428901, by rfl⟩ : syracuseStep 1143737 = 857803) B857803
theorem B2749393 : Blo 507795 2749393 := bstep (se 2 (by rfl) ⟨1031022, by rfl⟩ : syracuseStep 2749393 = 2062045) B2062045
theorem B2913245 : Blo 507795 2913245 := bstep (se 3 (by rfl) ⟨546233, by rfl⟩ : syracuseStep 2913245 = 1092467) B1092467
theorem B4912139 : Blo 507795 4912139 := bstep (se 1 (by rfl) ⟨3684104, by rfl⟩ : syracuseStep 4912139 = 7368209) B7368209
theorem B1930301 : Blo 507795 1930301 := bstep (se 3 (by rfl) ⟨361931, by rfl⟩ : syracuseStep 1930301 = 723863) B723863
theorem B1144079 : Blo 507795 1144079 := bstep (se 1 (by rfl) ⟨858059, by rfl⟩ : syracuseStep 1144079 = 1716119) B1716119
theorem B1144097 : Blo 507795 1144097 := bstep (se 2 (by rfl) ⟨429036, by rfl⟩ : syracuseStep 1144097 = 858073) B858073
theorem B7337249 : Blo 507795 7337249 := bstep (se 2 (by rfl) ⟨2751468, by rfl⟩ : syracuseStep 7337249 = 5502937) B5502937
theorem B16774685 : Blo 507795 16774685 := bstep (se 3 (by rfl) ⟨3145253, by rfl⟩ : syracuseStep 16774685 = 6290507) B6290507
theorem B1635869 : Blo 507795 1635869 := bstep (se 3 (by rfl) ⟨306725, by rfl⟩ : syracuseStep 1635869 = 613451) B613451
theorem B1373755 : Blo 507795 1373755 := bstep (se 1 (by rfl) ⟨1030316, by rfl⟩ : syracuseStep 1373755 = 2060633) B2060633
theorem B22410827 : Blo 507795 22410827 := bstep (se 1 (by rfl) ⟨16808120, by rfl⟩ : syracuseStep 22410827 = 33616241) B33616241
theorem B5797453 : Blo 507795 5797453 := bstep (se 3 (by rfl) ⟨1087022, by rfl⟩ : syracuseStep 5797453 = 2174045) B2174045
theorem B1144439 : Blo 507795 1144439 := bstep (se 1 (by rfl) ⟨858329, by rfl⟩ : syracuseStep 1144439 = 1716659) B1716659
theorem B2062061 : Blo 507795 2062061 := bstep (se 3 (by rfl) ⟨386636, by rfl⟩ : syracuseStep 2062061 = 773273) B773273
theorem B1144619 : Blo 507795 1144619 := bstep (se 1 (by rfl) ⟨858464, by rfl⟩ : syracuseStep 1144619 = 1716929) B1716929
theorem B4650803 : Blo 507795 4650803 := bstep (se 1 (by rfl) ⟨3488102, by rfl⟩ : syracuseStep 4650803 = 6976205) B6976205
theorem B915347 : Blo 507795 915347 := bstep (se 1 (by rfl) ⟨686510, by rfl⟩ : syracuseStep 915347 = 1373021) B1373021
theorem B2586653 : Blo 507795 2586653 := bstep (se 3 (by rfl) ⟨484997, by rfl⟩ : syracuseStep 2586653 = 969995) B969995
theorem B1144979 : Blo 507795 1144979 := bstep (se 1 (by rfl) ⟨858734, by rfl⟩ : syracuseStep 1144979 = 1717469) B1717469
theorem B1145033 : Blo 507795 1145033 := bstep (se 2 (by rfl) ⟨429387, by rfl⟩ : syracuseStep 1145033 = 858775) B858775
theorem B2062745 : Blo 507795 2062745 := bstep (se 2 (by rfl) ⟨773529, by rfl⟩ : syracuseStep 2062745 = 1547059) B1547059
theorem B2587139 : Blo 507795 2587139 := bstep (se 1 (by rfl) ⟨1940354, by rfl⟩ : syracuseStep 2587139 = 3880709) B3880709
theorem B5798465 : Blo 507795 5798465 := bstep (se 2 (by rfl) ⟨2174424, by rfl⟩ : syracuseStep 5798465 = 4348849) B4348849
theorem B7371557 : Blo 507795 7371557 := bstep (se 4 (by rfl) ⟨691083, by rfl⟩ : syracuseStep 7371557 = 1382167) B1382167
theorem B1145735 : Blo 507795 1145735 := bstep (se 1 (by rfl) ⟨859301, by rfl⟩ : syracuseStep 1145735 = 1718603) B1718603
theorem B818191 : Blo 507795 818191 := bstep (se 1 (by rfl) ⟨613643, by rfl⟩ : syracuseStep 818191 = 1227287) B1227287
theorem B1145915 : Blo 507795 1145915 := bstep (se 1 (by rfl) ⟨859436, by rfl⟩ : syracuseStep 1145915 = 1718873) B1718873
theorem B916615 : Blo 507795 916615 := bstep (se 1 (by rfl) ⟨687461, by rfl⟩ : syracuseStep 916615 = 1374923) B1374923
theorem B1146041 : Blo 507795 1146041 := bstep (se 2 (by rfl) ⟨429765, by rfl⟩ : syracuseStep 1146041 = 859531) B859531
theorem B1637779 : Blo 507795 1637779 := bstep (se 1 (by rfl) ⟨1228334, by rfl⟩ : syracuseStep 1637779 = 2456669) B2456669
theorem B818633 : Blo 507795 818633 := bstep (se 2 (by rfl) ⟨306987, by rfl⟩ : syracuseStep 818633 = 613975) B613975
theorem B9305549 : Blo 507795 9305549 := bstep (se 3 (by rfl) ⟨1744790, by rfl⟩ : syracuseStep 9305549 = 3489581) B3489581
theorem B4357597 : Blo 507795 4357597 := bstep (se 3 (by rfl) ⟨817049, by rfl⟩ : syracuseStep 4357597 = 1634099) B1634099
theorem B1146383 : Blo 507795 1146383 := bstep (se 1 (by rfl) ⟨859787, by rfl⟩ : syracuseStep 1146383 = 1719575) B1719575
theorem B1146401 : Blo 507795 1146401 := bstep (se 2 (by rfl) ⟨429900, by rfl⟩ : syracuseStep 1146401 = 859801) B859801
theorem B67927853 : Blo 507795 67927853 := bstep (se 3 (by rfl) ⟨12736472, by rfl⟩ : syracuseStep 67927853 = 25472945) B25472945
theorem B1146743 : Blo 507795 1146743 := bstep (se 1 (by rfl) ⟨860057, by rfl⟩ : syracuseStep 1146743 = 1720115) B1720115
theorem B12058571 : Blo 507795 12058571 := bstep (se 1 (by rfl) ⟨9043928, by rfl⟩ : syracuseStep 12058571 = 18087857) B18087857
theorem B1146887 : Blo 507795 1146887 := bstep (se 1 (by rfl) ⟨860165, by rfl⟩ : syracuseStep 1146887 = 1720331) B1720331
theorem B5898269 : Blo 507795 5898269 := bstep (se 3 (by rfl) ⟨1105925, by rfl⟩ : syracuseStep 5898269 = 2211851) B2211851
theorem B9830429 : Blo 507795 9830429 := bstep (se 3 (by rfl) ⟨1843205, by rfl⟩ : syracuseStep 9830429 = 3686411) B3686411
theorem B917561 : Blo 507795 917561 := bstep (se 2 (by rfl) ⟨344085, by rfl⟩ : syracuseStep 917561 = 688171) B688171
theorem B1146959 : Blo 507795 1146959 := bstep (se 1 (by rfl) ⟨860219, by rfl⟩ : syracuseStep 1146959 = 1720439) B1720439
theorem B2621783 : Blo 507795 2621783 := bstep (se 1 (by rfl) ⟨1966337, by rfl⟩ : syracuseStep 2621783 = 3932675) B3932675
theorem B1147355 : Blo 507795 1147355 := bstep (se 1 (by rfl) ⟨860516, by rfl⟩ : syracuseStep 1147355 = 1721033) B1721033
theorem B14680601 : Blo 507795 14680601 := bstep (se 2 (by rfl) ⟨5505225, by rfl⟩ : syracuseStep 14680601 = 11010451) B11010451
theorem B4883003 : Blo 507795 4883003 := bstep (se 1 (by rfl) ⟨3662252, by rfl⟩ : syracuseStep 4883003 = 7324505) B7324505
theorem B524999 : Blo 507795 524999 := bstep (se 1 (by rfl) ⟨393749, by rfl⟩ : syracuseStep 524999 = 787499) B787499
theorem B1639111 : Blo 507795 1639111 := bstep (se 1 (by rfl) ⟨1229333, by rfl⟩ : syracuseStep 1639111 = 2458667) B2458667
theorem B8389331 : Blo 507795 8389331 := bstep (se 1 (by rfl) ⟨6291998, by rfl⟩ : syracuseStep 8389331 = 12583997) B12583997
theorem B1835885 : Blo 507795 1835885 := bstep (se 3 (by rfl) ⟨344228, by rfl⟩ : syracuseStep 1835885 = 688457) B688457
theorem B1934189 : Blo 507795 1934189 := bstep (se 3 (by rfl) ⟨362660, by rfl⟩ : syracuseStep 1934189 = 725321) B725321
theorem B3539857 : Blo 507795 3539857 := bstep (se 2 (by rfl) ⟨1327446, by rfl⟩ : syracuseStep 3539857 = 2654893) B2654893
theorem B1147823 : Blo 507795 1147823 := bstep (se 1 (by rfl) ⟨860867, by rfl⟩ : syracuseStep 1147823 = 1721735) B1721735
theorem B1311671 : Blo 507795 1311671 := bstep (se 1 (by rfl) ⟨983753, by rfl⟩ : syracuseStep 1311671 = 1967507) B1967507
theorem B1148075 : Blo 507795 1148075 := bstep (se 1 (by rfl) ⟨861056, by rfl⟩ : syracuseStep 1148075 = 1722113) B1722113
theorem B5801381 : Blo 507795 5801381 := bstep (se 4 (by rfl) ⟨543879, by rfl⟩ : syracuseStep 5801381 = 1087759) B1087759
theorem B3278245 : Blo 507795 3278245 := bstep (se 4 (by rfl) ⟨307335, by rfl⟩ : syracuseStep 3278245 = 614671) B614671
theorem B886235 : Blo 507795 886235 := bstep (se 1 (by rfl) ⟨664676, by rfl⟩ : syracuseStep 886235 = 1329353) B1329353
theorem B1934873 : Blo 507795 1934873 := bstep (se 2 (by rfl) ⟨725577, by rfl⟩ : syracuseStep 1934873 = 1451155) B1451155
theorem B1934887 : Blo 507795 1934887 := bstep (se 1 (by rfl) ⟨1451165, by rfl⟩ : syracuseStep 1934887 = 2902331) B2902331
theorem B1377931 : Blo 507795 1377931 := bstep (se 1 (by rfl) ⟨1033448, by rfl⟩ : syracuseStep 1377931 = 2066897) B2066897
theorem B1148615 : Blo 507795 1148615 := bstep (se 1 (by rfl) ⟨861461, by rfl⟩ : syracuseStep 1148615 = 1722923) B1722923
theorem B5507129 : Blo 507795 5507129 := bstep (se 2 (by rfl) ⟨2065173, by rfl⟩ : syracuseStep 5507129 = 4130347) B4130347
theorem B1935677 : Blo 507795 1935677 := bstep (se 3 (by rfl) ⟨362939, by rfl⟩ : syracuseStep 1935677 = 725879) B725879
theorem B1935859 : Blo 507795 1935859 := bstep (se 1 (by rfl) ⟨1451894, by rfl⟩ : syracuseStep 1935859 = 2903789) B2903789
theorem B1149479 : Blo 507795 1149479 := bstep (se 1 (by rfl) ⟨862109, by rfl⟩ : syracuseStep 1149479 = 1724219) B1724219
theorem B2689595 : Blo 507795 2689595 := bstep (se 1 (by rfl) ⟨2017196, by rfl⟩ : syracuseStep 2689595 = 4034393) B4034393
theorem B920393 : Blo 507795 920393 := bstep (se 2 (by rfl) ⟨345147, by rfl⟩ : syracuseStep 920393 = 690295) B690295
theorem B1149803 : Blo 507795 1149803 := bstep (se 1 (by rfl) ⟨862352, by rfl⟩ : syracuseStep 1149803 = 1724705) B1724705
theorem B1149857 : Blo 507795 1149857 := bstep (se 2 (by rfl) ⟨431196, by rfl⟩ : syracuseStep 1149857 = 862393) B862393
theorem B1150199 : Blo 507795 1150199 := bstep (se 1 (by rfl) ⟨862649, by rfl⟩ : syracuseStep 1150199 = 1725299) B1725299
theorem B5312087 : Blo 507795 5312087 := bstep (se 1 (by rfl) ⟨3984065, by rfl⟩ : syracuseStep 5312087 = 7968131) B7968131
theorem B1937105 : Blo 507795 1937105 := bstep (se 2 (by rfl) ⟨726414, by rfl⟩ : syracuseStep 1937105 = 1452829) B1452829
theorem B724729 : Blo 507795 724729 := bstep (se 2 (by rfl) ⟨271773, by rfl⟩ : syracuseStep 724729 = 543547) B543547
theorem B1150793 : Blo 507795 1150793 := bstep (se 2 (by rfl) ⟨431547, by rfl⟩ : syracuseStep 1150793 = 863095) B863095
theorem B1937789 : Blo 507795 1937789 := bstep (se 3 (by rfl) ⟨363335, by rfl⟩ : syracuseStep 1937789 = 726671) B726671
theorem B922151 : Blo 507795 922151 := bstep (se 1 (by rfl) ⟨691613, by rfl⟩ : syracuseStep 922151 = 1383227) B1383227
theorem B6296237 : Blo 507795 6296237 := bstep (se 3 (by rfl) ⟨1180544, by rfl⟩ : syracuseStep 6296237 = 2361089) B2361089
theorem B1446599 : Blo 507795 1446599 := bstep (se 1 (by rfl) ⟨1084949, by rfl⟩ : syracuseStep 1446599 = 2169899) B2169899
theorem B10490579 : Blo 507795 10490579 := bstep (se 1 (by rfl) ⟨7867934, by rfl⟩ : syracuseStep 10490579 = 15735869) B15735869
theorem B1381193 : Blo 507795 1381193 := bstep (se 2 (by rfl) ⟨517947, by rfl⟩ : syracuseStep 1381193 = 1035895) B1035895
theorem B856939 : Blo 507795 856939 := bstep (se 1 (by rfl) ⟨642704, by rfl⟩ : syracuseStep 856939 = 1285409) B1285409
theorem B1840207 : Blo 507795 1840207 := bstep (se 1 (by rfl) ⟨1380155, by rfl⟩ : syracuseStep 1840207 = 2760311) B2760311
theorem B1938775 : Blo 507795 1938775 := bstep (se 1 (by rfl) ⟨1454081, by rfl⟩ : syracuseStep 1938775 = 2908163) B2908163
theorem B1939079 : Blo 507795 1939079 := bstep (se 1 (by rfl) ⟨1454309, by rfl⟩ : syracuseStep 1939079 = 2908619) B2908619
theorem B857999 : Blo 507795 857999 := bstep (se 1 (by rfl) ⟨643499, by rfl⟩ : syracuseStep 857999 = 1286999) B1286999
theorem B4888613 : Blo 507795 4888613 := bstep (se 4 (by rfl) ⟨458307, by rfl⟩ : syracuseStep 4888613 = 916615) B916615
theorem B1939535 : Blo 507795 1939535 := bstep (se 1 (by rfl) ⟨1454651, by rfl⟩ : syracuseStep 1939535 = 2909303) B2909303
theorem B13998167 : Blo 507795 13998167 := bstep (se 1 (by rfl) ⟨10498625, by rfl⟩ : syracuseStep 13998167 = 20997251) B20997251
theorem B858235 : Blo 507795 858235 := bstep (se 1 (by rfl) ⟨643676, by rfl⟩ : syracuseStep 858235 = 1287353) B1287353
theorem B5577011 : Blo 507795 5577011 := bstep (se 1 (by rfl) ⟨4182758, by rfl⟩ : syracuseStep 5577011 = 8365517) B8365517
theorem B14686595 : Blo 507795 14686595 := bstep (se 1 (by rfl) ⟨11014946, by rfl⟩ : syracuseStep 14686595 = 22029893) B22029893
theorem B3545633 : Blo 507795 3545633 := bstep (se 2 (by rfl) ⟨1329612, by rfl⟩ : syracuseStep 3545633 = 2659225) B2659225
theorem B9837125 : Blo 507795 9837125 := bstep (se 4 (by rfl) ⟨922230, by rfl⟩ : syracuseStep 9837125 = 1844461) B1844461
theorem B859099 : Blo 507795 859099 := bstep (se 1 (by rfl) ⟨644324, by rfl⟩ : syracuseStep 859099 = 1288649) B1288649
theorem B1940537 : Blo 507795 1940537 := bstep (se 2 (by rfl) ⟨727701, by rfl⟩ : syracuseStep 1940537 = 1455403) B1455403
theorem B4398461 : Blo 507795 4398461 := bstep (se 3 (by rfl) ⟨824711, by rfl⟩ : syracuseStep 4398461 = 1649423) B1649423
theorem B9772609 : Blo 507795 9772609 := bstep (se 2 (by rfl) ⟨3664728, by rfl⟩ : syracuseStep 9772609 = 7329457) B7329457
theorem B859727 : Blo 507795 859727 := bstep (se 1 (by rfl) ⟨644795, by rfl⟩ : syracuseStep 859727 = 1289591) B1289591
theorem B3874391 : Blo 507795 3874391 := bstep (se 1 (by rfl) ⟨2905793, by rfl⟩ : syracuseStep 3874391 = 5811587) B5811587
theorem B1941191 : Blo 507795 1941191 := bstep (se 1 (by rfl) ⟨1455893, by rfl⟩ : syracuseStep 1941191 = 2911787) B2911787
theorem B2170583 : Blo 507795 2170583 := bstep (se 1 (by rfl) ⟨1627937, by rfl⟩ : syracuseStep 2170583 = 3255875) B3255875
theorem B761705 : Blo 507795 761705 := bstep (se 2 (by rfl) ⟨285639, by rfl⟩ : syracuseStep 761705 = 571279) B571279
theorem B761783 : Blo 507795 761783 := bstep (se 1 (by rfl) ⟨571337, by rfl⟩ : syracuseStep 761783 = 1142675) B1142675
theorem B761819 : Blo 507795 761819 := bstep (se 1 (by rfl) ⟨571364, by rfl⟩ : syracuseStep 761819 = 1142729) B1142729
theorem B1286543 : Blo 507795 1286543 := bstep (se 1 (by rfl) ⟨964907, by rfl⟩ : syracuseStep 1286543 = 1929815) B1929815
theorem B762287 : Blo 507795 762287 := bstep (se 1 (by rfl) ⟨571715, by rfl⟩ : syracuseStep 762287 = 1143431) B1143431
theorem B860591 : Blo 507795 860591 := bstep (se 1 (by rfl) ⟨645443, by rfl⟩ : syracuseStep 860591 = 1290887) B1290887
theorem B762377 : Blo 507795 762377 := bstep (se 2 (by rfl) ⟨285891, by rfl⟩ : syracuseStep 762377 = 571783) B571783
theorem B3482135 : Blo 507795 3482135 := bstep (se 1 (by rfl) ⟨2611601, by rfl⟩ : syracuseStep 3482135 = 5223203) B5223203
theorem B8495641 : Blo 507795 8495641 := bstep (se 2 (by rfl) ⟨3185865, by rfl⟩ : syracuseStep 8495641 = 6371731) B6371731
theorem B762407 : Blo 507795 762407 := bstep (se 1 (by rfl) ⟨571805, by rfl⟩ : syracuseStep 762407 = 1143611) B1143611
theorem B762491 : Blo 507795 762491 := bstep (se 1 (by rfl) ⟨571868, by rfl⟩ : syracuseStep 762491 = 1143737) B1143737
theorem B1450619 : Blo 507795 1450619 := bstep (se 1 (by rfl) ⟨1087964, by rfl⟩ : syracuseStep 1450619 = 2175929) B2175929
theorem B1942163 : Blo 507795 1942163 := bstep (se 1 (by rfl) ⟨1456622, by rfl⟩ : syracuseStep 1942163 = 2913245) B2913245
theorem B1286867 : Blo 507795 1286867 := bstep (se 1 (by rfl) ⟨965150, by rfl⟩ : syracuseStep 1286867 = 1930301) B1930301
theorem B762617 : Blo 507795 762617 := bstep (se 2 (by rfl) ⟨285981, by rfl⟩ : syracuseStep 762617 = 571963) B571963
theorem B762719 : Blo 507795 762719 := bstep (se 1 (by rfl) ⟨572039, by rfl⟩ : syracuseStep 762719 = 1144079) B1144079
theorem B1450847 : Blo 507795 1450847 := bstep (se 1 (by rfl) ⟨1088135, by rfl⟩ : syracuseStep 1450847 = 2176271) B2176271
theorem B861023 : Blo 507795 861023 := bstep (se 1 (by rfl) ⟨645767, by rfl⟩ : syracuseStep 861023 = 1291535) B1291535
theorem B762731 : Blo 507795 762731 := bstep (se 1 (by rfl) ⟨572048, by rfl⟩ : syracuseStep 762731 = 1144097) B1144097
theorem B4891499 : Blo 507795 4891499 := bstep (se 1 (by rfl) ⟨3668624, by rfl⟩ : syracuseStep 4891499 = 7337249) B7337249
theorem B1844129 : Blo 507795 1844129 := bstep (se 2 (by rfl) ⟨691548, by rfl⟩ : syracuseStep 1844129 = 1383097) B1383097
theorem B11183123 : Blo 507795 11183123 := bstep (se 1 (by rfl) ⟨8387342, by rfl⟩ : syracuseStep 11183123 = 16774685) B16774685
theorem B1090579 : Blo 507795 1090579 := bstep (se 1 (by rfl) ⟨817934, by rfl⟩ : syracuseStep 1090579 = 1635869) B1635869
theorem B762959 : Blo 507795 762959 := bstep (se 1 (by rfl) ⟨572219, by rfl⟩ : syracuseStep 762959 = 1144439) B1144439
theorem B763079 : Blo 507795 763079 := bstep (se 1 (by rfl) ⟨572309, by rfl⟩ : syracuseStep 763079 = 1144619) B1144619
theorem B763241 : Blo 507795 763241 := bstep (se 2 (by rfl) ⟨286215, by rfl⟩ : syracuseStep 763241 = 572431) B572431
theorem B1090921 : Blo 507795 1090921 := bstep (se 2 (by rfl) ⟨409095, by rfl⟩ : syracuseStep 1090921 = 818191) B818191
theorem B861583 : Blo 507795 861583 := bstep (se 1 (by rfl) ⟨646187, by rfl⟩ : syracuseStep 861583 = 1292375) B1292375
theorem B763319 : Blo 507795 763319 := bstep (se 1 (by rfl) ⟨572489, by rfl⟩ : syracuseStep 763319 = 1144979) B1144979
theorem B763355 : Blo 507795 763355 := bstep (se 1 (by rfl) ⟨572516, by rfl⟩ : syracuseStep 763355 = 1145033) B1145033
theorem B763823 : Blo 507795 763823 := bstep (se 1 (by rfl) ⟨572867, by rfl⟩ : syracuseStep 763823 = 1145735) B1145735
theorem B5810129 : Blo 507795 5810129 := bstep (se 2 (by rfl) ⟨2178798, by rfl⟩ : syracuseStep 5810129 = 4357597) B4357597
theorem B763913 : Blo 507795 763913 := bstep (se 2 (by rfl) ⟨286467, by rfl⟩ : syracuseStep 763913 = 572935) B572935
theorem B763943 : Blo 507795 763943 := bstep (se 1 (by rfl) ⟨572957, by rfl⟩ : syracuseStep 763943 = 1145915) B1145915
theorem B862265 : Blo 507795 862265 := bstep (se 2 (by rfl) ⟨323349, by rfl⟩ : syracuseStep 862265 = 646699) B646699
theorem B764027 : Blo 507795 764027 := bstep (se 1 (by rfl) ⟨573020, by rfl⟩ : syracuseStep 764027 = 1146041) B1146041
theorem B4139171 : Blo 507795 4139171 := bstep (se 1 (by rfl) ⟨3104378, by rfl⟩ : syracuseStep 4139171 = 6208757) B6208757
theorem B764153 : Blo 507795 764153 := bstep (se 2 (by rfl) ⟨286557, by rfl⟩ : syracuseStep 764153 = 573115) B573115
theorem B6203699 : Blo 507795 6203699 := bstep (se 1 (by rfl) ⟨4652774, by rfl⟩ : syracuseStep 6203699 = 9305549) B9305549
theorem B764255 : Blo 507795 764255 := bstep (se 1 (by rfl) ⟨573191, by rfl⟩ : syracuseStep 764255 = 1146383) B1146383
theorem B764267 : Blo 507795 764267 := bstep (se 1 (by rfl) ⟨573200, by rfl⟩ : syracuseStep 764267 = 1146401) B1146401
theorem B1452431 : Blo 507795 1452431 := bstep (se 1 (by rfl) ⟨1089323, by rfl⟩ : syracuseStep 1452431 = 2178647) B2178647
theorem B32156189 : Blo 507795 32156189 := bstep (se 3 (by rfl) ⟨6029285, by rfl⟩ : syracuseStep 32156189 = 12058571) B12058571
theorem B764495 : Blo 507795 764495 := bstep (se 1 (by rfl) ⟨573371, by rfl⟩ : syracuseStep 764495 = 1146743) B1146743
theorem B1714823 : Blo 507795 1714823 := bstep (se 1 (by rfl) ⟨1286117, by rfl⟩ : syracuseStep 1714823 = 2572235) B2572235
theorem B1714877 : Blo 507795 1714877 := bstep (se 3 (by rfl) ⟨321539, by rfl⟩ : syracuseStep 1714877 = 643079) B643079
theorem B764615 : Blo 507795 764615 := bstep (se 1 (by rfl) ⟨573461, by rfl⟩ : syracuseStep 764615 = 1146923) B1146923
theorem B862967 : Blo 507795 862967 := bstep (se 1 (by rfl) ⟨647225, by rfl⟩ : syracuseStep 862967 = 1294451) B1294451
theorem B1715039 : Blo 507795 1715039 := bstep (se 1 (by rfl) ⟨1286279, by rfl⟩ : syracuseStep 1715039 = 2572559) B2572559
theorem B764777 : Blo 507795 764777 := bstep (se 2 (by rfl) ⟨286791, by rfl⟩ : syracuseStep 764777 = 573583) B573583
theorem B1289135 : Blo 507795 1289135 := bstep (se 1 (by rfl) ⟨966851, by rfl⟩ : syracuseStep 1289135 = 1933703) B1933703
theorem B15641527 : Blo 507795 15641527 := bstep (se 1 (by rfl) ⟨11731145, by rfl⟩ : syracuseStep 15641527 = 23462291) B23462291
theorem B764855 : Blo 507795 764855 := bstep (se 1 (by rfl) ⟨573641, by rfl⟩ : syracuseStep 764855 = 1147283) B1147283
theorem B764891 : Blo 507795 764891 := bstep (se 1 (by rfl) ⟨573668, by rfl⟩ : syracuseStep 764891 = 1147337) B1147337
theorem B1715201 : Blo 507795 1715201 := bstep (se 2 (by rfl) ⟨643200, by rfl⟩ : syracuseStep 1715201 = 1286401) B1286401
theorem B863311 : Blo 507795 863311 := bstep (se 1 (by rfl) ⟨647483, by rfl⟩ : syracuseStep 863311 = 1294967) B1294967
theorem B863561 : Blo 507795 863561 := bstep (se 2 (by rfl) ⟨323835, by rfl⟩ : syracuseStep 863561 = 647671) B647671
theorem B765359 : Blo 507795 765359 := bstep (se 1 (by rfl) ⟨574019, by rfl⟩ : syracuseStep 765359 = 1148039) B1148039
theorem B765449 : Blo 507795 765449 := bstep (se 2 (by rfl) ⟨287043, by rfl⟩ : syracuseStep 765449 = 574087) B574087
theorem B1289753 : Blo 507795 1289753 := bstep (se 2 (by rfl) ⟨483657, by rfl⟩ : syracuseStep 1289753 = 967315) B967315
theorem B765479 : Blo 507795 765479 := bstep (se 1 (by rfl) ⟨574109, by rfl⟩ : syracuseStep 765479 = 1148219) B1148219
theorem B765563 : Blo 507795 765563 := bstep (se 1 (by rfl) ⟨574172, by rfl⟩ : syracuseStep 765563 = 1148345) B1148345
theorem B765689 : Blo 507795 765689 := bstep (se 2 (by rfl) ⟨287133, by rfl⟩ : syracuseStep 765689 = 574267) B574267
theorem B1716011 : Blo 507795 1716011 := bstep (se 1 (by rfl) ⟨1287008, by rfl⟩ : syracuseStep 1716011 = 2574017) B2574017
theorem B765791 : Blo 507795 765791 := bstep (se 1 (by rfl) ⟨574343, by rfl⟩ : syracuseStep 765791 = 1148687) B1148687
theorem B765803 : Blo 507795 765803 := bstep (se 1 (by rfl) ⟨574352, by rfl⟩ : syracuseStep 765803 = 1148705) B1148705
theorem B3878765 : Blo 507795 3878765 := bstep (se 3 (by rfl) ⟨727268, by rfl⟩ : syracuseStep 3878765 = 1454537) B1454537
theorem B3092411 : Blo 507795 3092411 := bstep (se 1 (by rfl) ⟨2319308, by rfl⟩ : syracuseStep 3092411 = 4638617) B4638617
theorem B1716281 : Blo 507795 1716281 := bstep (se 2 (by rfl) ⟨643605, by rfl⟩ : syracuseStep 1716281 = 1287211) B1287211
theorem B766031 : Blo 507795 766031 := bstep (se 1 (by rfl) ⟨574523, by rfl⟩ : syracuseStep 766031 = 1149047) B1149047
theorem B1224875 : Blo 507795 1224875 := bstep (se 1 (by rfl) ⟨918656, by rfl⟩ : syracuseStep 1224875 = 1837313) B1837313
theorem B766151 : Blo 507795 766151 := bstep (se 1 (by rfl) ⟨574613, by rfl⟩ : syracuseStep 766151 = 1149227) B1149227
theorem B4141313 : Blo 507795 4141313 := bstep (se 2 (by rfl) ⟨1552992, by rfl⟩ : syracuseStep 4141313 = 3105985) B3105985
theorem B766313 : Blo 507795 766313 := bstep (se 2 (by rfl) ⟨287367, by rfl⟩ : syracuseStep 766313 = 574735) B574735
theorem B1716605 : Blo 507795 1716605 := bstep (se 3 (by rfl) ⟨321863, by rfl⟩ : syracuseStep 1716605 = 643727) B643727
theorem B766391 : Blo 507795 766391 := bstep (se 1 (by rfl) ⟨574793, by rfl⟩ : syracuseStep 766391 = 1149587) B1149587
theorem B766427 : Blo 507795 766427 := bstep (se 1 (by rfl) ⟨574820, by rfl⟩ : syracuseStep 766427 = 1149641) B1149641
theorem B1716875 : Blo 507795 1716875 := bstep (se 1 (by rfl) ⟨1287656, by rfl⟩ : syracuseStep 1716875 = 2575313) B2575313
theorem B766895 : Blo 507795 766895 := bstep (se 1 (by rfl) ⟨575171, by rfl⟩ : syracuseStep 766895 = 1150343) B1150343
theorem B766985 : Blo 507795 766985 := bstep (se 2 (by rfl) ⟨287619, by rfl⟩ : syracuseStep 766985 = 575239) B575239
theorem B767015 : Blo 507795 767015 := bstep (se 1 (by rfl) ⟨575261, by rfl⟩ : syracuseStep 767015 = 1150523) B1150523
theorem B767099 : Blo 507795 767099 := bstep (se 1 (by rfl) ⟨575324, by rfl⟩ : syracuseStep 767099 = 1150649) B1150649
theorem B767225 : Blo 507795 767225 := bstep (se 2 (by rfl) ⟨287709, by rfl⟩ : syracuseStep 767225 = 575419) B575419
theorem B767327 : Blo 507795 767327 := bstep (se 1 (by rfl) ⟨575495, by rfl⟩ : syracuseStep 767327 = 1150991) B1150991
theorem B767339 : Blo 507795 767339 := bstep (se 1 (by rfl) ⟨575504, by rfl⟩ : syracuseStep 767339 = 1151009) B1151009
theorem B1717793 : Blo 507795 1717793 := bstep (se 2 (by rfl) ⟨644172, by rfl⟩ : syracuseStep 1717793 = 1288345) B1288345
theorem B767567 : Blo 507795 767567 := bstep (se 1 (by rfl) ⟨575675, by rfl⟩ : syracuseStep 767567 = 1151351) B1151351
theorem B767687 : Blo 507795 767687 := bstep (se 1 (by rfl) ⟨575765, by rfl⟩ : syracuseStep 767687 = 1151531) B1151531
theorem B1718009 : Blo 507795 1718009 := bstep (se 2 (by rfl) ⟨644253, by rfl⟩ : syracuseStep 1718009 = 1288507) B1288507
theorem B2176955 : Blo 507795 2176955 := bstep (se 1 (by rfl) ⟨1632716, by rfl⟩ : syracuseStep 2176955 = 3265433) B3265433
theorem B1718279 : Blo 507795 1718279 := bstep (se 1 (by rfl) ⟨1288709, by rfl⟩ : syracuseStep 1718279 = 2577419) B2577419
theorem B2897957 : Blo 507795 2897957 := bstep (se 4 (by rfl) ⟨271683, by rfl⟩ : syracuseStep 2897957 = 543367) B543367
theorem B1292345 : Blo 507795 1292345 := bstep (se 2 (by rfl) ⟨484629, by rfl⟩ : syracuseStep 1292345 = 969259) B969259
theorem B1718387 : Blo 507795 1718387 := bstep (se 1 (by rfl) ⟨1288790, by rfl⟩ : syracuseStep 1718387 = 2577581) B2577581
theorem B1718657 : Blo 507795 1718657 := bstep (se 2 (by rfl) ⟨644496, by rfl⟩ : syracuseStep 1718657 = 1288993) B1288993
theorem B1554817 : Blo 507795 1554817 := bstep (se 2 (by rfl) ⟨583056, by rfl⟩ : syracuseStep 1554817 = 1166113) B1166113
theorem B4340101 : Blo 507795 4340101 := bstep (se 4 (by rfl) ⟨406884, by rfl⟩ : syracuseStep 4340101 = 813769) B813769
theorem B13056389 : Blo 507795 13056389 := bstep (se 4 (by rfl) ⟨1224036, by rfl⟩ : syracuseStep 13056389 = 2448073) B2448073
theorem B2898413 : Blo 507795 2898413 := bstep (se 3 (by rfl) ⟨543452, by rfl⟩ : syracuseStep 2898413 = 1086905) B1086905
theorem B2570777 : Blo 507795 2570777 := bstep (se 2 (by rfl) ⟨964041, by rfl⟩ : syracuseStep 2570777 = 1928083) B1928083
theorem B1456679 : Blo 507795 1456679 := bstep (se 1 (by rfl) ⟨1092509, by rfl⟩ : syracuseStep 1456679 = 2185019) B2185019
theorem B3881681 : Blo 507795 3881681 := bstep (se 2 (by rfl) ⟨1455630, by rfl⟩ : syracuseStep 3881681 = 2911261) B2911261
theorem B1653577 : Blo 507795 1653577 := bstep (se 2 (by rfl) ⟨620091, by rfl⟩ : syracuseStep 1653577 = 1240183) B1240183
theorem B1162171 : Blo 507795 1162171 := bstep (se 1 (by rfl) ⟨871628, by rfl⟩ : syracuseStep 1162171 = 1743257) B1743257
theorem B1031177 : Blo 507795 1031177 := bstep (se 2 (by rfl) ⟨386691, by rfl⟩ : syracuseStep 1031177 = 773383) B773383
theorem B572539 : Blo 507795 572539 := bstep (se 1 (by rfl) ⟨429404, by rfl⟩ : syracuseStep 572539 = 858809) B858809
theorem B2899097 : Blo 507795 2899097 := bstep (se 2 (by rfl) ⟨1087161, by rfl⟩ : syracuseStep 2899097 = 2174323) B2174323
theorem B1719467 : Blo 507795 1719467 := bstep (se 1 (by rfl) ⟨1289600, by rfl⟩ : syracuseStep 1719467 = 2579201) B2579201
theorem B3489139 : Blo 507795 3489139 := bstep (se 1 (by rfl) ⟨2616854, by rfl⟩ : syracuseStep 3489139 = 5233709) B5233709
theorem B966107 : Blo 507795 966107 := bstep (se 1 (by rfl) ⟨724580, by rfl⟩ : syracuseStep 966107 = 1449161) B1449161
theorem B1883657 : Blo 507795 1883657 := bstep (se 2 (by rfl) ⟨706371, by rfl⟩ : syracuseStep 1883657 = 1412743) B1412743
theorem B1293833 : Blo 507795 1293833 := bstep (se 2 (by rfl) ⟨485187, by rfl⟩ : syracuseStep 1293833 = 970375) B970375
theorem B573007 : Blo 507795 573007 := bstep (se 1 (by rfl) ⟨429755, by rfl⟩ : syracuseStep 573007 = 859511) B859511
theorem B1162849 : Blo 507795 1162849 := bstep (se 2 (by rfl) ⟨436068, by rfl⟩ : syracuseStep 1162849 = 872137) B872137
theorem B27836045 : Blo 507795 27836045 := bstep (se 3 (by rfl) ⟨5219258, by rfl⟩ : syracuseStep 27836045 = 10438517) B10438517
theorem B4341437 : Blo 507795 4341437 := bstep (se 3 (by rfl) ⟨814019, by rfl⟩ : syracuseStep 4341437 = 1628039) B1628039
theorem B966343 : Blo 507795 966343 := bstep (se 1 (by rfl) ⟨724757, by rfl⟩ : syracuseStep 966343 = 1449515) B1449515
theorem B1720007 : Blo 507795 1720007 := bstep (se 1 (by rfl) ⟨1290005, by rfl⟩ : syracuseStep 1720007 = 2580011) B2580011
theorem B2440925 : Blo 507795 2440925 := bstep (se 3 (by rfl) ⟨457673, by rfl⟩ : syracuseStep 2440925 = 915347) B915347
theorem B507823 : Blo 507795 507823 := bstep (se 1 (by rfl) ⟨380867, by rfl⟩ : syracuseStep 507823 = 761735) B761735
theorem B1228727 : Blo 507795 1228727 := bstep (se 1 (by rfl) ⟨921545, by rfl⟩ : syracuseStep 1228727 = 1843091) B1843091
theorem B507847 : Blo 507795 507847 := bstep (se 1 (by rfl) ⟨380885, by rfl⟩ : syracuseStep 507847 = 761771) B761771
theorem B507867 : Blo 507795 507867 := bstep (se 1 (by rfl) ⟨380900, by rfl⟩ : syracuseStep 507867 = 761801) B761801
theorem B573403 : Blo 507795 573403 := bstep (se 1 (by rfl) ⟨430052, by rfl⟩ : syracuseStep 573403 = 860105) B860105
theorem B507943 : Blo 507795 507943 := bstep (se 1 (by rfl) ⟨380957, by rfl⟩ : syracuseStep 507943 = 761915) B761915
theorem B507983 : Blo 507795 507983 := bstep (se 1 (by rfl) ⟨380987, by rfl⟩ : syracuseStep 507983 = 761975) B761975
theorem B2801753 : Blo 507795 2801753 := bstep (se 2 (by rfl) ⟨1050657, by rfl⟩ : syracuseStep 2801753 = 2101315) B2101315
theorem B507999 : Blo 507795 507999 := bstep (se 1 (by rfl) ⟨380999, by rfl⟩ : syracuseStep 507999 = 761999) B761999
theorem B508027 : Blo 507795 508027 := bstep (se 1 (by rfl) ⟨381020, by rfl⟩ : syracuseStep 508027 = 762041) B762041
theorem B508079 : Blo 507795 508079 := bstep (se 1 (by rfl) ⟨381059, by rfl⟩ : syracuseStep 508079 = 762119) B762119
theorem B508103 : Blo 507795 508103 := bstep (se 1 (by rfl) ⟨381077, by rfl⟩ : syracuseStep 508103 = 762155) B762155
theorem B508123 : Blo 507795 508123 := bstep (se 1 (by rfl) ⟨381092, by rfl⟩ : syracuseStep 508123 = 762185) B762185
theorem B508199 : Blo 507795 508199 := bstep (se 1 (by rfl) ⟨381149, by rfl⟩ : syracuseStep 508199 = 762299) B762299
theorem B508239 : Blo 507795 508239 := bstep (se 1 (by rfl) ⟨381179, by rfl⟩ : syracuseStep 508239 = 762359) B762359
theorem B508255 : Blo 507795 508255 := bstep (se 1 (by rfl) ⟨381191, by rfl⟩ : syracuseStep 508255 = 762383) B762383
theorem B508283 : Blo 507795 508283 := bstep (se 1 (by rfl) ⟨381212, by rfl⟩ : syracuseStep 508283 = 762425) B762425
theorem B508335 : Blo 507795 508335 := bstep (se 1 (by rfl) ⟨381251, by rfl⟩ : syracuseStep 508335 = 762503) B762503
theorem B573871 : Blo 507795 573871 := bstep (se 1 (by rfl) ⟨430403, by rfl⟩ : syracuseStep 573871 = 860807) B860807
theorem B508359 : Blo 507795 508359 := bstep (se 1 (by rfl) ⟨381269, by rfl⟩ : syracuseStep 508359 = 762539) B762539
theorem B508379 : Blo 507795 508379 := bstep (se 1 (by rfl) ⟨381284, by rfl⟩ : syracuseStep 508379 = 762569) B762569
theorem B967187 : Blo 507795 967187 := bstep (se 1 (by rfl) ⟨725390, by rfl⟩ : syracuseStep 967187 = 1450781) B1450781
theorem B508455 : Blo 507795 508455 := bstep (se 1 (by rfl) ⟨381341, by rfl⟩ : syracuseStep 508455 = 762683) B762683
theorem B1720871 : Blo 507795 1720871 := bstep (se 1 (by rfl) ⟨1290653, by rfl⟩ : syracuseStep 1720871 = 2581307) B2581307
theorem B508495 : Blo 507795 508495 := bstep (se 1 (by rfl) ⟨381371, by rfl⟩ : syracuseStep 508495 = 762743) B762743
theorem B508511 : Blo 507795 508511 := bstep (se 1 (by rfl) ⟨381383, by rfl⟩ : syracuseStep 508511 = 762767) B762767
theorem B508539 : Blo 507795 508539 := bstep (se 1 (by rfl) ⟨381404, by rfl⟩ : syracuseStep 508539 = 762809) B762809
theorem B1294987 : Blo 507795 1294987 := bstep (se 1 (by rfl) ⟨971240, by rfl⟩ : syracuseStep 1294987 = 1942481) B1942481
theorem B1720979 : Blo 507795 1720979 := bstep (se 1 (by rfl) ⟨1290734, by rfl⟩ : syracuseStep 1720979 = 2581469) B2581469
theorem B508591 : Blo 507795 508591 := bstep (se 1 (by rfl) ⟨381443, by rfl⟩ : syracuseStep 508591 = 762887) B762887
theorem B508615 : Blo 507795 508615 := bstep (se 1 (by rfl) ⟨381461, by rfl⟩ : syracuseStep 508615 = 762923) B762923
theorem B508635 : Blo 507795 508635 := bstep (se 1 (by rfl) ⟨381476, by rfl⟩ : syracuseStep 508635 = 762953) B762953
theorem B508711 : Blo 507795 508711 := bstep (se 1 (by rfl) ⟨381533, by rfl⟩ : syracuseStep 508711 = 763067) B763067
theorem B508751 : Blo 507795 508751 := bstep (se 1 (by rfl) ⟨381563, by rfl⟩ : syracuseStep 508751 = 763127) B763127
theorem B508767 : Blo 507795 508767 := bstep (se 1 (by rfl) ⟨381575, by rfl⟩ : syracuseStep 508767 = 763151) B763151
theorem B574303 : Blo 507795 574303 := bstep (se 1 (by rfl) ⟨430727, by rfl⟩ : syracuseStep 574303 = 861455) B861455
theorem B1721195 : Blo 507795 1721195 := bstep (se 1 (by rfl) ⟨1290896, by rfl⟩ : syracuseStep 1721195 = 2581793) B2581793
theorem B508795 : Blo 507795 508795 := bstep (se 1 (by rfl) ⟨381596, by rfl⟩ : syracuseStep 508795 = 763193) B763193
theorem B1721249 : Blo 507795 1721249 := bstep (se 2 (by rfl) ⟨645468, by rfl⟩ : syracuseStep 1721249 = 1290937) B1290937
theorem B508847 : Blo 507795 508847 := bstep (se 1 (by rfl) ⟨381635, by rfl⟩ : syracuseStep 508847 = 763271) B763271
theorem B1295291 : Blo 507795 1295291 := bstep (se 1 (by rfl) ⟨971468, by rfl⟩ : syracuseStep 1295291 = 1942937) B1942937
theorem B508871 : Blo 507795 508871 := bstep (se 1 (by rfl) ⟨381653, by rfl⟩ : syracuseStep 508871 = 763307) B763307
theorem B508891 : Blo 507795 508891 := bstep (se 1 (by rfl) ⟨381668, by rfl⟩ : syracuseStep 508891 = 763337) B763337
theorem B508967 : Blo 507795 508967 := bstep (se 1 (by rfl) ⟨381725, by rfl⟩ : syracuseStep 508967 = 763451) B763451
theorem B4342835 : Blo 507795 4342835 := bstep (se 1 (by rfl) ⟨3257126, by rfl⟩ : syracuseStep 4342835 = 6514253) B6514253
theorem B509007 : Blo 507795 509007 := bstep (se 1 (by rfl) ⟨381755, by rfl⟩ : syracuseStep 509007 = 763511) B763511
theorem B3884111 : Blo 507795 3884111 := bstep (se 1 (by rfl) ⟨2913083, by rfl⟩ : syracuseStep 3884111 = 5826167) B5826167
theorem B509023 : Blo 507795 509023 := bstep (se 1 (by rfl) ⟨381767, by rfl⟩ : syracuseStep 509023 = 763535) B763535
theorem B509051 : Blo 507795 509051 := bstep (se 1 (by rfl) ⟨381788, by rfl⟩ : syracuseStep 509051 = 763577) B763577
theorem B509103 : Blo 507795 509103 := bstep (se 1 (by rfl) ⟨381827, by rfl⟩ : syracuseStep 509103 = 763655) B763655
theorem B509127 : Blo 507795 509127 := bstep (se 1 (by rfl) ⟨381845, by rfl⟩ : syracuseStep 509127 = 763691) B763691
theorem B574663 : Blo 507795 574663 := bstep (se 1 (by rfl) ⟨430997, by rfl⟩ : syracuseStep 574663 = 861995) B861995
theorem B509147 : Blo 507795 509147 := bstep (se 1 (by rfl) ⟨381860, by rfl⟩ : syracuseStep 509147 = 763721) B763721
theorem B509223 : Blo 507795 509223 := bstep (se 1 (by rfl) ⟨381917, by rfl⟩ : syracuseStep 509223 = 763835) B763835
theorem B509263 : Blo 507795 509263 := bstep (se 1 (by rfl) ⟨381947, by rfl⟩ : syracuseStep 509263 = 763895) B763895
theorem B509279 : Blo 507795 509279 := bstep (se 1 (by rfl) ⟨381959, by rfl⟩ : syracuseStep 509279 = 763919) B763919
theorem B509307 : Blo 507795 509307 := bstep (se 1 (by rfl) ⟨381980, by rfl⟩ : syracuseStep 509307 = 763961) B763961
theorem B2573693 : Blo 507795 2573693 := bstep (se 3 (by rfl) ⟨482567, by rfl⟩ : syracuseStep 2573693 = 965135) B965135
theorem B509359 : Blo 507795 509359 := bstep (se 1 (by rfl) ⟨382019, by rfl⟩ : syracuseStep 509359 = 764039) B764039
theorem B509383 : Blo 507795 509383 := bstep (se 1 (by rfl) ⟨382037, by rfl⟩ : syracuseStep 509383 = 764075) B764075
theorem B509403 : Blo 507795 509403 := bstep (se 1 (by rfl) ⟨382052, by rfl⟩ : syracuseStep 509403 = 764105) B764105
theorem B1721843 : Blo 507795 1721843 := bstep (se 1 (by rfl) ⟨1291382, by rfl⟩ : syracuseStep 1721843 = 2582765) B2582765
theorem B509479 : Blo 507795 509479 := bstep (se 1 (by rfl) ⟨382109, by rfl⟩ : syracuseStep 509479 = 764219) B764219
theorem B968249 : Blo 507795 968249 := bstep (se 2 (by rfl) ⟨363093, by rfl⟩ : syracuseStep 968249 = 726187) B726187
theorem B509519 : Blo 507795 509519 := bstep (se 1 (by rfl) ⟨382139, by rfl⟩ : syracuseStep 509519 = 764279) B764279
theorem B509535 : Blo 507795 509535 := bstep (se 1 (by rfl) ⟨382151, by rfl⟩ : syracuseStep 509535 = 764303) B764303
theorem B509563 : Blo 507795 509563 := bstep (se 1 (by rfl) ⟨382172, by rfl⟩ : syracuseStep 509563 = 764345) B764345
theorem B509615 : Blo 507795 509615 := bstep (se 1 (by rfl) ⟨382211, by rfl⟩ : syracuseStep 509615 = 764423) B764423
theorem B509639 : Blo 507795 509639 := bstep (se 1 (by rfl) ⟨382229, by rfl⟩ : syracuseStep 509639 = 764459) B764459
theorem B509659 : Blo 507795 509659 := bstep (se 1 (by rfl) ⟨382244, by rfl⟩ : syracuseStep 509659 = 764489) B764489
theorem B509735 : Blo 507795 509735 := bstep (se 1 (by rfl) ⟨382301, by rfl⟩ : syracuseStep 509735 = 764603) B764603
theorem B509775 : Blo 507795 509775 := bstep (se 1 (by rfl) ⟨382331, by rfl⟩ : syracuseStep 509775 = 764663) B764663
theorem B509791 : Blo 507795 509791 := bstep (se 1 (by rfl) ⟨382343, by rfl⟩ : syracuseStep 509791 = 764687) B764687
theorem B509819 : Blo 507795 509819 := bstep (se 1 (by rfl) ⟨382364, by rfl⟩ : syracuseStep 509819 = 764729) B764729
theorem B968591 : Blo 507795 968591 := bstep (se 1 (by rfl) ⟨726443, by rfl⟩ : syracuseStep 968591 = 1452887) B1452887
theorem B509871 : Blo 507795 509871 := bstep (se 1 (by rfl) ⟨382403, by rfl⟩ : syracuseStep 509871 = 764807) B764807
theorem B509895 : Blo 507795 509895 := bstep (se 1 (by rfl) ⟨382421, by rfl⟩ : syracuseStep 509895 = 764843) B764843
theorem B509915 : Blo 507795 509915 := bstep (se 1 (by rfl) ⟨382436, by rfl⟩ : syracuseStep 509915 = 764873) B764873
theorem B1722383 : Blo 507795 1722383 := bstep (se 1 (by rfl) ⟨1291787, by rfl⟩ : syracuseStep 1722383 = 2583575) B2583575
theorem B509991 : Blo 507795 509991 := bstep (se 1 (by rfl) ⟨382493, by rfl⟩ : syracuseStep 509991 = 764987) B764987
theorem B575527 : Blo 507795 575527 := bstep (se 1 (by rfl) ⟨431645, by rfl⟩ : syracuseStep 575527 = 863291) B863291
theorem B510031 : Blo 507795 510031 := bstep (se 1 (by rfl) ⟨382523, by rfl⟩ : syracuseStep 510031 = 765047) B765047
theorem B510047 : Blo 507795 510047 := bstep (se 1 (by rfl) ⟨382535, by rfl⟩ : syracuseStep 510047 = 765071) B765071
theorem B510075 : Blo 507795 510075 := bstep (se 1 (by rfl) ⟨382556, by rfl⟩ : syracuseStep 510075 = 765113) B765113
theorem B510127 : Blo 507795 510127 := bstep (se 1 (by rfl) ⟨382595, by rfl⟩ : syracuseStep 510127 = 765191) B765191
theorem B510151 : Blo 507795 510151 := bstep (se 1 (by rfl) ⟨382613, by rfl⟩ : syracuseStep 510151 = 765227) B765227
theorem B510171 : Blo 507795 510171 := bstep (se 1 (by rfl) ⟨382628, by rfl⟩ : syracuseStep 510171 = 765257) B765257
theorem B510247 : Blo 507795 510247 := bstep (se 1 (by rfl) ⟨382685, by rfl⟩ : syracuseStep 510247 = 765371) B765371
theorem B510287 : Blo 507795 510287 := bstep (se 1 (by rfl) ⟨382715, by rfl⟩ : syracuseStep 510287 = 765431) B765431
theorem B510303 : Blo 507795 510303 := bstep (se 1 (by rfl) ⟨382727, by rfl⟩ : syracuseStep 510303 = 765455) B765455
theorem B510331 : Blo 507795 510331 := bstep (se 1 (by rfl) ⟨382748, by rfl⟩ : syracuseStep 510331 = 765497) B765497
theorem B510383 : Blo 507795 510383 := bstep (se 1 (by rfl) ⟨382787, by rfl⟩ : syracuseStep 510383 = 765575) B765575
theorem B510407 : Blo 507795 510407 := bstep (se 1 (by rfl) ⟨382805, by rfl⟩ : syracuseStep 510407 = 765611) B765611
theorem B510427 : Blo 507795 510427 := bstep (se 1 (by rfl) ⟨382820, by rfl⟩ : syracuseStep 510427 = 765641) B765641
theorem B510503 : Blo 507795 510503 := bstep (se 1 (by rfl) ⟨382877, by rfl⟩ : syracuseStep 510503 = 765755) B765755
theorem B510543 : Blo 507795 510543 := bstep (se 1 (by rfl) ⟨382907, by rfl⟩ : syracuseStep 510543 = 765815) B765815
theorem B510559 : Blo 507795 510559 := bstep (se 1 (by rfl) ⟨382919, by rfl⟩ : syracuseStep 510559 = 765839) B765839
theorem B1722977 : Blo 507795 1722977 := bstep (se 2 (by rfl) ⟨646116, by rfl⟩ : syracuseStep 1722977 = 1292233) B1292233
theorem B510587 : Blo 507795 510587 := bstep (se 1 (by rfl) ⟨382940, by rfl⟩ : syracuseStep 510587 = 765881) B765881
theorem B510639 : Blo 507795 510639 := bstep (se 1 (by rfl) ⟨382979, by rfl⟩ : syracuseStep 510639 = 765959) B765959
theorem B510663 : Blo 507795 510663 := bstep (se 1 (by rfl) ⟨382997, by rfl⟩ : syracuseStep 510663 = 765995) B765995
theorem B510683 : Blo 507795 510683 := bstep (se 1 (by rfl) ⟨383012, by rfl⟩ : syracuseStep 510683 = 766025) B766025
theorem B2902787 : Blo 507795 2902787 := bstep (se 1 (by rfl) ⟨2177090, by rfl⟩ : syracuseStep 2902787 = 4354181) B4354181
theorem B510759 : Blo 507795 510759 := bstep (se 1 (by rfl) ⟨383069, by rfl⟩ : syracuseStep 510759 = 766139) B766139
theorem B510799 : Blo 507795 510799 := bstep (se 1 (by rfl) ⟨383099, by rfl⟩ : syracuseStep 510799 = 766199) B766199
theorem B510815 : Blo 507795 510815 := bstep (se 1 (by rfl) ⟨383111, by rfl⟩ : syracuseStep 510815 = 766223) B766223
theorem B510843 : Blo 507795 510843 := bstep (se 1 (by rfl) ⟨383132, by rfl⟩ : syracuseStep 510843 = 766265) B766265
theorem B510895 : Blo 507795 510895 := bstep (se 1 (by rfl) ⟨383171, by rfl⟩ : syracuseStep 510895 = 766343) B766343
theorem B510919 : Blo 507795 510919 := bstep (se 1 (by rfl) ⟨383189, by rfl⟩ : syracuseStep 510919 = 766379) B766379
theorem B510939 : Blo 507795 510939 := bstep (se 1 (by rfl) ⟨383204, by rfl⟩ : syracuseStep 510939 = 766409) B766409
theorem B511015 : Blo 507795 511015 := bstep (se 1 (by rfl) ⟨383261, by rfl⟩ : syracuseStep 511015 = 766523) B766523
theorem B511055 : Blo 507795 511055 := bstep (se 1 (by rfl) ⟨383291, by rfl⟩ : syracuseStep 511055 = 766583) B766583
theorem B511071 : Blo 507795 511071 := bstep (se 1 (by rfl) ⟨383303, by rfl⟩ : syracuseStep 511071 = 766607) B766607
theorem B511099 : Blo 507795 511099 := bstep (se 1 (by rfl) ⟨383324, by rfl⟩ : syracuseStep 511099 = 766649) B766649
theorem B511151 : Blo 507795 511151 := bstep (se 1 (by rfl) ⟨383363, by rfl⟩ : syracuseStep 511151 = 766727) B766727
theorem B5491907 : Blo 507795 5491907 := bstep (se 1 (by rfl) ⟨4118930, by rfl⟩ : syracuseStep 5491907 = 8237861) B8237861
theorem B511175 : Blo 507795 511175 := bstep (se 1 (by rfl) ⟨383381, by rfl⟩ : syracuseStep 511175 = 766763) B766763
theorem B511195 : Blo 507795 511195 := bstep (se 1 (by rfl) ⟨383396, by rfl⟩ : syracuseStep 511195 = 766793) B766793
theorem B511271 : Blo 507795 511271 := bstep (se 1 (by rfl) ⟨383453, by rfl⟩ : syracuseStep 511271 = 766907) B766907
theorem B511311 : Blo 507795 511311 := bstep (se 1 (by rfl) ⟨383483, by rfl⟩ : syracuseStep 511311 = 766967) B766967
theorem B511327 : Blo 507795 511327 := bstep (se 1 (by rfl) ⟨383495, by rfl⟩ : syracuseStep 511327 = 766991) B766991
theorem B511355 : Blo 507795 511355 := bstep (se 1 (by rfl) ⟨383516, by rfl⟩ : syracuseStep 511355 = 767033) B767033
theorem B511407 : Blo 507795 511407 := bstep (se 1 (by rfl) ⟨383555, by rfl⟩ : syracuseStep 511407 = 767111) B767111
theorem B511431 : Blo 507795 511431 := bstep (se 1 (by rfl) ⟨383573, by rfl⟩ : syracuseStep 511431 = 767147) B767147
theorem B511451 : Blo 507795 511451 := bstep (se 1 (by rfl) ⟨383588, by rfl⟩ : syracuseStep 511451 = 767177) B767177
theorem B511527 : Blo 507795 511527 := bstep (se 1 (by rfl) ⟨383645, by rfl⟩ : syracuseStep 511527 = 767291) B767291
theorem B511567 : Blo 507795 511567 := bstep (se 1 (by rfl) ⟨383675, by rfl⟩ : syracuseStep 511567 = 767351) B767351
theorem B511583 : Blo 507795 511583 := bstep (se 1 (by rfl) ⟨383687, by rfl⟩ : syracuseStep 511583 = 767375) B767375
theorem B511611 : Blo 507795 511611 := bstep (se 1 (by rfl) ⟨383708, by rfl⟩ : syracuseStep 511611 = 767417) B767417
theorem B511663 : Blo 507795 511663 := bstep (se 1 (by rfl) ⟨383747, by rfl⟩ : syracuseStep 511663 = 767495) B767495
theorem B511687 : Blo 507795 511687 := bstep (se 1 (by rfl) ⟨383765, by rfl⟩ : syracuseStep 511687 = 767531) B767531
theorem B970451 : Blo 507795 970451 := bstep (se 1 (by rfl) ⟨727838, by rfl⟩ : syracuseStep 970451 = 1455677) B1455677
theorem B511707 : Blo 507795 511707 := bstep (se 1 (by rfl) ⟨383780, by rfl⟩ : syracuseStep 511707 = 767561) B767561
theorem B511783 : Blo 507795 511783 := bstep (se 1 (by rfl) ⟨383837, by rfl⟩ : syracuseStep 511783 = 767675) B767675
theorem B2183021 : Blo 507795 2183021 := bstep (se 3 (by rfl) ⟨409316, by rfl⟩ : syracuseStep 2183021 = 818633) B818633
theorem B3100535 : Blo 507795 3100535 := bstep (se 1 (by rfl) ⟨2325401, by rfl⟩ : syracuseStep 3100535 = 4650803) B4650803
theorem B2936737 : Blo 507795 2936737 := bstep (se 2 (by rfl) ⟨1101276, by rfl⟩ : syracuseStep 2936737 = 2202553) B2202553
theorem B970679 : Blo 507795 970679 := bstep (se 1 (by rfl) ⟨728009, by rfl⟩ : syracuseStep 970679 = 1456019) B1456019
theorem B4182031 : Blo 507795 4182031 := bstep (se 1 (by rfl) ⟨3136523, by rfl⟩ : syracuseStep 4182031 = 6273047) B6273047
theorem B1724435 : Blo 507795 1724435 := bstep (se 1 (by rfl) ⟨1293326, by rfl⟩ : syracuseStep 1724435 = 2586653) B2586653
theorem B1724759 : Blo 507795 1724759 := bstep (se 1 (by rfl) ⟨1293569, by rfl⟩ : syracuseStep 1724759 = 2587139) B2587139
theorem B2183705 : Blo 507795 2183705 := bstep (se 2 (by rfl) ⟨818889, by rfl⟩ : syracuseStep 2183705 = 1637779) B1637779
theorem B643783 : Blo 507795 643783 := bstep (se 1 (by rfl) ⟨482837, by rfl⟩ : syracuseStep 643783 = 965675) B965675
theorem B1036999 : Blo 507795 1036999 := bstep (se 1 (by rfl) ⟨777749, by rfl⟩ : syracuseStep 1036999 = 1555499) B1555499
theorem B1626923 : Blo 507795 1626923 := bstep (se 1 (by rfl) ⟨1220192, by rfl⟩ : syracuseStep 1626923 = 2440385) B2440385
theorem B3724289 : Blo 507795 3724289 := bstep (se 2 (by rfl) ⟨1396608, by rfl⟩ : syracuseStep 3724289 = 2793217) B2793217
theorem B1725839 : Blo 507795 1725839 := bstep (se 1 (by rfl) ⟨1294379, by rfl⟩ : syracuseStep 1725839 = 2588759) B2588759
theorem B644527 : Blo 507795 644527 := bstep (se 1 (by rfl) ⟨483395, by rfl⟩ : syracuseStep 644527 = 966791) B966791
theorem B546383 : Blo 507795 546383 := bstep (se 1 (by rfl) ⟨409787, by rfl⟩ : syracuseStep 546383 = 819575) B819575
theorem B2578067 : Blo 507795 2578067 := bstep (se 1 (by rfl) ⟨1933550, by rfl⟩ : syracuseStep 2578067 = 3867101) B3867101
theorem B1627847 : Blo 507795 1627847 := bstep (se 1 (by rfl) ⟨1220885, by rfl⟩ : syracuseStep 1627847 = 2441771) B2441771
theorem B1726163 : Blo 507795 1726163 := bstep (se 1 (by rfl) ⟨1294622, by rfl⟩ : syracuseStep 1726163 = 2589245) B2589245
theorem B6215717 : Blo 507795 6215717 := bstep (se 4 (by rfl) ⟨582723, by rfl⟩ : syracuseStep 6215717 = 1165447) B1165447
theorem B645671 : Blo 507795 645671 := bstep (se 1 (by rfl) ⟨484253, by rfl⟩ : syracuseStep 645671 = 968507) B968507
theorem B645995 : Blo 507795 645995 := bstep (se 1 (by rfl) ⟨484496, by rfl⟩ : syracuseStep 645995 = 968993) B968993
theorem B3857381 : Blo 507795 3857381 := bstep (se 4 (by rfl) ⟨361629, by rfl⟩ : syracuseStep 3857381 = 723259) B723259
theorem B6511589 : Blo 507795 6511589 := bstep (se 4 (by rfl) ⟨610461, by rfl⟩ : syracuseStep 6511589 = 1220923) B1220923
theorem B613499 : Blo 507795 613499 := bstep (se 1 (by rfl) ⟨460124, by rfl⟩ : syracuseStep 613499 = 920249) B920249
theorem B4349123 : Blo 507795 4349123 := bstep (se 1 (by rfl) ⟨3261842, by rfl⟩ : syracuseStep 4349123 = 6523685) B6523685
theorem B3103991 : Blo 507795 3103991 := bstep (se 1 (by rfl) ⟨2327993, by rfl⟩ : syracuseStep 3103991 = 4655987) B4655987
theorem B6544961 : Blo 507795 6544961 := bstep (se 2 (by rfl) ⟨2454360, by rfl⟩ : syracuseStep 6544961 = 4908721) B4908721
theorem B3104477 : Blo 507795 3104477 := bstep (se 3 (by rfl) ⟨582089, by rfl⟩ : syracuseStep 3104477 = 1164179) B1164179
theorem B647291 : Blo 507795 647291 := bstep (se 1 (by rfl) ⟨485468, by rfl⟩ : syracuseStep 647291 = 970937) B970937
theorem B5234867 : Blo 507795 5234867 := bstep (se 1 (by rfl) ⟨3926150, by rfl⟩ : syracuseStep 5234867 = 7852301) B7852301
theorem B4645181 : Blo 507795 4645181 := bstep (se 3 (by rfl) ⟨870971, by rfl⟩ : syracuseStep 4645181 = 1741943) B1741943
theorem B582107 : Blo 507795 582107 := bstep (se 1 (by rfl) ⟨436580, by rfl⟩ : syracuseStep 582107 = 873161) B873161
theorem B8708633 : Blo 507795 8708633 := bstep (se 2 (by rfl) ⟨3265737, by rfl⟩ : syracuseStep 8708633 = 6531475) B6531475
theorem B3269483 : Blo 507795 3269483 := bstep (se 1 (by rfl) ⟨2452112, by rfl⟩ : syracuseStep 3269483 = 4904225) B4904225
theorem B2385353 : Blo 507795 2385353 := bstep (se 2 (by rfl) ⟨894507, by rfl⟩ : syracuseStep 2385353 = 1789015) B1789015
theorem B3107159 : Blo 507795 3107159 := bstep (se 1 (by rfl) ⟨2330369, by rfl⟩ : syracuseStep 3107159 = 4660739) B4660739
theorem B3500525 : Blo 507795 3500525 := bstep (se 3 (by rfl) ⟨656348, by rfl⟩ : syracuseStep 3500525 = 1312697) B1312697
theorem B1632793 : Blo 507795 1632793 := bstep (se 2 (by rfl) ⟨612297, by rfl⟩ : syracuseStep 1632793 = 1224595) B1224595
theorem B8743625 : Blo 507795 8743625 := bstep (se 2 (by rfl) ⟨3278859, by rfl⟩ : syracuseStep 8743625 = 6557719) B6557719
theorem B2583251 : Blo 507795 2583251 := bstep (se 1 (by rfl) ⟨1937438, by rfl⟩ : syracuseStep 2583251 = 3874877) B3874877
theorem B813815 : Blo 507795 813815 := bstep (se 1 (by rfl) ⟨610361, by rfl⟩ : syracuseStep 813815 = 1220723) B1220723
theorem B5532563 : Blo 507795 5532563 := bstep (se 1 (by rfl) ⟨4149422, by rfl⟩ : syracuseStep 5532563 = 8298845) B8298845
theorem B1928387 : Blo 507795 1928387 := bstep (se 1 (by rfl) ⟨1446290, by rfl⟩ : syracuseStep 1928387 = 2892581) B2892581
theorem B1633679 : Blo 507795 1633679 := bstep (se 1 (by rfl) ⟨1225259, by rfl⟩ : syracuseStep 1633679 = 2450519) B2450519
theorem B3501629 : Blo 507795 3501629 := bstep (se 3 (by rfl) ⟨656555, by rfl⟩ : syracuseStep 3501629 = 1313111) B1313111
theorem B1928843 : Blo 507795 1928843 := bstep (se 1 (by rfl) ⟨1446632, by rfl⟩ : syracuseStep 1928843 = 2893265) B2893265
theorem B5795549 : Blo 507795 5795549 := bstep (se 3 (by rfl) ⟨1086665, by rfl⟩ : syracuseStep 5795549 = 2173331) B2173331
theorem B1929055 : Blo 507795 1929055 := bstep (se 1 (by rfl) ⟨1446791, by rfl⟩ : syracuseStep 1929055 = 2893583) B2893583
theorem B814943 : Blo 507795 814943 := bstep (se 1 (by rfl) ⟨611207, by rfl⟩ : syracuseStep 814943 = 1222415) B1222415
theorem B1142711 : Blo 507795 1142711 := bstep (se 1 (by rfl) ⟨857033, by rfl⟩ : syracuseStep 1142711 = 1714067) B1714067
theorem B3665857 : Blo 507795 3665857 := bstep (se 2 (by rfl) ⟨1374696, by rfl⟩ : syracuseStep 3665857 = 2749393) B2749393
theorem B880763 : Blo 507795 880763 := bstep (se 1 (by rfl) ⟨660572, by rfl⟩ : syracuseStep 880763 = 1321145) B1321145
theorem B815455 : Blo 507795 815455 := bstep (se 1 (by rfl) ⟨611591, by rfl⟩ : syracuseStep 815455 = 1223183) B1223183
theorem B1143305 : Blo 507795 1143305 := bstep (se 2 (by rfl) ⟨428739, by rfl⟩ : syracuseStep 1143305 = 857479) B857479
theorem B3863213 : Blo 507795 3863213 := bstep (se 3 (by rfl) ⟨724352, by rfl⟩ : syracuseStep 3863213 = 1448705) B1448705
theorem B1831673 : Blo 507795 1831673 := bstep (se 2 (by rfl) ⟨686877, by rfl⟩ : syracuseStep 1831673 = 1373755) B1373755
theorem B7729937 : Blo 507795 7729937 := bstep (se 2 (by rfl) ⟨2898726, by rfl⟩ : syracuseStep 7729937 = 5797453) B5797453
theorem B1930013 : Blo 507795 1930013 := bstep (se 3 (by rfl) ⟨361877, by rfl⟩ : syracuseStep 1930013 = 723755) B723755
theorem B1930027 : Blo 507795 1930027 := bstep (se 1 (by rfl) ⟨1447520, by rfl⟩ : syracuseStep 1930027 = 2895041) B2895041
theorem B1143647 : Blo 507795 1143647 := bstep (se 1 (by rfl) ⟨857735, by rfl⟩ : syracuseStep 1143647 = 1715471) B1715471
theorem B2585519 : Blo 507795 2585519 := bstep (se 1 (by rfl) ⟨1939139, by rfl⟩ : syracuseStep 2585519 = 3878279) B3878279
theorem B1143827 : Blo 507795 1143827 := bstep (se 1 (by rfl) ⟨857870, by rfl⟩ : syracuseStep 1143827 = 1715741) B1715741
theorem B1144169 : Blo 507795 1144169 := bstep (se 2 (by rfl) ⟨429063, by rfl⟩ : syracuseStep 1144169 = 858127) B858127
theorem B1635689 : Blo 507795 1635689 := bstep (se 2 (by rfl) ⟨613383, by rfl⟩ : syracuseStep 1635689 = 1226767) B1226767
theorem B2061787 : Blo 507795 2061787 := bstep (se 1 (by rfl) ⟨1546340, by rfl⟩ : syracuseStep 2061787 = 3092681) B3092681
theorem B7960313 : Blo 507795 7960313 := bstep (se 2 (by rfl) ⟨2985117, by rfl⟩ : syracuseStep 7960313 = 5970235) B5970235
theorem B1636139 : Blo 507795 1636139 := bstep (se 1 (by rfl) ⟨1227104, by rfl⟩ : syracuseStep 1636139 = 2454209) B2454209
theorem B2062189 : Blo 507795 2062189 := bstep (se 3 (by rfl) ⟨386660, by rfl⟩ : syracuseStep 2062189 = 773321) B773321
theorem B1144763 : Blo 507795 1144763 := bstep (se 1 (by rfl) ⟨858572, by rfl⟩ : syracuseStep 1144763 = 1717145) B1717145
theorem B3274759 : Blo 507795 3274759 := bstep (se 1 (by rfl) ⟨2456069, by rfl⟩ : syracuseStep 3274759 = 4912139) B4912139
theorem B1144889 : Blo 507795 1144889 := bstep (se 2 (by rfl) ⟨429333, by rfl⟩ : syracuseStep 1144889 = 858667) B858667
theorem B2455609 : Blo 507795 2455609 := bstep (se 2 (by rfl) ⟨920853, by rfl⟩ : syracuseStep 2455609 = 1841707) B1841707
theorem B686441 : Blo 507795 686441 := bstep (se 2 (by rfl) ⟨257415, by rfl⟩ : syracuseStep 686441 = 514831) B514831
theorem B14940551 : Blo 507795 14940551 := bstep (se 1 (by rfl) ⟨11205413, by rfl⟩ : syracuseStep 14940551 = 22410827) B22410827
theorem B1145231 : Blo 507795 1145231 := bstep (se 1 (by rfl) ⟨858923, by rfl⟩ : syracuseStep 1145231 = 1717847) B1717847
theorem B817627 : Blo 507795 817627 := bstep (se 1 (by rfl) ⟨613220, by rfl⟩ : syracuseStep 817627 = 1226441) B1226441
theorem B1374707 : Blo 507795 1374707 := bstep (se 1 (by rfl) ⟨1031030, by rfl⟩ : syracuseStep 1374707 = 2062061) B2062061
theorem B1145555 : Blo 507795 1145555 := bstep (se 1 (by rfl) ⟨859166, by rfl⟩ : syracuseStep 1145555 = 1718333) B1718333
theorem B2653103 : Blo 507795 2653103 := bstep (se 1 (by rfl) ⟨1989827, by rfl⟩ : syracuseStep 2653103 = 3979655) B3979655
theorem B1375163 : Blo 507795 1375163 := bstep (se 1 (by rfl) ⟨1031372, by rfl⟩ : syracuseStep 1375163 = 2062745) B2062745
theorem B3865643 : Blo 507795 3865643 := bstep (se 1 (by rfl) ⟨2899232, by rfl⟩ : syracuseStep 3865643 = 5798465) B5798465
theorem B818255 : Blo 507795 818255 := bstep (se 1 (by rfl) ⟨613691, by rfl⟩ : syracuseStep 818255 = 1227383) B1227383
theorem B4914371 : Blo 507795 4914371 := bstep (se 1 (by rfl) ⟨3685778, by rfl⟩ : syracuseStep 4914371 = 7371557) B7371557
theorem B181140941 : Blo 507795 181140941 := bstep (se 3 (by rfl) ⟨33963926, by rfl⟩ : syracuseStep 181140941 = 67927853) B67927853
theorem B1342985 : Blo 507795 1342985 := bstep (se 2 (by rfl) ⟨503619, by rfl⟩ : syracuseStep 1342985 = 1007239) B1007239
theorem B1867303 : Blo 507795 1867303 := bstep (se 1 (by rfl) ⟨1400477, by rfl⟩ : syracuseStep 1867303 = 2800955) B2800955
theorem B1146491 : Blo 507795 1146491 := bstep (se 1 (by rfl) ⟨859868, by rfl⟩ : syracuseStep 1146491 = 1719737) B1719737
theorem B1146617 : Blo 507795 1146617 := bstep (se 2 (by rfl) ⟨429981, by rfl⟩ : syracuseStep 1146617 = 859963) B859963
theorem B1933217 : Blo 507795 1933217 := bstep (se 2 (by rfl) ⟨724956, by rfl⟩ : syracuseStep 1933217 = 1449913) B1449913
theorem B6553619 : Blo 507795 6553619 := bstep (se 1 (by rfl) ⟨4915214, by rfl⟩ : syracuseStep 6553619 = 9830429) B9830429
theorem B1867835 : Blo 507795 1867835 := bstep (se 1 (by rfl) ⟨1400876, by rfl⟩ : syracuseStep 1867835 = 2801753) B2801753
theorem B15728717 : Blo 507795 15728717 := bstep (se 3 (by rfl) ⟨2949134, by rfl⟩ : syracuseStep 15728717 = 5898269) B5898269
theorem B1147247 : Blo 507795 1147247 := bstep (se 1 (by rfl) ⟨860435, by rfl⟩ : syracuseStep 1147247 = 1720871) B1720871
theorem B1147319 : Blo 507795 1147319 := bstep (se 1 (by rfl) ⟨860489, by rfl⟩ : syracuseStep 1147319 = 1720979) B1720979
theorem B1147463 : Blo 507795 1147463 := bstep (se 1 (by rfl) ⟨860597, by rfl⟩ : syracuseStep 1147463 = 1721195) B1721195
theorem B1147499 : Blo 507795 1147499 := bstep (se 1 (by rfl) ⟨860624, by rfl⟩ : syracuseStep 1147499 = 1721249) B1721249
theorem B2589407 : Blo 507795 2589407 := bstep (se 1 (by rfl) ⟨1942055, by rfl⟩ : syracuseStep 2589407 = 3884111) B3884111
theorem B3867587 : Blo 507795 3867587 := bstep (se 1 (by rfl) ⟨2900690, by rfl⟩ : syracuseStep 3867587 = 5801381) B5801381
theorem B1147895 : Blo 507795 1147895 := bstep (se 1 (by rfl) ⟨860921, by rfl⟩ : syracuseStep 1147895 = 1721843) B1721843
theorem B4719809 : Blo 507795 4719809 := bstep (se 2 (by rfl) ⟨1769928, by rfl⟩ : syracuseStep 4719809 = 3539857) B3539857
theorem B1148255 : Blo 507795 1148255 := bstep (se 1 (by rfl) ⟨861191, by rfl⟩ : syracuseStep 1148255 = 1722383) B1722383
theorem B3671419 : Blo 507795 3671419 := bstep (se 1 (by rfl) ⟨2753564, by rfl⟩ : syracuseStep 3671419 = 5507129) B5507129
theorem B2459069 : Blo 507795 2459069 := bstep (se 3 (by rfl) ⟨461075, by rfl⟩ : syracuseStep 2459069 = 922151) B922151
theorem B1148651 : Blo 507795 1148651 := bstep (se 1 (by rfl) ⟨861488, by rfl⟩ : syracuseStep 1148651 = 1722977) B1722977
theorem B1935191 : Blo 507795 1935191 := bstep (se 1 (by rfl) ⟨1451393, by rfl⟩ : syracuseStep 1935191 = 2902787) B2902787
theorem B1148777 : Blo 507795 1148777 := bstep (se 2 (by rfl) ⟨430791, by rfl⟩ : syracuseStep 1148777 = 861583) B861583
theorem B4884461 : Blo 507795 4884461 := bstep (se 3 (by rfl) ⟨915836, by rfl⟩ : syracuseStep 4884461 = 1831673) B1831673
theorem B1837241 : Blo 507795 1837241 := bstep (se 2 (by rfl) ⟨688965, by rfl⟩ : syracuseStep 1837241 = 1377931) B1377931
theorem B3541391 : Blo 507795 3541391 := bstep (se 1 (by rfl) ⟨2656043, by rfl⟩ : syracuseStep 3541391 = 5312087) B5312087
theorem B2067023 : Blo 507795 2067023 := bstep (se 1 (by rfl) ⟨1550267, by rfl⟩ : syracuseStep 2067023 = 3100535) B3100535
theorem B1149623 : Blo 507795 1149623 := bstep (se 1 (by rfl) ⟨862217, by rfl⟩ : syracuseStep 1149623 = 1724435) B1724435
theorem B1149839 : Blo 507795 1149839 := bstep (se 1 (by rfl) ⟨862379, by rfl⟩ : syracuseStep 1149839 = 1724759) B1724759
theorem B4197491 : Blo 507795 4197491 := bstep (se 1 (by rfl) ⟨3148118, by rfl⟩ : syracuseStep 4197491 = 6296237) B6296237
theorem B1150559 : Blo 507795 1150559 := bstep (se 1 (by rfl) ⟨862919, by rfl⟩ : syracuseStep 1150559 = 1725839) B1725839
theorem B1085231 : Blo 507795 1085231 := bstep (se 1 (by rfl) ⟨813923, by rfl⟩ : syracuseStep 1085231 = 1627847) B1627847
theorem B1150775 : Blo 507795 1150775 := bstep (se 1 (by rfl) ⟨863081, by rfl⟩ : syracuseStep 1150775 = 1726163) B1726163
theorem B6360941 : Blo 507795 6360941 := bstep (se 3 (by rfl) ⟨1192676, by rfl⟩ : syracuseStep 6360941 = 2385353) B2385353
theorem B2363293 : Blo 507795 2363293 := bstep (se 3 (by rfl) ⟨443117, by rfl⟩ : syracuseStep 2363293 = 886235) B886235
theorem B1151081 : Blo 507795 1151081 := bstep (se 2 (by rfl) ⟨431655, by rfl⟩ : syracuseStep 1151081 = 863311) B863311
theorem B2363755 : Blo 507795 2363755 := bstep (se 1 (by rfl) ⟨1772816, by rfl⟩ : syracuseStep 2363755 = 3545633) B3545633
theorem B6558083 : Blo 507795 6558083 := bstep (se 1 (by rfl) ⟨4918562, by rfl⟩ : syracuseStep 6558083 = 9837125) B9837125
theorem B2069327 : Blo 507795 2069327 := bstep (se 1 (by rfl) ⟨1551995, by rfl⟩ : syracuseStep 2069327 = 3103991) B3103991
theorem B4363307 : Blo 507795 4363307 := bstep (se 1 (by rfl) ⟨3272480, by rfl⟩ : syracuseStep 4363307 = 6544961) B6544961
theorem B1447055 : Blo 507795 1447055 := bstep (se 1 (by rfl) ⟨1085291, by rfl⟩ : syracuseStep 1447055 = 2170583) B2170583
theorem B2069651 : Blo 507795 2069651 := bstep (se 1 (by rfl) ⟨1552238, by rfl⟩ : syracuseStep 2069651 = 3104477) B3104477
theorem B4887809 : Blo 507795 4887809 := bstep (se 2 (by rfl) ⟨1832928, by rfl⟩ : syracuseStep 4887809 = 3665857) B3665857
theorem B857695 : Blo 507795 857695 := bstep (se 1 (by rfl) ⟨643271, by rfl⟩ : syracuseStep 857695 = 1286543) B1286543
theorem B5805755 : Blo 507795 5805755 := bstep (se 1 (by rfl) ⟨4354316, by rfl⟩ : syracuseStep 5805755 = 8708633) B8708633
theorem B1087273 : Blo 507795 1087273 := bstep (se 2 (by rfl) ⟨407727, by rfl⟩ : syracuseStep 1087273 = 815455) B815455
theorem B857911 : Blo 507795 857911 := bstep (se 1 (by rfl) ⟨643433, by rfl⟩ : syracuseStep 857911 = 1286867) B1286867
theorem B858377 : Blo 507795 858377 := bstep (se 2 (by rfl) ⟨321891, by rfl⟩ : syracuseStep 858377 = 643783) B643783
theorem B1382665 : Blo 507795 1382665 := bstep (se 2 (by rfl) ⟨518499, by rfl⟩ : syracuseStep 1382665 = 1036999) B1036999
theorem B3873419 : Blo 507795 3873419 := bstep (se 1 (by rfl) ⟨2905064, by rfl⟩ : syracuseStep 3873419 = 5810129) B5810129
theorem B2759447 : Blo 507795 2759447 := bstep (se 1 (by rfl) ⟨2069585, by rfl⟩ : syracuseStep 2759447 = 4139171) B4139171
theorem B4135799 : Blo 507795 4135799 := bstep (se 1 (by rfl) ⟨3101849, by rfl⟩ : syracuseStep 4135799 = 6203699) B6203699
theorem B2071439 : Blo 507795 2071439 := bstep (se 1 (by rfl) ⟨1553579, by rfl⟩ : syracuseStep 2071439 = 3107159) B3107159
theorem B2333683 : Blo 507795 2333683 := bstep (se 1 (by rfl) ⟨1750262, by rfl⟩ : syracuseStep 2333683 = 3500525) B3500525
theorem B21437459 : Blo 507795 21437459 := bstep (se 1 (by rfl) ⟨16078094, by rfl⟩ : syracuseStep 21437459 = 32156189) B32156189
theorem B859369 : Blo 507795 859369 := bstep (se 2 (by rfl) ⟨322263, by rfl⟩ : syracuseStep 859369 = 644527) B644527
theorem B859423 : Blo 507795 859423 := bstep (se 1 (by rfl) ⟨644567, by rfl⟩ : syracuseStep 859423 = 1289135) B1289135
theorem B1285591 : Blo 507795 1285591 := bstep (se 1 (by rfl) ⟨964193, by rfl⟩ : syracuseStep 1285591 = 1928387) B1928387
theorem B1089119 : Blo 507795 1089119 := bstep (se 1 (by rfl) ⟨816839, by rfl⟩ : syracuseStep 1089119 = 1633679) B1633679
theorem B859835 : Blo 507795 859835 := bstep (se 1 (by rfl) ⟨644876, by rfl⟩ : syracuseStep 859835 = 1289753) B1289753
theorem B2334419 : Blo 507795 2334419 := bstep (se 1 (by rfl) ⟨1750814, by rfl⟩ : syracuseStep 2334419 = 3501629) B3501629
theorem B1285895 : Blo 507795 1285895 := bstep (se 1 (by rfl) ⟨964421, by rfl⟩ : syracuseStep 1285895 = 1928843) B1928843
theorem B761807 : Blo 507795 761807 := bstep (se 1 (by rfl) ⟨571355, by rfl⟩ : syracuseStep 761807 = 1142711) B1142711
theorem B4366345 : Blo 507795 4366345 := bstep (se 2 (by rfl) ⟨1637379, by rfl⟩ : syracuseStep 4366345 = 3274759) B3274759
theorem B2760875 : Blo 507795 2760875 := bstep (se 1 (by rfl) ⟨2070656, by rfl⟩ : syracuseStep 2760875 = 4141313) B4141313
theorem B762203 : Blo 507795 762203 := bstep (se 1 (by rfl) ⟨571652, by rfl⟩ : syracuseStep 762203 = 1143305) B1143305
theorem B2073089 : Blo 507795 2073089 := bstep (se 2 (by rfl) ⟨777408, by rfl⟩ : syracuseStep 2073089 = 1554817) B1554817
theorem B5153291 : Blo 507795 5153291 := bstep (se 1 (by rfl) ⟨3864968, by rfl⟩ : syracuseStep 5153291 = 7729937) B7729937
theorem B1286675 : Blo 507795 1286675 := bstep (se 1 (by rfl) ⟨965006, by rfl⟩ : syracuseStep 1286675 = 1930013) B1930013
theorem B762431 : Blo 507795 762431 := bstep (se 1 (by rfl) ⟨571823, by rfl⟩ : syracuseStep 762431 = 1143647) B1143647
theorem B1090169 : Blo 507795 1090169 := bstep (se 2 (by rfl) ⟨408813, by rfl⟩ : syracuseStep 1090169 = 817627) B817627
theorem B762551 : Blo 507795 762551 := bstep (se 1 (by rfl) ⟨571913, by rfl⟩ : syracuseStep 762551 = 1143827) B1143827
theorem B762779 : Blo 507795 762779 := bstep (se 1 (by rfl) ⟨572084, by rfl⟩ : syracuseStep 762779 = 1144169) B1144169
theorem B1090459 : Blo 507795 1090459 := bstep (se 1 (by rfl) ⟨817844, by rfl⟩ : syracuseStep 1090459 = 1635689) B1635689
theorem B1090759 : Blo 507795 1090759 := bstep (se 1 (by rfl) ⟨818069, by rfl⟩ : syracuseStep 1090759 = 1636139) B1636139
theorem B1549561 : Blo 507795 1549561 := bstep (se 2 (by rfl) ⟨581085, by rfl⟩ : syracuseStep 1549561 = 1162171) B1162171
theorem B763175 : Blo 507795 763175 := bstep (se 1 (by rfl) ⟨572381, by rfl⟩ : syracuseStep 763175 = 1144763) B1144763
theorem B1451303 : Blo 507795 1451303 := bstep (se 1 (by rfl) ⟨1088477, by rfl⟩ : syracuseStep 1451303 = 2176955) B2176955
theorem B3581293 : Blo 507795 3581293 := bstep (se 3 (by rfl) ⟨671492, by rfl⟩ : syracuseStep 3581293 = 1342985) B1342985
theorem B763259 : Blo 507795 763259 := bstep (se 1 (by rfl) ⟨572444, by rfl⟩ : syracuseStep 763259 = 1144889) B1144889
theorem B861563 : Blo 507795 861563 := bstep (se 1 (by rfl) ⟨646172, by rfl⟩ : syracuseStep 861563 = 1292345) B1292345
theorem B763385 : Blo 507795 763385 := bstep (se 2 (by rfl) ⟨286269, by rfl⟩ : syracuseStep 763385 = 572539) B572539
theorem B763487 : Blo 507795 763487 := bstep (se 1 (by rfl) ⟨572615, by rfl⟩ : syracuseStep 763487 = 1145231) B1145231
theorem B1713851 : Blo 507795 1713851 := bstep (se 1 (by rfl) ⟨1285388, by rfl⟩ : syracuseStep 1713851 = 2570777) B2570777
theorem B763703 : Blo 507795 763703 := bstep (se 1 (by rfl) ⟨572777, by rfl⟩ : syracuseStep 763703 = 1145555) B1145555
theorem B764009 : Blo 507795 764009 := bstep (se 2 (by rfl) ⟨286503, by rfl⟩ : syracuseStep 764009 = 573007) B573007
theorem B1550465 : Blo 507795 1550465 := bstep (se 2 (by rfl) ⟨581424, by rfl⟩ : syracuseStep 1550465 = 1162849) B1162849
theorem B1288457 : Blo 507795 1288457 := bstep (se 2 (by rfl) ⟨483171, by rfl⟩ : syracuseStep 1288457 = 966343) B966343
theorem B120760627 : Blo 507795 120760627 := bstep (se 1 (by rfl) ⟨90570470, by rfl⟩ : syracuseStep 120760627 = 181140941) B181140941
theorem B1255771 : Blo 507795 1255771 := bstep (se 1 (by rfl) ⟨941828, by rfl⟩ : syracuseStep 1255771 = 1883657) B1883657
theorem B862555 : Blo 507795 862555 := bstep (se 1 (by rfl) ⟨646916, by rfl⟩ : syracuseStep 862555 = 1293833) B1293833
theorem B764327 : Blo 507795 764327 := bstep (se 1 (by rfl) ⟨573245, by rfl⟩ : syracuseStep 764327 = 1146491) B1146491
theorem B18557363 : Blo 507795 18557363 := bstep (se 1 (by rfl) ⟨13918022, by rfl⟩ : syracuseStep 18557363 = 27836045) B27836045
theorem B2894291 : Blo 507795 2894291 := bstep (se 1 (by rfl) ⟨2170718, by rfl⟩ : syracuseStep 2894291 = 4341437) B4341437
theorem B764411 : Blo 507795 764411 := bstep (se 1 (by rfl) ⟨573308, by rfl⟩ : syracuseStep 764411 = 1146617) B1146617
theorem B1288811 : Blo 507795 1288811 := bstep (se 1 (by rfl) ⟨966608, by rfl⟩ : syracuseStep 1288811 = 1933217) B1933217
theorem B764537 : Blo 507795 764537 := bstep (se 2 (by rfl) ⟨286701, by rfl⟩ : syracuseStep 764537 = 573403) B573403
theorem B764591 : Blo 507795 764591 := bstep (se 1 (by rfl) ⟨573443, by rfl⟩ : syracuseStep 764591 = 1146887) B1146887
theorem B764639 : Blo 507795 764639 := bstep (se 1 (by rfl) ⟨573479, by rfl⟩ : syracuseStep 764639 = 1146959) B1146959
theorem B1747855 : Blo 507795 1747855 := bstep (se 1 (by rfl) ⟨1310891, by rfl⟩ : syracuseStep 1747855 = 2621783) B2621783
theorem B764903 : Blo 507795 764903 := bstep (se 1 (by rfl) ⟨573677, by rfl⟩ : syracuseStep 764903 = 1147355) B1147355
theorem B3255335 : Blo 507795 3255335 := bstep (se 1 (by rfl) ⟨2441501, by rfl⟩ : syracuseStep 3255335 = 4883003) B4883003
theorem B765161 : Blo 507795 765161 := bstep (se 2 (by rfl) ⟨286935, by rfl⟩ : syracuseStep 765161 = 573871) B573871
theorem B1223923 : Blo 507795 1223923 := bstep (se 1 (by rfl) ⟨917942, by rfl⟩ : syracuseStep 1223923 = 1835885) B1835885
theorem B1289459 : Blo 507795 1289459 := bstep (se 1 (by rfl) ⟨967094, by rfl⟩ : syracuseStep 1289459 = 1934189) B1934189
theorem B765215 : Blo 507795 765215 := bstep (se 1 (by rfl) ⟨573911, by rfl⟩ : syracuseStep 765215 = 1147823) B1147823
theorem B863527 : Blo 507795 863527 := bstep (se 1 (by rfl) ⟨647645, by rfl⟩ : syracuseStep 863527 = 1295291) B1295291
theorem B2895223 : Blo 507795 2895223 := bstep (se 1 (by rfl) ⟨2171417, by rfl⟩ : syracuseStep 2895223 = 4342835) B4342835
theorem B765383 : Blo 507795 765383 := bstep (se 1 (by rfl) ⟨574037, by rfl⟩ : syracuseStep 765383 = 1148075) B1148075
theorem B1715795 : Blo 507795 1715795 := bstep (se 1 (by rfl) ⟨1286846, by rfl⟩ : syracuseStep 1715795 = 2573693) B2573693
theorem B1289915 : Blo 507795 1289915 := bstep (se 1 (by rfl) ⟨967436, by rfl⟩ : syracuseStep 1289915 = 1934873) B1934873
theorem B765737 : Blo 507795 765737 := bstep (se 2 (by rfl) ⟨287151, by rfl⟩ : syracuseStep 765737 = 574303) B574303
theorem B765743 : Blo 507795 765743 := bstep (se 1 (by rfl) ⟨574307, by rfl⟩ : syracuseStep 765743 = 1148615) B1148615
theorem B1454105 : Blo 507795 1454105 := bstep (se 2 (by rfl) ⟨545289, by rfl⟩ : syracuseStep 1454105 = 1090579) B1090579
theorem B1290451 : Blo 507795 1290451 := bstep (se 1 (by rfl) ⟨967838, by rfl⟩ : syracuseStep 1290451 = 1935677) B1935677
theorem B766217 : Blo 507795 766217 := bstep (se 2 (by rfl) ⟨287331, by rfl⟩ : syracuseStep 766217 = 574663) B574663
theorem B766319 : Blo 507795 766319 := bstep (se 1 (by rfl) ⟨574739, by rfl⟩ : syracuseStep 766319 = 1149479) B1149479
theorem B1454561 : Blo 507795 1454561 := bstep (se 2 (by rfl) ⟨545460, by rfl⟩ : syracuseStep 1454561 = 1090921) B1090921
theorem B4370993 : Blo 507795 4370993 := bstep (se 2 (by rfl) ⟨1639122, by rfl⟩ : syracuseStep 4370993 = 3278245) B3278245
theorem B766535 : Blo 507795 766535 := bstep (se 1 (by rfl) ⟨574901, by rfl⟩ : syracuseStep 766535 = 1149803) B1149803
theorem B766571 : Blo 507795 766571 := bstep (se 1 (by rfl) ⟨574928, by rfl⟩ : syracuseStep 766571 = 1149857) B1149857
theorem B4338461 : Blo 507795 4338461 := bstep (se 3 (by rfl) ⟨813461, by rfl⟩ : syracuseStep 4338461 = 1626923) B1626923
theorem B766799 : Blo 507795 766799 := bstep (se 1 (by rfl) ⟨575099, by rfl⟩ : syracuseStep 766799 = 1150199) B1150199
theorem B1291403 : Blo 507795 1291403 := bstep (se 1 (by rfl) ⟨968552, by rfl⟩ : syracuseStep 1291403 = 1937105) B1937105
theorem B767195 : Blo 507795 767195 := bstep (se 1 (by rfl) ⟨575396, by rfl⟩ : syracuseStep 767195 = 1150793) B1150793
theorem B1455347 : Blo 507795 1455347 := bstep (se 1 (by rfl) ⟨1091510, by rfl⟩ : syracuseStep 1455347 = 2183021) B2183021
theorem B767369 : Blo 507795 767369 := bstep (se 2 (by rfl) ⟨287763, by rfl⟩ : syracuseStep 767369 = 575527) B575527
theorem B1291859 : Blo 507795 1291859 := bstep (se 1 (by rfl) ⟨968894, by rfl⟩ : syracuseStep 1291859 = 1937789) B1937789
theorem B1455803 : Blo 507795 1455803 := bstep (se 1 (by rfl) ⟨1091852, by rfl⟩ : syracuseStep 1455803 = 2183705) B2183705
theorem B964399 : Blo 507795 964399 := bstep (se 1 (by rfl) ⟨723299, by rfl⟩ : syracuseStep 964399 = 1446599) B1446599
theorem B6993719 : Blo 507795 6993719 := bstep (se 1 (by rfl) ⟨5245289, by rfl⟩ : syracuseStep 6993719 = 10490579) B10490579
theorem B2177057 : Blo 507795 2177057 := bstep (se 2 (by rfl) ⟨816396, by rfl⟩ : syracuseStep 2177057 = 1632793) B1632793
theorem B1292719 : Blo 507795 1292719 := bstep (se 1 (by rfl) ⟨969539, by rfl⟩ : syracuseStep 1292719 = 1939079) B1939079
theorem B1718711 : Blo 507795 1718711 := bstep (se 1 (by rfl) ⟨1289033, by rfl⟩ : syracuseStep 1718711 = 2578067) B2578067
theorem B20855369 : Blo 507795 20855369 := bstep (se 2 (by rfl) ⟨7820763, by rfl⟩ : syracuseStep 20855369 = 15641527) B15641527
theorem B571999 : Blo 507795 571999 := bstep (se 1 (by rfl) ⟨428999, by rfl⟩ : syracuseStep 571999 = 857999) B857999
theorem B3259075 : Blo 507795 3259075 := bstep (se 1 (by rfl) ⟨2444306, by rfl⟩ : syracuseStep 3259075 = 4888613) B4888613
theorem B4143811 : Blo 507795 4143811 := bstep (se 1 (by rfl) ⟨3107858, by rfl⟩ : syracuseStep 4143811 = 6215717) B6215717
theorem B1293023 : Blo 507795 1293023 := bstep (se 1 (by rfl) ⟨969767, by rfl⟩ : syracuseStep 1293023 = 1939535) B1939535
theorem B3718007 : Blo 507795 3718007 := bstep (se 1 (by rfl) ⟨2788505, by rfl⟩ : syracuseStep 3718007 = 5577011) B5577011
theorem B1457021 : Blo 507795 1457021 := bstep (se 3 (by rfl) ⟨273191, by rfl⟩ : syracuseStep 1457021 = 546383) B546383
theorem B2571587 : Blo 507795 2571587 := bstep (se 1 (by rfl) ⟨1928690, by rfl⟩ : syracuseStep 2571587 = 3857381) B3857381
theorem B4341059 : Blo 507795 4341059 := bstep (se 1 (by rfl) ⟨3255794, by rfl⟩ : syracuseStep 4341059 = 6511589) B6511589
theorem B1293691 : Blo 507795 1293691 := bstep (se 1 (by rfl) ⟨970268, by rfl⟩ : syracuseStep 1293691 = 1940537) B1940537
theorem B2899415 : Blo 507795 2899415 := bstep (se 1 (by rfl) ⟨2174561, by rfl⟩ : syracuseStep 2899415 = 4349123) B4349123
theorem B2932307 : Blo 507795 2932307 := bstep (se 1 (by rfl) ⟨2199230, by rfl⟩ : syracuseStep 2932307 = 4398461) B4398461
theorem B6209141 : Blo 507795 6209141 := bstep (se 5 (by rfl) ⟨291053, by rfl⟩ : syracuseStep 6209141 = 582107) B582107
theorem B966305 : Blo 507795 966305 := bstep (se 2 (by rfl) ⟨362364, by rfl⟩ : syracuseStep 966305 = 724729) B724729
theorem B573151 : Blo 507795 573151 := bstep (se 1 (by rfl) ⟨429863, by rfl⟩ : syracuseStep 573151 = 859727) B859727
theorem B2572073 : Blo 507795 2572073 := bstep (se 2 (by rfl) ⟨964527, by rfl⟩ : syracuseStep 2572073 = 1929055) B1929055
theorem B1294127 : Blo 507795 1294127 := bstep (se 1 (by rfl) ⟨970595, by rfl⟩ : syracuseStep 1294127 = 1941191) B1941191
theorem B3915649 : Blo 507795 3915649 := bstep (se 2 (by rfl) ⟨1468368, by rfl⟩ : syracuseStep 3915649 = 2936737) B2936737
theorem B507803 : Blo 507795 507803 := bstep (se 1 (by rfl) ⟨380852, by rfl⟩ : syracuseStep 507803 = 761705) B761705
theorem B507855 : Blo 507795 507855 := bstep (se 1 (by rfl) ⟨380891, by rfl⟩ : syracuseStep 507855 = 761783) B761783
theorem B507879 : Blo 507795 507879 := bstep (se 1 (by rfl) ⟨380909, by rfl⟩ : syracuseStep 507879 = 761819) B761819
theorem B3489911 : Blo 507795 3489911 := bstep (se 1 (by rfl) ⟨2617433, by rfl⟩ : syracuseStep 3489911 = 5234867) B5234867
theorem B3096787 : Blo 507795 3096787 := bstep (se 1 (by rfl) ⟨2322590, by rfl⟩ : syracuseStep 3096787 = 4645181) B4645181
theorem B508191 : Blo 507795 508191 := bstep (se 1 (by rfl) ⟨381143, by rfl⟩ : syracuseStep 508191 = 762287) B762287
theorem B573727 : Blo 507795 573727 := bstep (se 1 (by rfl) ⟨430295, by rfl⟩ : syracuseStep 573727 = 860591) B860591
theorem B508251 : Blo 507795 508251 := bstep (se 1 (by rfl) ⟨381188, by rfl⟩ : syracuseStep 508251 = 762377) B762377
theorem B508271 : Blo 507795 508271 := bstep (se 1 (by rfl) ⟨381203, by rfl⟩ : syracuseStep 508271 = 762407) B762407
theorem B508327 : Blo 507795 508327 := bstep (se 1 (by rfl) ⟨381245, by rfl⟩ : syracuseStep 508327 = 762491) B762491
theorem B967079 : Blo 507795 967079 := bstep (se 1 (by rfl) ⟨725309, by rfl⟩ : syracuseStep 967079 = 1450619) B1450619
theorem B1294775 : Blo 507795 1294775 := bstep (se 1 (by rfl) ⟨971081, by rfl⟩ : syracuseStep 1294775 = 1942163) B1942163
theorem B508411 : Blo 507795 508411 := bstep (se 1 (by rfl) ⟨381308, by rfl⟩ : syracuseStep 508411 = 762617) B762617
theorem B508479 : Blo 507795 508479 := bstep (se 1 (by rfl) ⟨381359, by rfl⟩ : syracuseStep 508479 = 762719) B762719
theorem B967231 : Blo 507795 967231 := bstep (se 1 (by rfl) ⟨725423, by rfl⟩ : syracuseStep 967231 = 1450847) B1450847
theorem B574015 : Blo 507795 574015 := bstep (se 1 (by rfl) ⟨430511, by rfl⟩ : syracuseStep 574015 = 861023) B861023
theorem B508487 : Blo 507795 508487 := bstep (se 1 (by rfl) ⟨381365, by rfl⟩ : syracuseStep 508487 = 762731) B762731
theorem B3260999 : Blo 507795 3260999 := bstep (se 1 (by rfl) ⟨2445749, by rfl⟩ : syracuseStep 3260999 = 4891499) B4891499
theorem B2179655 : Blo 507795 2179655 := bstep (se 1 (by rfl) ⟨1634741, by rfl⟩ : syracuseStep 2179655 = 3269483) B3269483
theorem B1229419 : Blo 507795 1229419 := bstep (se 1 (by rfl) ⟨922064, by rfl⟩ : syracuseStep 1229419 = 1844129) B1844129
theorem B7455415 : Blo 507795 7455415 := bstep (se 1 (by rfl) ⟨5591561, by rfl⟩ : syracuseStep 7455415 = 11183123) B11183123
theorem B508639 : Blo 507795 508639 := bstep (se 1 (by rfl) ⟨381479, by rfl⟩ : syracuseStep 508639 = 762959) B762959
theorem B508719 : Blo 507795 508719 := bstep (se 1 (by rfl) ⟨381539, by rfl⟩ : syracuseStep 508719 = 763079) B763079
theorem B508827 : Blo 507795 508827 := bstep (se 1 (by rfl) ⟨381620, by rfl⟩ : syracuseStep 508827 = 763241) B763241
theorem B508879 : Blo 507795 508879 := bstep (se 1 (by rfl) ⟨381659, by rfl⟩ : syracuseStep 508879 = 763319) B763319
theorem B508903 : Blo 507795 508903 := bstep (se 1 (by rfl) ⟨381677, by rfl⟩ : syracuseStep 508903 = 763355) B763355
theorem B2573369 : Blo 507795 2573369 := bstep (se 2 (by rfl) ⟨965013, by rfl⟩ : syracuseStep 2573369 = 1930027) B1930027
theorem B509215 : Blo 507795 509215 := bstep (se 1 (by rfl) ⟨381911, by rfl⟩ : syracuseStep 509215 = 763823) B763823
theorem B509275 : Blo 507795 509275 := bstep (se 1 (by rfl) ⟨381956, by rfl⟩ : syracuseStep 509275 = 763913) B763913
theorem B509295 : Blo 507795 509295 := bstep (se 1 (by rfl) ⟨381971, by rfl⟩ : syracuseStep 509295 = 763943) B763943
theorem B574843 : Blo 507795 574843 := bstep (se 1 (by rfl) ⟨431132, by rfl⟩ : syracuseStep 574843 = 862265) B862265
theorem B509351 : Blo 507795 509351 := bstep (se 1 (by rfl) ⟨382013, by rfl⟩ : syracuseStep 509351 = 764027) B764027
theorem B1721789 : Blo 507795 1721789 := bstep (se 3 (by rfl) ⟨322835, by rfl⟩ : syracuseStep 1721789 = 645671) B645671
theorem B509435 : Blo 507795 509435 := bstep (se 1 (by rfl) ⟨382076, by rfl⟩ : syracuseStep 509435 = 764153) B764153
theorem B35276309 : Blo 507795 35276309 := bstep (se 6 (by rfl) ⟨826788, by rfl⟩ : syracuseStep 35276309 = 1653577) B1653577
theorem B509503 : Blo 507795 509503 := bstep (se 1 (by rfl) ⟨382127, by rfl⟩ : syracuseStep 509503 = 764255) B764255
theorem B509511 : Blo 507795 509511 := bstep (se 1 (by rfl) ⟨382133, by rfl⟩ : syracuseStep 509511 = 764267) B764267
theorem B968287 : Blo 507795 968287 := bstep (se 1 (by rfl) ⟨726215, by rfl⟩ : syracuseStep 968287 = 1452431) B1452431
theorem B509663 : Blo 507795 509663 := bstep (se 1 (by rfl) ⟨382247, by rfl⟩ : syracuseStep 509663 = 764495) B764495
theorem B509743 : Blo 507795 509743 := bstep (se 1 (by rfl) ⟨382307, by rfl⟩ : syracuseStep 509743 = 764615) B764615
theorem B1722167 : Blo 507795 1722167 := bstep (se 1 (by rfl) ⟨1291625, by rfl⟩ : syracuseStep 1722167 = 2583251) B2583251
theorem B542543 : Blo 507795 542543 := bstep (se 1 (by rfl) ⟨406907, by rfl⟩ : syracuseStep 542543 = 813815) B813815
theorem B575311 : Blo 507795 575311 := bstep (se 1 (by rfl) ⟨431483, by rfl⟩ : syracuseStep 575311 = 862967) B862967
theorem B509851 : Blo 507795 509851 := bstep (se 1 (by rfl) ⟨382388, by rfl⟩ : syracuseStep 509851 = 764777) B764777
theorem B3688375 : Blo 507795 3688375 := bstep (se 1 (by rfl) ⟨2766281, by rfl⟩ : syracuseStep 3688375 = 5532563) B5532563
theorem B509903 : Blo 507795 509903 := bstep (se 1 (by rfl) ⟨382427, by rfl⟩ : syracuseStep 509903 = 764855) B764855
theorem B509927 : Blo 507795 509927 := bstep (se 1 (by rfl) ⟨382445, by rfl⟩ : syracuseStep 509927 = 764891) B764891
theorem B575707 : Blo 507795 575707 := bstep (se 1 (by rfl) ⟨431780, by rfl⟩ : syracuseStep 575707 = 863561) B863561
theorem B1722653 : Blo 507795 1722653 := bstep (se 3 (by rfl) ⟨322997, by rfl⟩ : syracuseStep 1722653 = 645995) B645995
theorem B510239 : Blo 507795 510239 := bstep (se 1 (by rfl) ⟨382679, by rfl⟩ : syracuseStep 510239 = 765359) B765359
theorem B510299 : Blo 507795 510299 := bstep (se 1 (by rfl) ⟨382724, by rfl⟩ : syracuseStep 510299 = 765449) B765449
theorem B510319 : Blo 507795 510319 := bstep (se 1 (by rfl) ⟨382739, by rfl⟩ : syracuseStep 510319 = 765479) B765479
theorem B510375 : Blo 507795 510375 := bstep (se 1 (by rfl) ⟨382781, by rfl⟩ : syracuseStep 510375 = 765563) B765563
theorem B510459 : Blo 507795 510459 := bstep (se 1 (by rfl) ⟨382844, by rfl⟩ : syracuseStep 510459 = 765689) B765689
theorem B543295 : Blo 507795 543295 := bstep (se 1 (by rfl) ⟨407471, by rfl⟩ : syracuseStep 543295 = 814943) B814943
theorem B510527 : Blo 507795 510527 := bstep (se 1 (by rfl) ⟨382895, by rfl⟩ : syracuseStep 510527 = 765791) B765791
theorem B510535 : Blo 507795 510535 := bstep (se 1 (by rfl) ⟨382901, by rfl⟩ : syracuseStep 510535 = 765803) B765803
theorem B510687 : Blo 507795 510687 := bstep (se 1 (by rfl) ⟨383015, by rfl⟩ : syracuseStep 510687 = 766031) B766031
theorem B510767 : Blo 507795 510767 := bstep (se 1 (by rfl) ⟨383075, by rfl⟩ : syracuseStep 510767 = 766151) B766151
theorem B510875 : Blo 507795 510875 := bstep (se 1 (by rfl) ⟨383156, by rfl⟩ : syracuseStep 510875 = 766313) B766313
theorem B510927 : Blo 507795 510927 := bstep (se 1 (by rfl) ⟨383195, by rfl⟩ : syracuseStep 510927 = 766391) B766391
theorem B510951 : Blo 507795 510951 := bstep (se 1 (by rfl) ⟨383213, by rfl⟩ : syracuseStep 510951 = 766427) B766427
theorem B2575475 : Blo 507795 2575475 := bstep (se 1 (by rfl) ⟨1931606, by rfl⟩ : syracuseStep 2575475 = 3863213) B3863213
theorem B5786801 : Blo 507795 5786801 := bstep (se 2 (by rfl) ⟨2170050, by rfl⟩ : syracuseStep 5786801 = 4340101) B4340101
theorem B1723679 : Blo 507795 1723679 := bstep (se 1 (by rfl) ⟨1292759, by rfl⟩ : syracuseStep 1723679 = 2585519) B2585519
theorem B511263 : Blo 507795 511263 := bstep (se 1 (by rfl) ⟨383447, by rfl⟩ : syracuseStep 511263 = 766895) B766895
theorem B511323 : Blo 507795 511323 := bstep (se 1 (by rfl) ⟨383492, by rfl⟩ : syracuseStep 511323 = 766985) B766985
theorem B511343 : Blo 507795 511343 := bstep (se 1 (by rfl) ⟨383507, by rfl⟩ : syracuseStep 511343 = 767015) B767015
theorem B511399 : Blo 507795 511399 := bstep (se 1 (by rfl) ⟨383549, by rfl⟩ : syracuseStep 511399 = 767099) B767099
theorem B14732725 : Blo 507795 14732725 := bstep (se 5 (by rfl) ⟨690596, by rfl⟩ : syracuseStep 14732725 = 1381193) B1381193
theorem B511483 : Blo 507795 511483 := bstep (se 1 (by rfl) ⟨383612, by rfl⟩ : syracuseStep 511483 = 767225) B767225
theorem B511551 : Blo 507795 511551 := bstep (se 1 (by rfl) ⟨383663, by rfl⟩ : syracuseStep 511551 = 767327) B767327
theorem B511559 : Blo 507795 511559 := bstep (se 1 (by rfl) ⟨383669, by rfl⟩ : syracuseStep 511559 = 767339) B767339
theorem B511711 : Blo 507795 511711 := bstep (se 1 (by rfl) ⟨383783, by rfl⟩ : syracuseStep 511711 = 767567) B767567
theorem B511791 : Blo 507795 511791 := bstep (se 1 (by rfl) ⟨383843, by rfl⟩ : syracuseStep 511791 = 767687) B767687
theorem B2576285 : Blo 507795 2576285 := bstep (se 3 (by rfl) ⟨483053, by rfl⟩ : syracuseStep 2576285 = 966107) B966107
theorem B8704259 : Blo 507795 8704259 := bstep (se 1 (by rfl) ⟨6528194, by rfl⟩ : syracuseStep 8704259 = 13056389) B13056389
theorem B971119 : Blo 507795 971119 := bstep (se 1 (by rfl) ⟨728339, by rfl⟩ : syracuseStep 971119 = 1456679) B1456679
theorem B10998341 : Blo 507795 10998341 := bstep (se 4 (by rfl) ⟨1031094, by rfl⟩ : syracuseStep 10998341 = 2062189) B2062189
theorem B2577095 : Blo 507795 2577095 := bstep (se 1 (by rfl) ⟨1932821, by rfl⟩ : syracuseStep 2577095 = 3865643) B3865643
theorem B545503 : Blo 507795 545503 := bstep (se 1 (by rfl) ⟨409127, by rfl⟩ : syracuseStep 545503 = 818255) B818255
theorem B13030145 : Blo 507795 13030145 := bstep (se 2 (by rfl) ⟨4886304, by rfl⟩ : syracuseStep 13030145 = 9772609) B9772609
theorem B1627283 : Blo 507795 1627283 := bstep (se 1 (by rfl) ⟨1220462, by rfl⟩ : syracuseStep 1627283 = 2440925) B2440925
theorem B611707 : Blo 507795 611707 := bstep (se 1 (by rfl) ⟨458780, by rfl⟩ : syracuseStep 611707 = 917561) B917561
theorem B22304165 : Blo 507795 22304165 := bstep (se 4 (by rfl) ⟨2091015, by rfl⟩ : syracuseStep 22304165 = 4182031) B4182031
theorem B1726109 : Blo 507795 1726109 := bstep (se 3 (by rfl) ⟨323645, by rfl⟩ : syracuseStep 1726109 = 647291) B647291
theorem B9787067 : Blo 507795 9787067 := bstep (se 1 (by rfl) ⟨7340300, by rfl⟩ : syracuseStep 9787067 = 14680601) B14680601
theorem B5592887 : Blo 507795 5592887 := bstep (se 1 (by rfl) ⟨4194665, by rfl⟩ : syracuseStep 5592887 = 8389331) B8389331
theorem B11327521 : Blo 507795 11327521 := bstep (se 2 (by rfl) ⟨4247820, by rfl⟩ : syracuseStep 11327521 = 8495641) B8495641
theorem B1726649 : Blo 507795 1726649 := bstep (se 2 (by rfl) ⟨647493, by rfl⟩ : syracuseStep 1726649 = 1294987) B1294987
theorem B2185481 : Blo 507795 2185481 := bstep (se 2 (by rfl) ⟨819555, by rfl⟩ : syracuseStep 2185481 = 1639111) B1639111
theorem B645499 : Blo 507795 645499 := bstep (se 1 (by rfl) ⟨484124, by rfl⟩ : syracuseStep 645499 = 968249) B968249
theorem B645727 : Blo 507795 645727 := bstep (se 1 (by rfl) ⟨484295, by rfl⟩ : syracuseStep 645727 = 968591) B968591
theorem B9394805 : Blo 507795 9394805 := bstep (se 5 (by rfl) ⟨440381, by rfl⟩ : syracuseStep 9394805 = 880763) B880763
theorem B2579165 : Blo 507795 2579165 := bstep (se 3 (by rfl) ⟨483593, by rfl⟩ : syracuseStep 2579165 = 967187) B967187
theorem B1793063 : Blo 507795 1793063 := bstep (se 1 (by rfl) ⟨1344797, by rfl⟩ : syracuseStep 1793063 = 2689595) B2689595
theorem B1399997 : Blo 507795 1399997 := bstep (se 3 (by rfl) ⟨262499, by rfl⟩ : syracuseStep 1399997 = 524999) B524999
theorem B613595 : Blo 507795 613595 := bstep (se 1 (by rfl) ⟨460196, by rfl⟩ : syracuseStep 613595 = 920393) B920393
theorem B2579849 : Blo 507795 2579849 := bstep (se 2 (by rfl) ⟨967443, by rfl⟩ : syracuseStep 2579849 = 1934887) B1934887
theorem B3661271 : Blo 507795 3661271 := bstep (se 1 (by rfl) ⟨2745953, by rfl⟩ : syracuseStep 3661271 = 5491907) B5491907
theorem B646967 : Blo 507795 646967 := bstep (se 1 (by rfl) ⟨485225, by rfl⟩ : syracuseStep 646967 = 970451) B970451
theorem B3497789 : Blo 507795 3497789 := bstep (se 3 (by rfl) ⟨655835, by rfl⟩ : syracuseStep 3497789 = 1311671) B1311671
theorem B647119 : Blo 507795 647119 := bstep (se 1 (by rfl) ⟨485339, by rfl⟩ : syracuseStep 647119 = 970679) B970679
theorem B2581145 : Blo 507795 2581145 := bstep (se 2 (by rfl) ⟨967929, by rfl⟩ : syracuseStep 2581145 = 1935859) B1935859
theorem B2482859 : Blo 507795 2482859 := bstep (se 1 (by rfl) ⟨1862144, by rfl⟩ : syracuseStep 2482859 = 3724289) B3724289
theorem B9332111 : Blo 507795 9332111 := bstep (se 1 (by rfl) ⟨6999083, by rfl⟩ : syracuseStep 9332111 = 13998167) B13998167
theorem B9791063 : Blo 507795 9791063 := bstep (se 1 (by rfl) ⟨7343297, by rfl⟩ : syracuseStep 9791063 = 14686595) B14686595
theorem B21227501 : Blo 507795 21227501 := bstep (se 3 (by rfl) ⟨3980156, by rfl⟩ : syracuseStep 21227501 = 7960313) B7960313
theorem B2582927 : Blo 507795 2582927 := bstep (se 1 (by rfl) ⟨1937195, by rfl⟩ : syracuseStep 2582927 = 3874391) B3874391
theorem B2321423 : Blo 507795 2321423 := bstep (se 1 (by rfl) ⟨1741067, by rfl⟩ : syracuseStep 2321423 = 3482135) B3482135
theorem B1830509 : Blo 507795 1830509 := bstep (se 3 (by rfl) ⟨343220, by rfl⟩ : syracuseStep 1830509 = 686441) B686441
theorem B39841469 : Blo 507795 39841469 := bstep (se 3 (by rfl) ⟨7470275, by rfl⟩ : syracuseStep 39841469 = 14940551) B14940551
theorem B1142585 : Blo 507795 1142585 := bstep (se 2 (by rfl) ⟨428469, by rfl⟩ : syracuseStep 1142585 = 856939) B856939
theorem B2453609 : Blo 507795 2453609 := bstep (se 2 (by rfl) ⟨920103, by rfl⟩ : syracuseStep 2453609 = 1840207) B1840207
theorem B1143215 : Blo 507795 1143215 := bstep (se 1 (by rfl) ⟨857411, by rfl⟩ : syracuseStep 1143215 = 1714823) B1714823
theorem B2585033 : Blo 507795 2585033 := bstep (se 2 (by rfl) ⟨969387, by rfl⟩ : syracuseStep 2585033 = 1938775) B1938775
theorem B1143251 : Blo 507795 1143251 := bstep (se 1 (by rfl) ⟨857438, by rfl⟩ : syracuseStep 1143251 = 1714877) B1714877
theorem B5829083 : Blo 507795 5829083 := bstep (se 1 (by rfl) ⟨4371812, by rfl⟩ : syracuseStep 5829083 = 8743625) B8743625
theorem B1143359 : Blo 507795 1143359 := bstep (se 1 (by rfl) ⟨857519, by rfl⟩ : syracuseStep 1143359 = 1715039) B1715039
theorem B2749049 : Blo 507795 2749049 := bstep (se 2 (by rfl) ⟨1030893, by rfl⟩ : syracuseStep 2749049 = 2061787) B2061787
theorem B1143467 : Blo 507795 1143467 := bstep (se 1 (by rfl) ⟨857600, by rfl⟩ : syracuseStep 1143467 = 1715201) B1715201
theorem B3863699 : Blo 507795 3863699 := bstep (se 1 (by rfl) ⟨2897774, by rfl⟩ : syracuseStep 3863699 = 5795549) B5795549
theorem B1144007 : Blo 507795 1144007 := bstep (se 1 (by rfl) ⟨858005, by rfl⟩ : syracuseStep 1144007 = 1716011) B1716011
theorem B2585843 : Blo 507795 2585843 := bstep (se 1 (by rfl) ⟨1939382, by rfl⟩ : syracuseStep 2585843 = 3878765) B3878765
theorem B2061607 : Blo 507795 2061607 := bstep (se 1 (by rfl) ⟨1546205, by rfl⟩ : syracuseStep 2061607 = 3092411) B3092411
theorem B1144187 : Blo 507795 1144187 := bstep (se 1 (by rfl) ⟨858140, by rfl⟩ : syracuseStep 1144187 = 1716281) B1716281
theorem B3274145 : Blo 507795 3274145 := bstep (se 2 (by rfl) ⟨1227804, by rfl⟩ : syracuseStep 3274145 = 2455609) B2455609
theorem B816583 : Blo 507795 816583 := bstep (se 1 (by rfl) ⟨612437, by rfl⟩ : syracuseStep 816583 = 1224875) B1224875
theorem B1144313 : Blo 507795 1144313 := bstep (se 2 (by rfl) ⟨429117, by rfl⟩ : syracuseStep 1144313 = 858235) B858235
theorem B1144403 : Blo 507795 1144403 := bstep (se 1 (by rfl) ⟨858302, by rfl⟩ : syracuseStep 1144403 = 1716605) B1716605
theorem B1635997 : Blo 507795 1635997 := bstep (se 3 (by rfl) ⟨306749, by rfl⟩ : syracuseStep 1635997 = 613499) B613499
theorem B1144583 : Blo 507795 1144583 := bstep (se 1 (by rfl) ⟨858437, by rfl⟩ : syracuseStep 1144583 = 1716875) B1716875
theorem B1145195 : Blo 507795 1145195 := bstep (se 1 (by rfl) ⟨858896, by rfl⟩ : syracuseStep 1145195 = 1717793) B1717793
theorem B1145339 : Blo 507795 1145339 := bstep (se 1 (by rfl) ⟨859004, by rfl⟩ : syracuseStep 1145339 = 1718009) B1718009
theorem B1145465 : Blo 507795 1145465 := bstep (se 2 (by rfl) ⟨429549, by rfl⟩ : syracuseStep 1145465 = 859099) B859099
theorem B1145519 : Blo 507795 1145519 := bstep (se 1 (by rfl) ⟨859139, by rfl⟩ : syracuseStep 1145519 = 1718279) B1718279
theorem B1931971 : Blo 507795 1931971 := bstep (se 1 (by rfl) ⟨1448978, by rfl⟩ : syracuseStep 1931971 = 2897957) B2897957
theorem B1145591 : Blo 507795 1145591 := bstep (se 1 (by rfl) ⟨859193, by rfl⟩ : syracuseStep 1145591 = 1718387) B1718387
theorem B1145771 : Blo 507795 1145771 := bstep (se 1 (by rfl) ⟨859328, by rfl⟩ : syracuseStep 1145771 = 1718657) B1718657
theorem B1932275 : Blo 507795 1932275 := bstep (se 1 (by rfl) ⟨1449206, by rfl⟩ : syracuseStep 1932275 = 2898413) B2898413
theorem B916471 : Blo 507795 916471 := bstep (se 1 (by rfl) ⟨687353, by rfl⟩ : syracuseStep 916471 = 1374707) B1374707
theorem B2587787 : Blo 507795 2587787 := bstep (se 1 (by rfl) ⟨1940840, by rfl⟩ : syracuseStep 2587787 = 3881681) B3881681
theorem B4652185 : Blo 507795 4652185 := bstep (se 2 (by rfl) ⟨1744569, by rfl⟩ : syracuseStep 4652185 = 3489139) B3489139
theorem B1768735 : Blo 507795 1768735 := bstep (se 1 (by rfl) ⟨1326551, by rfl⟩ : syracuseStep 1768735 = 2653103) B2653103
theorem B916775 : Blo 507795 916775 := bstep (se 1 (by rfl) ⟨687581, by rfl⟩ : syracuseStep 916775 = 1375163) B1375163
theorem B687451 : Blo 507795 687451 := bstep (se 1 (by rfl) ⟨515588, by rfl⟩ : syracuseStep 687451 = 1031177) B1031177
theorem B2489737 : Blo 507795 2489737 := bstep (se 2 (by rfl) ⟨933651, by rfl⟩ : syracuseStep 2489737 = 1867303) B1867303
theorem B1932731 : Blo 507795 1932731 := bstep (se 1 (by rfl) ⟨1449548, by rfl⟩ : syracuseStep 1932731 = 2899097) B2899097
theorem B1146311 : Blo 507795 1146311 := bstep (se 1 (by rfl) ⟨859733, by rfl⟩ : syracuseStep 1146311 = 1719467) B1719467
theorem B3276247 : Blo 507795 3276247 := bstep (se 1 (by rfl) ⟨2457185, by rfl⟩ : syracuseStep 3276247 = 4914371) B4914371
theorem B1146671 : Blo 507795 1146671 := bstep (se 1 (by rfl) ⟨860003, by rfl⟩ : syracuseStep 1146671 = 1720007) B1720007
theorem B3276605 : Blo 507795 3276605 := bstep (se 3 (by rfl) ⟨614363, by rfl⟩ : syracuseStep 3276605 = 1228727) B1228727
theorem B1245223 : Blo 507795 1245223 := bstep (se 1 (by rfl) ⟨933917, by rfl⟩ : syracuseStep 1245223 = 1867835) B1867835
theorem B10485811 : Blo 507795 10485811 := bstep (se 1 (by rfl) ⟨7864358, by rfl⟩ : syracuseStep 10485811 = 15728717) B15728717
theorem B2326607 : Blo 507795 2326607 := bstep (se 1 (by rfl) ⟨1744955, by rfl⟩ : syracuseStep 2326607 = 3489911) B3489911
theorem B4129049 : Blo 507795 4129049 := bstep (se 2 (by rfl) ⟨1548393, by rfl⟩ : syracuseStep 4129049 = 3096787) B3096787
theorem B3146539 : Blo 507795 3146539 := bstep (se 1 (by rfl) ⟨2359904, by rfl⟩ : syracuseStep 3146539 = 4719809) B4719809
theorem B1639225 : Blo 507795 1639225 := bstep (se 2 (by rfl) ⟨614709, by rfl⟩ : syracuseStep 1639225 = 1229419) B1229419
theorem B1147859 : Blo 507795 1147859 := bstep (se 1 (by rfl) ⟨860894, by rfl⟩ : syracuseStep 1147859 = 1721789) B1721789
theorem B1639379 : Blo 507795 1639379 := bstep (se 1 (by rfl) ⟨1229534, by rfl⟩ : syracuseStep 1639379 = 2459069) B2459069
theorem B1148111 : Blo 507795 1148111 := bstep (se 1 (by rfl) ⟨861083, by rfl⟩ : syracuseStep 1148111 = 1722167) B1722167
theorem B1148435 : Blo 507795 1148435 := bstep (se 1 (by rfl) ⟨861326, by rfl⟩ : syracuseStep 1148435 = 1722653) B1722653
theorem B2360927 : Blo 507795 2360927 := bstep (se 1 (by rfl) ⟨1770695, by rfl⟩ : syracuseStep 2360927 = 3541391) B3541391
theorem B2066081 : Blo 507795 2066081 := bstep (se 2 (by rfl) ⟨774780, by rfl⟩ : syracuseStep 2066081 = 1549561) B1549561
theorem B1378015 : Blo 507795 1378015 := bstep (se 1 (by rfl) ⟨1033511, by rfl⟩ : syracuseStep 1378015 = 2067023) B2067023
theorem B6620957 : Blo 507795 6620957 := bstep (se 3 (by rfl) ⟨1241429, by rfl⟩ : syracuseStep 6620957 = 2482859) B2482859
theorem B1149119 : Blo 507795 1149119 := bstep (se 1 (by rfl) ⟨861839, by rfl⟩ : syracuseStep 1149119 = 1723679) B1723679
theorem B723487 : Blo 507795 723487 := bstep (se 1 (by rfl) ⟨542615, by rfl⟩ : syracuseStep 723487 = 1085231) B1085231
theorem B4917833 : Blo 507795 4917833 := bstep (se 2 (by rfl) ⟨1844187, by rfl⟩ : syracuseStep 4917833 = 3688375) B3688375
theorem B5802839 : Blo 507795 5802839 := bstep (se 1 (by rfl) ⟨4352129, by rfl⟩ : syracuseStep 5802839 = 8704259) B8704259
theorem B1674361 : Blo 507795 1674361 := bstep (se 2 (by rfl) ⟨627885, by rfl⟩ : syracuseStep 1674361 = 1255771) B1255771
theorem B1150073 : Blo 507795 1150073 := bstep (se 2 (by rfl) ⟨431277, by rfl⟩ : syracuseStep 1150073 = 862555) B862555
theorem B8686763 : Blo 507795 8686763 := bstep (se 1 (by rfl) ⟨6515072, by rfl⟩ : syracuseStep 8686763 = 13030145) B13030145
theorem B1379551 : Blo 507795 1379551 := bstep (se 1 (by rfl) ⟨1034663, by rfl⟩ : syracuseStep 1379551 = 2069327) B2069327
theorem B724393 : Blo 507795 724393 := bstep (se 2 (by rfl) ⟨271647, by rfl⟩ : syracuseStep 724393 = 543295) B543295
theorem B1084855 : Blo 507795 1084855 := bstep (se 1 (by rfl) ⟨813641, by rfl⟩ : syracuseStep 1084855 = 1627283) B1627283
theorem B1379767 : Blo 507795 1379767 := bstep (se 1 (by rfl) ⟨1034825, by rfl⟩ : syracuseStep 1379767 = 2069651) B2069651
theorem B59477773 : Blo 507795 59477773 := bstep (se 3 (by rfl) ⟨11152082, by rfl⟩ : syracuseStep 59477773 = 22304165) B22304165
theorem B1150739 : Blo 507795 1150739 := bstep (se 1 (by rfl) ⟨863054, by rfl⟩ : syracuseStep 1150739 = 1726109) B1726109
theorem B6524711 : Blo 507795 6524711 := bstep (se 1 (by rfl) ⟨4893533, by rfl⟩ : syracuseStep 6524711 = 9787067) B9787067
theorem B3870503 : Blo 507795 3870503 := bstep (se 1 (by rfl) ⟨2902877, by rfl⟩ : syracuseStep 3870503 = 5805755) B5805755
theorem B2330473 : Blo 507795 2330473 := bstep (se 2 (by rfl) ⟨873927, by rfl⟩ : syracuseStep 2330473 = 1747855) B1747855
theorem B1151099 : Blo 507795 1151099 := bstep (se 1 (by rfl) ⟨863324, by rfl⟩ : syracuseStep 1151099 = 1726649) B1726649
theorem B1151369 : Blo 507795 1151369 := bstep (se 2 (by rfl) ⟨431763, by rfl⟩ : syracuseStep 1151369 = 863527) B863527
theorem B6263203 : Blo 507795 6263203 := bstep (se 1 (by rfl) ⟨4697402, by rfl⟩ : syracuseStep 6263203 = 9394805) B9394805
theorem B2757199 : Blo 507795 2757199 := bstep (se 1 (by rfl) ⟨2067899, by rfl⟩ : syracuseStep 2757199 = 4135799) B4135799
theorem B1380959 : Blo 507795 1380959 := bstep (se 1 (by rfl) ⟨1035719, by rfl⟩ : syracuseStep 1380959 = 2071439) B2071439
theorem B14291639 : Blo 507795 14291639 := bstep (se 1 (by rfl) ⟨10718729, by rfl⟩ : syracuseStep 14291639 = 21437459) B21437459
theorem B1446781 : Blo 507795 1446781 := bstep (se 3 (by rfl) ⟨271271, by rfl⟩ : syracuseStep 1446781 = 542543) B542543
theorem B726079 : Blo 507795 726079 := bstep (se 1 (by rfl) ⟨544559, by rfl⟩ : syracuseStep 726079 = 1089119) B1089119
theorem B857263 : Blo 507795 857263 := bstep (se 1 (by rfl) ⟨642947, by rfl⟩ : syracuseStep 857263 = 1285895) B1285895
theorem B3151057 : Blo 507795 3151057 := bstep (se 2 (by rfl) ⟨1181646, by rfl⟩ : syracuseStep 3151057 = 2363293) B2363293
theorem B1840583 : Blo 507795 1840583 := bstep (se 1 (by rfl) ⟨1380437, by rfl⟩ : syracuseStep 1840583 = 2760875) B2760875
theorem B1382059 : Blo 507795 1382059 := bstep (se 1 (by rfl) ⟨1036544, by rfl⟩ : syracuseStep 1382059 = 2073089) B2073089
theorem B857783 : Blo 507795 857783 := bstep (se 1 (by rfl) ⟨643337, by rfl⟩ : syracuseStep 857783 = 1286675) B1286675
theorem B726779 : Blo 507795 726779 := bstep (se 1 (by rfl) ⟨545084, by rfl⟩ : syracuseStep 726779 = 1090169) B1090169
theorem B3151673 : Blo 507795 3151673 := bstep (se 2 (by rfl) ⟨1181877, by rfl⟩ : syracuseStep 3151673 = 2363755) B2363755
theorem B727337 : Blo 507795 727337 := bstep (se 2 (by rfl) ⟨272751, by rfl⟩ : syracuseStep 727337 = 545503) B545503
theorem B6527375 : Blo 507795 6527375 := bstep (se 1 (by rfl) ⟨4895531, by rfl⟩ : syracuseStep 6527375 = 9791063) B9791063
theorem B858971 : Blo 507795 858971 := bstep (se 1 (by rfl) ⟨644228, by rfl⟩ : syracuseStep 858971 = 1288457) B1288457
theorem B859207 : Blo 507795 859207 := bstep (se 1 (by rfl) ⟨644405, by rfl⟩ : syracuseStep 859207 = 1288811) B1288811
theorem B1088777 : Blo 507795 1088777 := bstep (se 2 (by rfl) ⟨408291, by rfl⟩ : syracuseStep 1088777 = 816583) B816583
theorem B1547615 : Blo 507795 1547615 := bstep (se 1 (by rfl) ⟨1160711, by rfl⟩ : syracuseStep 1547615 = 2321423) B2321423
theorem B2170223 : Blo 507795 2170223 := bstep (se 1 (by rfl) ⟨1627667, by rfl⟩ : syracuseStep 2170223 = 3255335) B3255335
theorem B859639 : Blo 507795 859639 := bstep (se 1 (by rfl) ⟨644729, by rfl⟩ : syracuseStep 859639 = 1289459) B1289459
theorem B1449697 : Blo 507795 1449697 := bstep (se 2 (by rfl) ⟨543636, by rfl⟩ : syracuseStep 1449697 = 1087273) B1087273
theorem B1285865 : Blo 507795 1285865 := bstep (se 2 (by rfl) ⟨482199, by rfl⟩ : syracuseStep 1285865 = 964399) B964399
theorem B1220339 : Blo 507795 1220339 := bstep (se 1 (by rfl) ⟨915254, by rfl⟩ : syracuseStep 1220339 = 1830509) B1830509
theorem B859943 : Blo 507795 859943 := bstep (se 1 (by rfl) ⟨644957, by rfl⟩ : syracuseStep 859943 = 1289915) B1289915
theorem B761723 : Blo 507795 761723 := bstep (se 1 (by rfl) ⟨571292, by rfl⟩ : syracuseStep 761723 = 1142585) B1142585
theorem B762143 : Blo 507795 762143 := bstep (se 1 (by rfl) ⟨571607, by rfl⟩ : syracuseStep 762143 = 1143215) B1143215
theorem B762167 : Blo 507795 762167 := bstep (se 1 (by rfl) ⟨571625, by rfl⟩ : syracuseStep 762167 = 1143251) B1143251
theorem B1843553 : Blo 507795 1843553 := bstep (se 2 (by rfl) ⟨691332, by rfl⟩ : syracuseStep 1843553 = 1382665) B1382665
theorem B762239 : Blo 507795 762239 := bstep (se 1 (by rfl) ⟨571679, by rfl⟩ : syracuseStep 762239 = 1143359) B1143359
theorem B762311 : Blo 507795 762311 := bstep (se 1 (by rfl) ⟨571733, by rfl⟩ : syracuseStep 762311 = 1143467) B1143467
theorem B860665 : Blo 507795 860665 := bstep (se 2 (by rfl) ⟨322749, by rfl⟩ : syracuseStep 860665 = 645499) B645499
theorem B2892307 : Blo 507795 2892307 := bstep (se 1 (by rfl) ⟨2169230, by rfl⟩ : syracuseStep 2892307 = 4338461) B4338461
theorem B860935 : Blo 507795 860935 := bstep (se 1 (by rfl) ⟨645701, by rfl⟩ : syracuseStep 860935 = 1291403) B1291403
theorem B762665 : Blo 507795 762665 := bstep (se 2 (by rfl) ⟨285999, by rfl⟩ : syracuseStep 762665 = 571999) B571999
theorem B860969 : Blo 507795 860969 := bstep (se 2 (by rfl) ⟨322863, by rfl⟩ : syracuseStep 860969 = 645727) B645727
theorem B762671 : Blo 507795 762671 := bstep (se 1 (by rfl) ⟨572003, by rfl⟩ : syracuseStep 762671 = 1144007) B1144007
theorem B762791 : Blo 507795 762791 := bstep (se 1 (by rfl) ⟨572093, by rfl⟩ : syracuseStep 762791 = 1144187) B1144187
theorem B762875 : Blo 507795 762875 := bstep (se 1 (by rfl) ⟨572156, by rfl⟩ : syracuseStep 762875 = 1144313) B1144313
theorem B762935 : Blo 507795 762935 := bstep (se 1 (by rfl) ⟨572201, by rfl⟩ : syracuseStep 762935 = 1144403) B1144403
theorem B861239 : Blo 507795 861239 := bstep (se 1 (by rfl) ⟨645929, by rfl⟩ : syracuseStep 861239 = 1291859) B1291859
theorem B763055 : Blo 507795 763055 := bstep (se 1 (by rfl) ⟨572291, by rfl⟩ : syracuseStep 763055 = 1144583) B1144583
theorem B4662479 : Blo 507795 4662479 := bstep (se 1 (by rfl) ⟨3496859, by rfl⟩ : syracuseStep 4662479 = 6993719) B6993719
theorem B1221961 : Blo 507795 1221961 := bstep (se 2 (by rfl) ⟨458235, by rfl⟩ : syracuseStep 1221961 = 916471) B916471
theorem B1451371 : Blo 507795 1451371 := bstep (se 1 (by rfl) ⟨1088528, by rfl⟩ : syracuseStep 1451371 = 2177057) B2177057
theorem B6202913 : Blo 507795 6202913 := bstep (se 2 (by rfl) ⟨2326092, by rfl⟩ : syracuseStep 6202913 = 4652185) B4652185
theorem B763463 : Blo 507795 763463 := bstep (se 1 (by rfl) ⟨572597, by rfl⟩ : syracuseStep 763463 = 1145195) B1145195
theorem B16557709 : Blo 507795 16557709 := bstep (se 3 (by rfl) ⟨3104570, by rfl⟩ : syracuseStep 16557709 = 6209141) B6209141
theorem B763559 : Blo 507795 763559 := bstep (se 1 (by rfl) ⟨572669, by rfl⟩ : syracuseStep 763559 = 1145339) B1145339
theorem B13903579 : Blo 507795 13903579 := bstep (se 1 (by rfl) ⟨10427684, by rfl⟩ : syracuseStep 13903579 = 20855369) B20855369
theorem B763643 : Blo 507795 763643 := bstep (se 1 (by rfl) ⟨572732, by rfl⟩ : syracuseStep 763643 = 1145465) B1145465
theorem B763679 : Blo 507795 763679 := bstep (se 1 (by rfl) ⟨572759, by rfl⟩ : syracuseStep 763679 = 1145519) B1145519
theorem B862015 : Blo 507795 862015 := bstep (se 1 (by rfl) ⟨646511, by rfl⟩ : syracuseStep 862015 = 1293023) B1293023
theorem B763727 : Blo 507795 763727 := bstep (se 1 (by rfl) ⟨572795, by rfl⟩ : syracuseStep 763727 = 1145591) B1145591
theorem B3319649 : Blo 507795 3319649 := bstep (se 2 (by rfl) ⟨1244868, by rfl⟩ : syracuseStep 3319649 = 2489737) B2489737
theorem B763847 : Blo 507795 763847 := bstep (se 1 (by rfl) ⟨572885, by rfl⟩ : syracuseStep 763847 = 1145771) B1145771
theorem B1714121 : Blo 507795 1714121 := bstep (se 2 (by rfl) ⟨642795, by rfl⟩ : syracuseStep 1714121 = 1285591) B1285591
theorem B4368329 : Blo 507795 4368329 := bstep (se 2 (by rfl) ⟨1638123, by rfl⟩ : syracuseStep 4368329 = 3276247) B3276247
theorem B1288183 : Blo 507795 1288183 := bstep (se 1 (by rfl) ⟨966137, by rfl⟩ : syracuseStep 1288183 = 1932275) B1932275
theorem B1714391 : Blo 507795 1714391 := bstep (se 1 (by rfl) ⟨1285793, by rfl⟩ : syracuseStep 1714391 = 2571587) B2571587
theorem B2894039 : Blo 507795 2894039 := bstep (se 1 (by rfl) ⟨2170529, by rfl⟩ : syracuseStep 2894039 = 4341059) B4341059
theorem B1288487 : Blo 507795 1288487 := bstep (se 1 (by rfl) ⟨966365, by rfl⟩ : syracuseStep 1288487 = 1932731) B1932731
theorem B764201 : Blo 507795 764201 := bstep (se 2 (by rfl) ⟨286575, by rfl⟩ : syracuseStep 764201 = 573151) B573151
theorem B764207 : Blo 507795 764207 := bstep (se 1 (by rfl) ⟨573155, by rfl⟩ : syracuseStep 764207 = 1146311) B1146311
theorem B5220865 : Blo 507795 5220865 := bstep (se 2 (by rfl) ⟨1957824, by rfl⟩ : syracuseStep 5220865 = 3915649) B3915649
theorem B1714715 : Blo 507795 1714715 := bstep (se 1 (by rfl) ⟨1286036, by rfl⟩ : syracuseStep 1714715 = 2572073) B2572073
theorem B764447 : Blo 507795 764447 := bstep (se 1 (by rfl) ⟨573335, by rfl⟩ : syracuseStep 764447 = 1146671) B1146671
theorem B862751 : Blo 507795 862751 := bstep (se 1 (by rfl) ⟨647063, by rfl⟩ : syracuseStep 862751 = 1294127) B1294127
theorem B862825 : Blo 507795 862825 := bstep (se 2 (by rfl) ⟨323559, by rfl⟩ : syracuseStep 862825 = 647119) B647119
theorem B4369079 : Blo 507795 4369079 := bstep (se 1 (by rfl) ⟨3276809, by rfl⟩ : syracuseStep 4369079 = 6553619) B6553619
theorem B764831 : Blo 507795 764831 := bstep (se 1 (by rfl) ⟨573623, by rfl⟩ : syracuseStep 764831 = 1147247) B1147247
theorem B764879 : Blo 507795 764879 := bstep (se 1 (by rfl) ⟨573659, by rfl⟩ : syracuseStep 764879 = 1147319) B1147319
theorem B863183 : Blo 507795 863183 := bstep (se 1 (by rfl) ⟨647387, by rfl⟩ : syracuseStep 863183 = 1294775) B1294775
theorem B764969 : Blo 507795 764969 := bstep (se 2 (by rfl) ⟨286863, by rfl⟩ : syracuseStep 764969 = 573727) B573727
theorem B2173999 : Blo 507795 2173999 := bstep (se 1 (by rfl) ⟨1630499, by rfl⟩ : syracuseStep 2173999 = 3260999) B3260999
theorem B764975 : Blo 507795 764975 := bstep (se 1 (by rfl) ⟨573731, by rfl⟩ : syracuseStep 764975 = 1147463) B1147463
theorem B1453103 : Blo 507795 1453103 := bstep (se 1 (by rfl) ⟨1089827, by rfl⟩ : syracuseStep 1453103 = 2179655) B2179655
theorem B764999 : Blo 507795 764999 := bstep (se 1 (by rfl) ⟨573749, by rfl⟩ : syracuseStep 764999 = 1147499) B1147499
theorem B765263 : Blo 507795 765263 := bstep (se 1 (by rfl) ⟨573947, by rfl⟩ : syracuseStep 765263 = 1147895) B1147895
theorem B1715579 : Blo 507795 1715579 := bstep (se 1 (by rfl) ⟨1286684, by rfl⟩ : syracuseStep 1715579 = 2573369) B2573369
theorem B1289641 : Blo 507795 1289641 := bstep (se 2 (by rfl) ⟨483615, by rfl⟩ : syracuseStep 1289641 = 967231) B967231
theorem B765353 : Blo 507795 765353 := bstep (se 2 (by rfl) ⟨287007, by rfl⟩ : syracuseStep 765353 = 574015) B574015
theorem B765503 : Blo 507795 765503 := bstep (se 1 (by rfl) ⟨574127, by rfl⟩ : syracuseStep 765503 = 1148255) B1148255
theorem B9940553 : Blo 507795 9940553 := bstep (se 2 (by rfl) ⟨3727707, by rfl⟩ : syracuseStep 9940553 = 7455415) B7455415
theorem B765767 : Blo 507795 765767 := bstep (se 1 (by rfl) ⟨574325, by rfl⟩ : syracuseStep 765767 = 1148651) B1148651
theorem B1453945 : Blo 507795 1453945 := bstep (se 2 (by rfl) ⟨545229, by rfl⟩ : syracuseStep 1453945 = 1090459) B1090459
theorem B1290127 : Blo 507795 1290127 := bstep (se 1 (by rfl) ⟨967595, by rfl⟩ : syracuseStep 1290127 = 1935191) B1935191
theorem B765851 : Blo 507795 765851 := bstep (se 1 (by rfl) ⟨574388, by rfl⟩ : syracuseStep 765851 = 1148777) B1148777
theorem B3256307 : Blo 507795 3256307 := bstep (se 1 (by rfl) ⟨2442230, by rfl⟩ : syracuseStep 3256307 = 4884461) B4884461
theorem B1224827 : Blo 507795 1224827 := bstep (se 1 (by rfl) ⟨918620, by rfl⟩ : syracuseStep 1224827 = 1837241) B1837241
theorem B1454345 : Blo 507795 1454345 := bstep (se 2 (by rfl) ⟨545379, by rfl⟩ : syracuseStep 1454345 = 1090759) B1090759
theorem B766415 : Blo 507795 766415 := bstep (se 1 (by rfl) ⟨574811, by rfl⟩ : syracuseStep 766415 = 1149623) B1149623
theorem B4895225 : Blo 507795 4895225 := bstep (se 2 (by rfl) ⟨1835709, by rfl⟩ : syracuseStep 4895225 = 3671419) B3671419
theorem B766457 : Blo 507795 766457 := bstep (se 2 (by rfl) ⟨287421, by rfl⟩ : syracuseStep 766457 = 574843) B574843
theorem B766559 : Blo 507795 766559 := bstep (se 1 (by rfl) ⟨574919, by rfl⟩ : syracuseStep 766559 = 1149839) B1149839
theorem B1716983 : Blo 507795 1716983 := bstep (se 1 (by rfl) ⟨1287737, by rfl⟩ : syracuseStep 1716983 = 2575475) B2575475
theorem B2798327 : Blo 507795 2798327 := bstep (se 1 (by rfl) ⟨2098745, by rfl⟩ : syracuseStep 2798327 = 4197491) B4197491
theorem B1291049 : Blo 507795 1291049 := bstep (se 2 (by rfl) ⟨484143, by rfl⟩ : syracuseStep 1291049 = 968287) B968287
theorem B767039 : Blo 507795 767039 := bstep (se 1 (by rfl) ⟨575279, by rfl⟩ : syracuseStep 767039 = 1150559) B1150559
theorem B767081 : Blo 507795 767081 := bstep (se 2 (by rfl) ⟨287655, by rfl⟩ : syracuseStep 767081 = 575311) B575311
theorem B767183 : Blo 507795 767183 := bstep (se 1 (by rfl) ⟨575387, by rfl⟩ : syracuseStep 767183 = 1150775) B1150775
theorem B1717523 : Blo 507795 1717523 := bstep (se 1 (by rfl) ⟨1288142, by rfl⟩ : syracuseStep 1717523 = 2576285) B2576285
theorem B767387 : Blo 507795 767387 := bstep (se 1 (by rfl) ⟨575540, by rfl⟩ : syracuseStep 767387 = 1151081) B1151081
theorem B4372055 : Blo 507795 4372055 := bstep (se 1 (by rfl) ⟨3279041, by rfl⟩ : syracuseStep 4372055 = 6558083) B6558083
theorem B767609 : Blo 507795 767609 := bstep (se 2 (by rfl) ⟨287853, by rfl⟩ : syracuseStep 767609 = 575707) B575707
theorem B1718063 : Blo 507795 1718063 := bstep (se 1 (by rfl) ⟨1288547, by rfl⟩ : syracuseStep 1718063 = 2577095) B2577095
theorem B964703 : Blo 507795 964703 := bstep (se 1 (by rfl) ⟨723527, by rfl⟩ : syracuseStep 964703 = 1447055) B1447055
theorem B3258539 : Blo 507795 3258539 := bstep (se 1 (by rfl) ⟨2443904, by rfl⟩ : syracuseStep 3258539 = 4887809) B4887809
theorem B572251 : Blo 507795 572251 := bstep (se 1 (by rfl) ⟨429188, by rfl⟩ : syracuseStep 572251 = 858377) B858377
theorem B1456987 : Blo 507795 1456987 := bstep (se 1 (by rfl) ⟨1092740, by rfl⟩ : syracuseStep 1456987 = 2185481) B2185481
theorem B1719443 : Blo 507795 1719443 := bstep (se 1 (by rfl) ⟨1289582, by rfl⟩ : syracuseStep 1719443 = 2579165) B2579165
theorem B19643633 : Blo 507795 19643633 := bstep (se 2 (by rfl) ⟨7366362, by rfl⟩ : syracuseStep 19643633 = 14732725) B14732725
theorem B933331 : Blo 507795 933331 := bstep (se 1 (by rfl) ⟨699998, by rfl⟩ : syracuseStep 933331 = 1399997) B1399997
theorem B1719899 : Blo 507795 1719899 := bstep (se 1 (by rfl) ⟨1289924, by rfl⟩ : syracuseStep 1719899 = 2579849) B2579849
theorem B2440847 : Blo 507795 2440847 := bstep (se 1 (by rfl) ⟨1830635, by rfl⟩ : syracuseStep 2440847 = 3661271) B3661271
theorem B573223 : Blo 507795 573223 := bstep (se 1 (by rfl) ⟨429917, by rfl⟩ : syracuseStep 573223 = 859835) B859835
theorem B1556279 : Blo 507795 1556279 := bstep (se 1 (by rfl) ⟨1167209, by rfl⟩ : syracuseStep 1556279 = 2334419) B2334419
theorem B507871 : Blo 507795 507871 := bstep (se 1 (by rfl) ⟨380903, by rfl⟩ : syracuseStep 507871 = 761807) B761807
theorem B508135 : Blo 507795 508135 := bstep (se 1 (by rfl) ⟨381101, by rfl⟩ : syracuseStep 508135 = 762203) B762203
theorem B1720601 : Blo 507795 1720601 := bstep (se 2 (by rfl) ⟨645225, by rfl⟩ : syracuseStep 1720601 = 1290451) B1290451
theorem B508287 : Blo 507795 508287 := bstep (se 1 (by rfl) ⟨381215, by rfl⟩ : syracuseStep 508287 = 762431) B762431
theorem B1720763 : Blo 507795 1720763 := bstep (se 1 (by rfl) ⟨1290572, by rfl⟩ : syracuseStep 1720763 = 2581145) B2581145
theorem B508367 : Blo 507795 508367 := bstep (se 1 (by rfl) ⟨381275, by rfl⟩ : syracuseStep 508367 = 762551) B762551
theorem B1294825 : Blo 507795 1294825 := bstep (se 2 (by rfl) ⟨485559, by rfl⟩ : syracuseStep 1294825 = 971119) B971119
theorem B508519 : Blo 507795 508519 := bstep (se 1 (by rfl) ⟨381389, by rfl⟩ : syracuseStep 508519 = 762779) B762779
theorem B508783 : Blo 507795 508783 := bstep (se 1 (by rfl) ⟨381587, by rfl⟩ : syracuseStep 508783 = 763175) B763175
theorem B967535 : Blo 507795 967535 := bstep (se 1 (by rfl) ⟨725651, by rfl⟩ : syracuseStep 967535 = 1451303) B1451303
theorem B508839 : Blo 507795 508839 := bstep (se 1 (by rfl) ⟨381629, by rfl⟩ : syracuseStep 508839 = 763259) B763259
theorem B574375 : Blo 507795 574375 := bstep (se 1 (by rfl) ⟨430781, by rfl⟩ : syracuseStep 574375 = 861563) B861563
theorem B508923 : Blo 507795 508923 := bstep (se 1 (by rfl) ⟨381692, by rfl⟩ : syracuseStep 508923 = 763385) B763385
theorem B508991 : Blo 507795 508991 := bstep (se 1 (by rfl) ⟨381743, by rfl⟩ : syracuseStep 508991 = 763487) B763487
theorem B509135 : Blo 507795 509135 := bstep (se 1 (by rfl) ⟨381851, by rfl⟩ : syracuseStep 509135 = 763703) B763703
theorem B509339 : Blo 507795 509339 := bstep (se 1 (by rfl) ⟨382004, by rfl⟩ : syracuseStep 509339 = 764009) B764009
theorem B1033643 : Blo 507795 1033643 := bstep (se 1 (by rfl) ⟨775232, by rfl⟩ : syracuseStep 1033643 = 1550465) B1550465
theorem B1721951 : Blo 507795 1721951 := bstep (se 1 (by rfl) ⟨1291463, by rfl⟩ : syracuseStep 1721951 = 2582927) B2582927
theorem B509551 : Blo 507795 509551 := bstep (se 1 (by rfl) ⟨382163, by rfl⟩ : syracuseStep 509551 = 764327) B764327
theorem B12371575 : Blo 507795 12371575 := bstep (se 1 (by rfl) ⟨9278681, by rfl⟩ : syracuseStep 12371575 = 18557363) B18557363
theorem B509607 : Blo 507795 509607 := bstep (se 1 (by rfl) ⟨382205, by rfl⟩ : syracuseStep 509607 = 764411) B764411
theorem B509691 : Blo 507795 509691 := bstep (se 1 (by rfl) ⟨382268, by rfl⟩ : syracuseStep 509691 = 764537) B764537
theorem B509727 : Blo 507795 509727 := bstep (se 1 (by rfl) ⟨382295, by rfl⟩ : syracuseStep 509727 = 764591) B764591
theorem B509759 : Blo 507795 509759 := bstep (se 1 (by rfl) ⟨382319, by rfl⟩ : syracuseStep 509759 = 764639) B764639
theorem B509935 : Blo 507795 509935 := bstep (se 1 (by rfl) ⟨382451, by rfl⟩ : syracuseStep 509935 = 764903) B764903
theorem B7358525 : Blo 507795 7358525 := bstep (se 3 (by rfl) ⟨1379723, by rfl⟩ : syracuseStep 7358525 = 2759447) B2759447
theorem B510107 : Blo 507795 510107 := bstep (se 1 (by rfl) ⟨382580, by rfl⟩ : syracuseStep 510107 = 765161) B765161
theorem B510143 : Blo 507795 510143 := bstep (se 1 (by rfl) ⟨382607, by rfl⟩ : syracuseStep 510143 = 765215) B765215
theorem B2181329 : Blo 507795 2181329 := bstep (se 2 (by rfl) ⟨817998, by rfl⟩ : syracuseStep 2181329 = 1635997) B1635997
theorem B510255 : Blo 507795 510255 := bstep (se 1 (by rfl) ⟨382691, by rfl⟩ : syracuseStep 510255 = 765383) B765383
theorem B26560979 : Blo 507795 26560979 := bstep (se 1 (by rfl) ⟨19920734, by rfl⟩ : syracuseStep 26560979 = 39841469) B39841469
theorem B510491 : Blo 507795 510491 := bstep (se 1 (by rfl) ⟨382868, by rfl⟩ : syracuseStep 510491 = 765737) B765737
theorem B510495 : Blo 507795 510495 := bstep (se 1 (by rfl) ⟨382871, by rfl⟩ : syracuseStep 510495 = 765743) B765743
theorem B969403 : Blo 507795 969403 := bstep (se 1 (by rfl) ⟨727052, by rfl⟩ : syracuseStep 969403 = 1454105) B1454105
theorem B510811 : Blo 507795 510811 := bstep (se 1 (by rfl) ⟨383108, by rfl⟩ : syracuseStep 510811 = 766217) B766217
theorem B510879 : Blo 507795 510879 := bstep (se 1 (by rfl) ⟨383159, by rfl⟩ : syracuseStep 510879 = 766319) B766319
theorem B1723355 : Blo 507795 1723355 := bstep (se 1 (by rfl) ⟨1292516, by rfl⟩ : syracuseStep 1723355 = 2585033) B2585033
theorem B3886055 : Blo 507795 3886055 := bstep (se 1 (by rfl) ⟨2914541, by rfl⟩ : syracuseStep 3886055 = 5829083) B5829083
theorem B969707 : Blo 507795 969707 := bstep (se 1 (by rfl) ⟨727280, by rfl⟩ : syracuseStep 969707 = 1454561) B1454561
theorem B511023 : Blo 507795 511023 := bstep (se 1 (by rfl) ⟨383267, by rfl⟩ : syracuseStep 511023 = 766535) B766535
theorem B511047 : Blo 507795 511047 := bstep (se 1 (by rfl) ⟨383285, by rfl⟩ : syracuseStep 511047 = 766571) B766571
theorem B511199 : Blo 507795 511199 := bstep (se 1 (by rfl) ⟨383399, by rfl⟩ : syracuseStep 511199 = 766799) B766799
theorem B1723625 : Blo 507795 1723625 := bstep (se 2 (by rfl) ⟨646359, by rfl⟩ : syracuseStep 1723625 = 1292719) B1292719
theorem B2575799 : Blo 507795 2575799 := bstep (se 1 (by rfl) ⟨1931849, by rfl⟩ : syracuseStep 2575799 = 3863699) B3863699
theorem B511463 : Blo 507795 511463 := bstep (se 1 (by rfl) ⟨383597, by rfl⟩ : syracuseStep 511463 = 767195) B767195
theorem B1723895 : Blo 507795 1723895 := bstep (se 1 (by rfl) ⟨1292921, by rfl⟩ : syracuseStep 1723895 = 2585843) B2585843
theorem B970231 : Blo 507795 970231 := bstep (se 1 (by rfl) ⟨727673, by rfl⟩ : syracuseStep 970231 = 1455347) B1455347
theorem B4345433 : Blo 507795 4345433 := bstep (se 2 (by rfl) ⟨1629537, by rfl⟩ : syracuseStep 4345433 = 3259075) B3259075
theorem B2575961 : Blo 507795 2575961 := bstep (se 2 (by rfl) ⟨965985, by rfl⟩ : syracuseStep 2575961 = 1931971) B1931971
theorem B5525081 : Blo 507795 5525081 := bstep (se 2 (by rfl) ⟨2071905, by rfl⟩ : syracuseStep 5525081 = 4143811) B4143811
theorem B511579 : Blo 507795 511579 := bstep (se 1 (by rfl) ⟨383684, by rfl⟩ : syracuseStep 511579 = 767369) B767369
theorem B2182763 : Blo 507795 2182763 := bstep (se 1 (by rfl) ⟨1637072, by rfl⟩ : syracuseStep 2182763 = 3274145) B3274145
theorem B970535 : Blo 507795 970535 := bstep (se 1 (by rfl) ⟨727901, by rfl⟩ : syracuseStep 970535 = 1455803) B1455803
theorem B1724921 : Blo 507795 1724921 := bstep (se 2 (by rfl) ⟨646845, by rfl⟩ : syracuseStep 1724921 = 1293691) B1293691
theorem B2478671 : Blo 507795 2478671 := bstep (se 1 (by rfl) ⟨1859003, by rfl⟩ : syracuseStep 2478671 = 3718007) B3718007
theorem B971347 : Blo 507795 971347 := bstep (se 1 (by rfl) ⟨728510, by rfl⟩ : syracuseStep 971347 = 1457021) B1457021
theorem B1725191 : Blo 507795 1725191 := bstep (se 1 (by rfl) ⟨1293893, by rfl⟩ : syracuseStep 1725191 = 2587787) B2587787
theorem B1725245 : Blo 507795 1725245 := bstep (se 3 (by rfl) ⟨323483, by rfl⟩ : syracuseStep 1725245 = 646967) B646967
theorem B9327437 : Blo 507795 9327437 := bstep (se 3 (by rfl) ⟨1748894, by rfl⟩ : syracuseStep 9327437 = 3497789) B3497789
theorem B611183 : Blo 507795 611183 := bstep (se 1 (by rfl) ⟨458387, by rfl⟩ : syracuseStep 611183 = 916775) B916775
theorem B16962509 : Blo 507795 16962509 := bstep (se 3 (by rfl) ⟨3180470, by rfl⟩ : syracuseStep 16962509 = 6360941) B6360941
theorem B1954871 : Blo 507795 1954871 := bstep (se 1 (by rfl) ⟨1466153, by rfl⟩ : syracuseStep 1954871 = 2932307) B2932307
theorem B644203 : Blo 507795 644203 := bstep (se 1 (by rfl) ⟨483152, by rfl⟩ : syracuseStep 644203 = 966305) B966305
theorem B2184403 : Blo 507795 2184403 := bstep (se 1 (by rfl) ⟨1638302, by rfl⟩ : syracuseStep 2184403 = 3276605) B3276605
theorem B5821793 : Blo 507795 5821793 := bstep (se 2 (by rfl) ⟨2183172, by rfl⟩ : syracuseStep 5821793 = 4366345) B4366345
theorem B6542957 : Blo 507795 6542957 := bstep (se 3 (by rfl) ⟨1226804, by rfl⟩ : syracuseStep 6542957 = 2453609) B2453609
theorem B1726271 : Blo 507795 1726271 := bstep (se 1 (by rfl) ⟨1294703, by rfl⟩ : syracuseStep 1726271 = 2589407) B2589407
theorem B2578391 : Blo 507795 2578391 := bstep (se 1 (by rfl) ⟨1933793, by rfl⟩ : syracuseStep 2578391 = 3867587) B3867587
theorem B23517539 : Blo 507795 23517539 := bstep (se 1 (by rfl) ⟨17638154, by rfl⟩ : syracuseStep 23517539 = 35276309) B35276309
theorem B2578877 : Blo 507795 2578877 := bstep (se 3 (by rfl) ⟨483539, by rfl⟩ : syracuseStep 2578877 = 967079) B967079
theorem B4775057 : Blo 507795 4775057 := bstep (se 2 (by rfl) ⟨1790646, by rfl⟩ : syracuseStep 4775057 = 3581293) B3581293
theorem B3857867 : Blo 507795 3857867 := bstep (se 1 (by rfl) ⟨2893400, by rfl⟩ : syracuseStep 3857867 = 5786801) B5786801
theorem B7332227 : Blo 507795 7332227 := bstep (se 1 (by rfl) ⟨5499170, by rfl⟩ : syracuseStep 7332227 = 10998341) B10998341
theorem B161014169 : Blo 507795 161014169 := bstep (se 2 (by rfl) ⟨60380313, by rfl⟩ : syracuseStep 161014169 = 120760627) B120760627
theorem B2908871 : Blo 507795 2908871 := bstep (se 1 (by rfl) ⟨2181653, by rfl⟩ : syracuseStep 2908871 = 4363307) B4363307
theorem B3728591 : Blo 507795 3728591 := bstep (se 1 (by rfl) ⟨2796443, by rfl⟩ : syracuseStep 3728591 = 5592887) B5592887
theorem B1631897 : Blo 507795 1631897 := bstep (se 2 (by rfl) ⟨611961, by rfl⟩ : syracuseStep 1631897 = 1223923) B1223923
theorem B2582279 : Blo 507795 2582279 := bstep (se 1 (by rfl) ⟨1936709, by rfl⟩ : syracuseStep 2582279 = 3873419) B3873419
theorem B3860297 : Blo 507795 3860297 := bstep (se 2 (by rfl) ⟨1447611, by rfl⟩ : syracuseStep 3860297 = 2895223) B2895223
theorem B3435527 : Blo 507795 3435527 := bstep (se 1 (by rfl) ⟨2576645, by rfl⟩ : syracuseStep 3435527 = 5153291) B5153291
theorem B6221407 : Blo 507795 6221407 := bstep (se 1 (by rfl) ⟨4666055, by rfl⟩ : syracuseStep 6221407 = 9332111) B9332111
theorem B1142567 : Blo 507795 1142567 := bstep (se 1 (by rfl) ⟨856925, by rfl⟩ : syracuseStep 1142567 = 1713851) B1713851
theorem B14151667 : Blo 507795 14151667 := bstep (se 1 (by rfl) ⟨10613750, by rfl⟩ : syracuseStep 14151667 = 21227501) B21227501
theorem B9433253 : Blo 507795 9433253 := bstep (se 4 (by rfl) ⟨884367, by rfl⟩ : syracuseStep 9433253 = 1768735) B1768735
theorem B1929527 : Blo 507795 1929527 := bstep (se 1 (by rfl) ⟨1447145, by rfl⟩ : syracuseStep 1929527 = 2894291) B2894291
theorem B2748809 : Blo 507795 2748809 := bstep (se 2 (by rfl) ⟨1030803, by rfl⟩ : syracuseStep 2748809 = 2061607) B2061607
theorem B815609 : Blo 507795 815609 := bstep (se 2 (by rfl) ⟨305853, by rfl⟩ : syracuseStep 815609 = 611707) B611707
theorem B1143593 : Blo 507795 1143593 := bstep (se 2 (by rfl) ⟨428847, by rfl⟩ : syracuseStep 1143593 = 857695) B857695
theorem B1143863 : Blo 507795 1143863 := bstep (se 1 (by rfl) ⟨857897, by rfl⟩ : syracuseStep 1143863 = 1715795) B1715795
theorem B1143881 : Blo 507795 1143881 := bstep (se 2 (by rfl) ⟨428955, by rfl⟩ : syracuseStep 1143881 = 857911) B857911
theorem B15103361 : Blo 507795 15103361 := bstep (se 2 (by rfl) ⟨5663760, by rfl⟩ : syracuseStep 15103361 = 11327521) B11327521
theorem B4781501 : Blo 507795 4781501 := bstep (se 3 (by rfl) ⟨896531, by rfl⟩ : syracuseStep 4781501 = 1793063) B1793063
theorem B2913995 : Blo 507795 2913995 := bstep (se 1 (by rfl) ⟨2185496, by rfl⟩ : syracuseStep 2913995 = 4370993) B4370993
theorem B1832699 : Blo 507795 1832699 := bstep (se 1 (by rfl) ⟨1374524, by rfl⟩ : syracuseStep 1832699 = 2749049) B2749049
theorem B1636253 : Blo 507795 1636253 := bstep (se 3 (by rfl) ⟨306797, by rfl⟩ : syracuseStep 1636253 = 613595) B613595
theorem B3111577 : Blo 507795 3111577 := bstep (se 2 (by rfl) ⟨1166841, by rfl⟩ : syracuseStep 3111577 = 2333683) B2333683
theorem B1145807 : Blo 507795 1145807 := bstep (se 1 (by rfl) ⟨859355, by rfl⟩ : syracuseStep 1145807 = 1718711) B1718711
theorem B1145825 : Blo 507795 1145825 := bstep (se 2 (by rfl) ⟨429684, by rfl⟩ : syracuseStep 1145825 = 859369) B859369
theorem B1145897 : Blo 507795 1145897 := bstep (se 2 (by rfl) ⟨429711, by rfl⟩ : syracuseStep 1145897 = 859423) B859423
theorem B916601 : Blo 507795 916601 := bstep (se 2 (by rfl) ⟨343725, by rfl⟩ : syracuseStep 916601 = 687451) B687451
theorem B1932943 : Blo 507795 1932943 := bstep (se 1 (by rfl) ⟨1449707, by rfl⟩ : syracuseStep 1932943 = 2899415) B2899415
theorem B2752699 : Blo 507795 2752699 := bstep (se 1 (by rfl) ⟨2064524, by rfl⟩ : syracuseStep 2752699 = 4129049) B4129049
theorem B1147067 : Blo 507795 1147067 := bstep (se 1 (by rfl) ⟨860300, by rfl⟩ : syracuseStep 1147067 = 1720601) B1720601
theorem B1147175 : Blo 507795 1147175 := bstep (se 1 (by rfl) ⟨860381, by rfl⟩ : syracuseStep 1147175 = 1720763) B1720763
theorem B1147553 : Blo 507795 1147553 := bstep (se 2 (by rfl) ⟨430332, by rfl⟩ : syracuseStep 1147553 = 860665) B860665
theorem B689095 : Blo 507795 689095 := bstep (se 1 (by rfl) ⟨516821, by rfl⟩ : syracuseStep 689095 = 1033643) B1033643
theorem B1147913 : Blo 507795 1147913 := bstep (se 2 (by rfl) ⟨430467, by rfl⟩ : syracuseStep 1147913 = 860935) B860935
theorem B4195385 : Blo 507795 4195385 := bstep (se 2 (by rfl) ⟨1573269, by rfl⟩ : syracuseStep 4195385 = 3146539) B3146539
theorem B1147967 : Blo 507795 1147967 := bstep (se 1 (by rfl) ⟨860975, by rfl⟩ : syracuseStep 1147967 = 1721951) B1721951
theorem B3278555 : Blo 507795 3278555 := bstep (se 1 (by rfl) ⟨2458916, by rfl⟩ : syracuseStep 3278555 = 4917833) B4917833
theorem B1935161 : Blo 507795 1935161 := bstep (se 2 (by rfl) ⟨725685, by rfl⟩ : syracuseStep 1935161 = 1451371) B1451371
theorem B3868559 : Blo 507795 3868559 := bstep (se 1 (by rfl) ⟨2901419, by rfl⟩ : syracuseStep 3868559 = 5802839) B5802839
theorem B1148903 : Blo 507795 1148903 := bstep (se 1 (by rfl) ⟨861677, by rfl⟩ : syracuseStep 1148903 = 1723355) B1723355
theorem B2590703 : Blo 507795 2590703 := bstep (se 1 (by rfl) ⟨1943027, by rfl⟩ : syracuseStep 2590703 = 3886055) B3886055
theorem B1149083 : Blo 507795 1149083 := bstep (se 1 (by rfl) ⟨861812, by rfl⟩ : syracuseStep 1149083 = 1723625) B1723625
theorem B1149263 : Blo 507795 1149263 := bstep (se 1 (by rfl) ⟨861947, by rfl⟩ : syracuseStep 1149263 = 1723895) B1723895
theorem B1149353 : Blo 507795 1149353 := bstep (se 2 (by rfl) ⟨431007, by rfl⟩ : syracuseStep 1149353 = 862015) B862015
theorem B1149947 : Blo 507795 1149947 := bstep (se 1 (by rfl) ⟨862460, by rfl⟩ : syracuseStep 1149947 = 1724921) B1724921
theorem B920639 : Blo 507795 920639 := bstep (se 1 (by rfl) ⟨690479, by rfl⟩ : syracuseStep 920639 = 1380959) B1380959
theorem B1150127 : Blo 507795 1150127 := bstep (se 1 (by rfl) ⟨862595, by rfl⟩ : syracuseStep 1150127 = 1725191) B1725191
theorem B1150163 : Blo 507795 1150163 := bstep (se 1 (by rfl) ⟨862622, by rfl⟩ : syracuseStep 1150163 = 1725245) B1725245
theorem B11308339 : Blo 507795 11308339 := bstep (se 1 (by rfl) ⟨8481254, by rfl⟩ : syracuseStep 11308339 = 16962509) B16962509
theorem B1150433 : Blo 507795 1150433 := bstep (se 2 (by rfl) ⟨431412, by rfl⟩ : syracuseStep 1150433 = 862825) B862825
theorem B4361971 : Blo 507795 4361971 := bstep (se 1 (by rfl) ⟨3271478, by rfl⟩ : syracuseStep 4361971 = 6542957) B6542957
theorem B2101115 : Blo 507795 2101115 := bstep (se 1 (by rfl) ⟨1575836, by rfl⟩ : syracuseStep 2101115 = 3151673) B3151673
theorem B1150847 : Blo 507795 1150847 := bstep (se 1 (by rfl) ⟨863135, by rfl⟩ : syracuseStep 1150847 = 1726271) B1726271
theorem B2232481 : Blo 507795 2232481 := bstep (se 2 (by rfl) ⟨837180, by rfl⟩ : syracuseStep 2232481 = 1674361) B1674361
theorem B6295805 : Blo 507795 6295805 := bstep (se 3 (by rfl) ⟨1180463, by rfl⟩ : syracuseStep 6295805 = 2360927) B2360927
theorem B1839401 : Blo 507795 1839401 := bstep (se 2 (by rfl) ⟨689775, by rfl⟩ : syracuseStep 1839401 = 1379551) B1379551
theorem B5509549 : Blo 507795 5509549 := bstep (se 3 (by rfl) ⟨1033040, by rfl⟩ : syracuseStep 5509549 = 2066081) B2066081
theorem B1446473 : Blo 507795 1446473 := bstep (se 2 (by rfl) ⟨542427, by rfl⟩ : syracuseStep 1446473 = 1084855) B1084855
theorem B1839689 : Blo 507795 1839689 := bstep (se 2 (by rfl) ⟨689883, by rfl⟩ : syracuseStep 1839689 = 1379767) B1379767
theorem B1938077 : Blo 507795 1938077 := bstep (se 3 (by rfl) ⟨363389, by rfl⟩ : syracuseStep 1938077 = 726779) B726779
theorem B3183371 : Blo 507795 3183371 := bstep (se 1 (by rfl) ⟨2387528, by rfl⟩ : syracuseStep 3183371 = 4775057) B4775057
theorem B8295209 : Blo 507795 8295209 := bstep (se 2 (by rfl) ⟨3110703, by rfl⟩ : syracuseStep 8295209 = 6221407) B6221407
theorem B725851 : Blo 507795 725851 := bstep (se 1 (by rfl) ⟨544388, by rfl⟩ : syracuseStep 725851 = 1088777) B1088777
theorem B1446815 : Blo 507795 1446815 := bstep (se 1 (by rfl) ⟨1085111, by rfl⟩ : syracuseStep 1446815 = 2170223) B2170223
theorem B79303697 : Blo 507795 79303697 := bstep (se 2 (by rfl) ⟨29738886, by rfl⟩ : syracuseStep 79303697 = 59477773) B59477773
theorem B857243 : Blo 507795 857243 := bstep (se 1 (by rfl) ⟨642932, by rfl⟩ : syracuseStep 857243 = 1285865) B1285865
theorem B1938593 : Blo 507795 1938593 := bstep (se 2 (by rfl) ⟨726972, by rfl⟩ : syracuseStep 1938593 = 1453945) B1453945
theorem B4888151 : Blo 507795 4888151 := bstep (se 1 (by rfl) ⟨3666113, by rfl⟩ : syracuseStep 4888151 = 7332227) B7332227
theorem B1939247 : Blo 507795 1939247 := bstep (se 1 (by rfl) ⟨1454435, by rfl⟩ : syracuseStep 1939247 = 2908871) B2908871
theorem B3676265 : Blo 507795 3676265 := bstep (se 2 (by rfl) ⟨1378599, by rfl⟩ : syracuseStep 3676265 = 2757199) B2757199
theorem B1939565 : Blo 507795 1939565 := bstep (se 3 (by rfl) ⟨363668, by rfl⟩ : syracuseStep 1939565 = 727337) B727337
theorem B1087931 : Blo 507795 1087931 := bstep (se 1 (by rfl) ⟨815948, by rfl⟩ : syracuseStep 1087931 = 1631897) B1631897
theorem B858937 : Blo 507795 858937 := bstep (se 2 (by rfl) ⟨322101, by rfl⟩ : syracuseStep 858937 = 644203) B644203
theorem B858991 : Blo 507795 858991 := bstep (se 1 (by rfl) ⟨644243, by rfl⟩ : syracuseStep 858991 = 1288487) B1288487
theorem B4201409 : Blo 507795 4201409 := bstep (se 2 (by rfl) ⟨1575528, by rfl⟩ : syracuseStep 4201409 = 3151057) B3151057
theorem B1842745 : Blo 507795 1842745 := bstep (se 2 (by rfl) ⟨691029, by rfl⟩ : syracuseStep 1842745 = 1382059) B1382059
theorem B6627035 : Blo 507795 6627035 := bstep (se 1 (by rfl) ⟨4970276, by rfl⟩ : syracuseStep 6627035 = 9940553) B9940553
theorem B761711 : Blo 507795 761711 := bstep (se 1 (by rfl) ⟨571283, by rfl⟩ : syracuseStep 761711 = 1142567) B1142567
theorem B2170871 : Blo 507795 2170871 := bstep (se 1 (by rfl) ⟨1628153, by rfl⟩ : syracuseStep 2170871 = 3256307) B3256307
theorem B1286351 : Blo 507795 1286351 := bstep (se 1 (by rfl) ⟨964763, by rfl⟩ : syracuseStep 1286351 = 1929527) B1929527
theorem B762395 : Blo 507795 762395 := bstep (se 1 (by rfl) ⟨571796, by rfl⟩ : syracuseStep 762395 = 1143593) B1143593
theorem B860699 : Blo 507795 860699 := bstep (se 1 (by rfl) ⟨645524, by rfl⟩ : syracuseStep 860699 = 1291049) B1291049
theorem B762575 : Blo 507795 762575 := bstep (se 1 (by rfl) ⟨571931, by rfl⟩ : syracuseStep 762575 = 1143863) B1143863
theorem B762587 : Blo 507795 762587 := bstep (se 1 (by rfl) ⟨571940, by rfl⟩ : syracuseStep 762587 = 1143881) B1143881
theorem B10068907 : Blo 507795 10068907 := bstep (se 1 (by rfl) ⟨7551680, by rfl⟩ : syracuseStep 10068907 = 15103361) B15103361
theorem B3187667 : Blo 507795 3187667 := bstep (se 1 (by rfl) ⟨2390750, by rfl⟩ : syracuseStep 3187667 = 4781501) B4781501
theorem B763001 : Blo 507795 763001 := bstep (se 2 (by rfl) ⟨286125, by rfl⟩ : syracuseStep 763001 = 572251) B572251
theorem B1942649 : Blo 507795 1942649 := bstep (se 2 (by rfl) ⟨728493, by rfl⟩ : syracuseStep 1942649 = 1456987) B1456987
theorem B1942663 : Blo 507795 1942663 := bstep (se 1 (by rfl) ⟨1456997, by rfl⟩ : syracuseStep 1942663 = 2913995) B2913995
theorem B7349413 : Blo 507795 7349413 := bstep (se 4 (by rfl) ⟨689007, by rfl⟩ : syracuseStep 7349413 = 1378015) B1378015
theorem B1221799 : Blo 507795 1221799 := bstep (se 1 (by rfl) ⟨916349, by rfl⟩ : syracuseStep 1221799 = 1832699) B1832699
theorem B1090835 : Blo 507795 1090835 := bstep (se 1 (by rfl) ⟨818126, by rfl⟩ : syracuseStep 1090835 = 1636253) B1636253
theorem B2172359 : Blo 507795 2172359 := bstep (se 1 (by rfl) ⟨1629269, by rfl⟩ : syracuseStep 2172359 = 3258539) B3258539
theorem B763871 : Blo 507795 763871 := bstep (se 1 (by rfl) ⟨572903, by rfl⟩ : syracuseStep 763871 = 1145807) B1145807
theorem B763883 : Blo 507795 763883 := bstep (se 1 (by rfl) ⟨572912, by rfl⟩ : syracuseStep 763883 = 1145825) B1145825
theorem B763931 : Blo 507795 763931 := bstep (se 1 (by rfl) ⟨572948, by rfl⟩ : syracuseStep 763931 = 1145897) B1145897
theorem B764297 : Blo 507795 764297 := bstep (se 2 (by rfl) ⟨286611, by rfl⟩ : syracuseStep 764297 = 573223) B573223
theorem B1551071 : Blo 507795 1551071 := bstep (se 1 (by rfl) ⟨1163303, by rfl⟩ : syracuseStep 1551071 = 2326607) B2326607
theorem B765239 : Blo 507795 765239 := bstep (se 1 (by rfl) ⟨573929, by rfl⟩ : syracuseStep 765239 = 1147859) B1147859
theorem B765407 : Blo 507795 765407 := bstep (se 1 (by rfl) ⟨574055, by rfl⟩ : syracuseStep 765407 = 1148111) B1148111
theorem B765623 : Blo 507795 765623 := bstep (se 1 (by rfl) ⟨574217, by rfl⟩ : syracuseStep 765623 = 1148435) B1148435
theorem B765833 : Blo 507795 765833 := bstep (se 2 (by rfl) ⟨287187, by rfl⟩ : syracuseStep 765833 = 574375) B574375
theorem B2174957 : Blo 507795 2174957 := bstep (se 3 (by rfl) ⟨407804, by rfl⟩ : syracuseStep 2174957 = 815609) B815609
theorem B766079 : Blo 507795 766079 := bstep (se 1 (by rfl) ⟨574559, by rfl⟩ : syracuseStep 766079 = 1149119) B1149119
theorem B1454219 : Blo 507795 1454219 := bstep (se 1 (by rfl) ⟨1090664, by rfl⟩ : syracuseStep 1454219 = 2181329) B2181329
theorem B17707319 : Blo 507795 17707319 := bstep (se 1 (by rfl) ⟨13280489, by rfl⟩ : syracuseStep 17707319 = 26560979) B26560979
theorem B766715 : Blo 507795 766715 := bstep (se 1 (by rfl) ⟨575036, by rfl⟩ : syracuseStep 766715 = 1150073) B1150073
theorem B16495433 : Blo 507795 16495433 := bstep (se 2 (by rfl) ⟨6185787, by rfl⟩ : syracuseStep 16495433 = 12371575) B12371575
theorem B1717199 : Blo 507795 1717199 := bstep (se 1 (by rfl) ⟨1287899, by rfl⟩ : syracuseStep 1717199 = 2575799) B2575799
theorem B2896955 : Blo 507795 2896955 := bstep (se 1 (by rfl) ⟨2172716, by rfl⟩ : syracuseStep 2896955 = 4345433) B4345433
theorem B1717307 : Blo 507795 1717307 := bstep (se 1 (by rfl) ⟨1287980, by rfl⟩ : syracuseStep 1717307 = 2575961) B2575961
theorem B3683387 : Blo 507795 3683387 := bstep (se 1 (by rfl) ⟨2762540, by rfl⟩ : syracuseStep 3683387 = 5525081) B5525081
theorem B1455175 : Blo 507795 1455175 := bstep (se 1 (by rfl) ⟨1091381, by rfl⟩ : syracuseStep 1455175 = 2182763) B2182763
theorem B767159 : Blo 507795 767159 := bstep (se 1 (by rfl) ⟨575369, by rfl⟩ : syracuseStep 767159 = 1150739) B1150739
theorem B4371677 : Blo 507795 4371677 := bstep (se 3 (by rfl) ⟨819689, by rfl⟩ : syracuseStep 4371677 = 1639379) B1639379
theorem B1717577 : Blo 507795 1717577 := bstep (se 2 (by rfl) ⟨644091, by rfl⟩ : syracuseStep 1717577 = 1288183) B1288183
theorem B767399 : Blo 507795 767399 := bstep (se 1 (by rfl) ⟨575549, by rfl⟩ : syracuseStep 767399 = 1151099) B1151099
theorem B767579 : Blo 507795 767579 := bstep (se 1 (by rfl) ⟨575684, by rfl⟩ : syracuseStep 767579 = 1151369) B1151369
theorem B1652447 : Blo 507795 1652447 := bstep (se 1 (by rfl) ⟨1239335, by rfl⟩ : syracuseStep 1652447 = 2478671) B2478671
theorem B12433277 : Blo 507795 12433277 := bstep (se 3 (by rfl) ⟨2331239, by rfl⟩ : syracuseStep 12433277 = 4662479) B4662479
theorem B6961153 : Blo 507795 6961153 := bstep (se 2 (by rfl) ⟨2610432, by rfl⟩ : syracuseStep 6961153 = 5220865) B5220865
theorem B964649 : Blo 507795 964649 := bstep (se 2 (by rfl) ⟨361743, by rfl⟩ : syracuseStep 964649 = 723487) B723487
theorem B16595077 : Blo 507795 16595077 := bstep (se 4 (by rfl) ⟨1555788, by rfl⟩ : syracuseStep 16595077 = 3111577) B3111577
theorem B3881195 : Blo 507795 3881195 := bstep (se 1 (by rfl) ⟨2910896, by rfl⟩ : syracuseStep 3881195 = 5821793) B5821793
theorem B1292537 : Blo 507795 1292537 := bstep (se 2 (by rfl) ⟨484701, by rfl⟩ : syracuseStep 1292537 = 969403) B969403
theorem B571855 : Blo 507795 571855 := bstep (se 1 (by rfl) ⟨428891, by rfl⟩ : syracuseStep 571855 = 857783) B857783
theorem B1718927 : Blo 507795 1718927 := bstep (se 1 (by rfl) ⟨1289195, by rfl⟩ : syracuseStep 1718927 = 2578391) B2578391
theorem B2898665 : Blo 507795 2898665 := bstep (se 2 (by rfl) ⟨1086999, by rfl⟩ : syracuseStep 2898665 = 2173999) B2173999
theorem B15678359 : Blo 507795 15678359 := bstep (se 1 (by rfl) ⟨11758769, by rfl⟩ : syracuseStep 15678359 = 23517539) B23517539
theorem B1719251 : Blo 507795 1719251 := bstep (se 1 (by rfl) ⟨1289438, by rfl⟩ : syracuseStep 1719251 = 2578877) B2578877
theorem B965857 : Blo 507795 965857 := bstep (se 2 (by rfl) ⟨362196, by rfl⟩ : syracuseStep 965857 = 724393) B724393
theorem B1719521 : Blo 507795 1719521 := bstep (se 2 (by rfl) ⟨644820, by rfl⟩ : syracuseStep 1719521 = 1289641) B1289641
theorem B572647 : Blo 507795 572647 := bstep (se 1 (by rfl) ⟨429485, by rfl⟩ : syracuseStep 572647 = 858971) B858971
theorem B1293641 : Blo 507795 1293641 := bstep (se 2 (by rfl) ⟨485115, by rfl⟩ : syracuseStep 1293641 = 970231) B970231
theorem B1031743 : Blo 507795 1031743 := bstep (se 1 (by rfl) ⟨773807, by rfl⟩ : syracuseStep 1031743 = 1547615) B1547615
theorem B2571911 : Blo 507795 2571911 := bstep (se 1 (by rfl) ⟨1928933, by rfl⟩ : syracuseStep 2571911 = 3857867) B3857867
theorem B1720169 : Blo 507795 1720169 := bstep (se 2 (by rfl) ⟨645063, by rfl⟩ : syracuseStep 1720169 = 1290127) B1290127
theorem B573295 : Blo 507795 573295 := bstep (se 1 (by rfl) ⟨429971, by rfl⟩ : syracuseStep 573295 = 859943) B859943
theorem B507815 : Blo 507795 507815 := bstep (se 1 (by rfl) ⟨380861, by rfl⟩ : syracuseStep 507815 = 761723) B761723
theorem B508095 : Blo 507795 508095 := bstep (se 1 (by rfl) ⟨381071, by rfl⟩ : syracuseStep 508095 = 762143) B762143
theorem B508111 : Blo 507795 508111 := bstep (se 1 (by rfl) ⟨381083, by rfl⟩ : syracuseStep 508111 = 762167) B762167
theorem B1229035 : Blo 507795 1229035 := bstep (se 1 (by rfl) ⟨921776, by rfl⟩ : syracuseStep 1229035 = 1843553) B1843553
theorem B508159 : Blo 507795 508159 := bstep (se 1 (by rfl) ⟨381119, by rfl⟩ : syracuseStep 508159 = 762239) B762239
theorem B508207 : Blo 507795 508207 := bstep (se 1 (by rfl) ⟨381155, by rfl⟩ : syracuseStep 508207 = 762311) B762311
theorem B508443 : Blo 507795 508443 := bstep (se 1 (by rfl) ⟨381332, by rfl⟩ : syracuseStep 508443 = 762665) B762665
theorem B573979 : Blo 507795 573979 := bstep (se 1 (by rfl) ⟨430484, by rfl⟩ : syracuseStep 573979 = 860969) B860969
theorem B508447 : Blo 507795 508447 := bstep (se 1 (by rfl) ⟨381335, by rfl⟩ : syracuseStep 508447 = 762671) B762671
theorem B508527 : Blo 507795 508527 := bstep (se 1 (by rfl) ⟨381395, by rfl⟩ : syracuseStep 508527 = 762791) B762791
theorem B508583 : Blo 507795 508583 := bstep (se 1 (by rfl) ⟨381437, by rfl⟩ : syracuseStep 508583 = 762875) B762875
theorem B508623 : Blo 507795 508623 := bstep (se 1 (by rfl) ⟨381467, by rfl⟩ : syracuseStep 508623 = 762935) B762935
theorem B574159 : Blo 507795 574159 := bstep (se 1 (by rfl) ⟨430619, by rfl⟩ : syracuseStep 574159 = 861239) B861239
theorem B1295129 : Blo 507795 1295129 := bstep (se 2 (by rfl) ⟨485673, by rfl⟩ : syracuseStep 1295129 = 971347) B971347
theorem B508703 : Blo 507795 508703 := bstep (se 1 (by rfl) ⟨381527, by rfl⟩ : syracuseStep 508703 = 763055) B763055
theorem B508975 : Blo 507795 508975 := bstep (se 1 (by rfl) ⟨381731, by rfl⟩ : syracuseStep 508975 = 763463) B763463
theorem B509039 : Blo 507795 509039 := bstep (se 1 (by rfl) ⟨381779, by rfl⟩ : syracuseStep 509039 = 763559) B763559
theorem B509095 : Blo 507795 509095 := bstep (se 1 (by rfl) ⟨381821, by rfl⟩ : syracuseStep 509095 = 763643) B763643
theorem B1721519 : Blo 507795 1721519 := bstep (se 1 (by rfl) ⟨1291139, by rfl⟩ : syracuseStep 1721519 = 2582279) B2582279
theorem B509119 : Blo 507795 509119 := bstep (se 1 (by rfl) ⟨381839, by rfl⟩ : syracuseStep 509119 = 763679) B763679
theorem B2573531 : Blo 507795 2573531 := bstep (se 1 (by rfl) ⟨1930148, by rfl⟩ : syracuseStep 2573531 = 3860297) B3860297
theorem B509151 : Blo 507795 509151 := bstep (se 1 (by rfl) ⟨381863, by rfl⟩ : syracuseStep 509151 = 763727) B763727
theorem B2213099 : Blo 507795 2213099 := bstep (se 1 (by rfl) ⟨1659824, by rfl⟩ : syracuseStep 2213099 = 3319649) B3319649
theorem B509231 : Blo 507795 509231 := bstep (se 1 (by rfl) ⟨381923, by rfl⟩ : syracuseStep 509231 = 763847) B763847
theorem B968105 : Blo 507795 968105 := bstep (se 2 (by rfl) ⟨363039, by rfl⟩ : syracuseStep 968105 = 726079) B726079
theorem B509467 : Blo 507795 509467 := bstep (se 1 (by rfl) ⟨382100, by rfl⟩ : syracuseStep 509467 = 764201) B764201
theorem B509471 : Blo 507795 509471 := bstep (se 1 (by rfl) ⟨382103, by rfl⟩ : syracuseStep 509471 = 764207) B764207
theorem B509631 : Blo 507795 509631 := bstep (se 1 (by rfl) ⟨382223, by rfl⟩ : syracuseStep 509631 = 764447) B764447
theorem B575167 : Blo 507795 575167 := bstep (se 1 (by rfl) ⟨431375, by rfl⟩ : syracuseStep 575167 = 862751) B862751
theorem B509887 : Blo 507795 509887 := bstep (se 1 (by rfl) ⟨382415, by rfl⟩ : syracuseStep 509887 = 764831) B764831
theorem B509919 : Blo 507795 509919 := bstep (se 1 (by rfl) ⟨382439, by rfl⟩ : syracuseStep 509919 = 764879) B764879
theorem B575455 : Blo 507795 575455 := bstep (se 1 (by rfl) ⟨431591, by rfl⟩ : syracuseStep 575455 = 863183) B863183
theorem B509979 : Blo 507795 509979 := bstep (se 1 (by rfl) ⟨382484, by rfl⟩ : syracuseStep 509979 = 764969) B764969
theorem B509983 : Blo 507795 509983 := bstep (se 1 (by rfl) ⟨382487, by rfl⟩ : syracuseStep 509983 = 764975) B764975
theorem B968735 : Blo 507795 968735 := bstep (se 1 (by rfl) ⟨726551, by rfl⟩ : syracuseStep 968735 = 1453103) B1453103
theorem B509999 : Blo 507795 509999 := bstep (se 1 (by rfl) ⟨382499, by rfl⟩ : syracuseStep 509999 = 764999) B764999
theorem B510175 : Blo 507795 510175 := bstep (se 1 (by rfl) ⟨382631, by rfl⟩ : syracuseStep 510175 = 765263) B765263
theorem B510235 : Blo 507795 510235 := bstep (se 1 (by rfl) ⟨382676, by rfl⟩ : syracuseStep 510235 = 765353) B765353
theorem B510335 : Blo 507795 510335 := bstep (se 1 (by rfl) ⟨382751, by rfl⟩ : syracuseStep 510335 = 765503) B765503
theorem B510511 : Blo 507795 510511 := bstep (se 1 (by rfl) ⟨382883, by rfl⟩ : syracuseStep 510511 = 765767) B765767
theorem B510567 : Blo 507795 510567 := bstep (se 1 (by rfl) ⟨382925, by rfl⟩ : syracuseStep 510567 = 765851) B765851
theorem B969563 : Blo 507795 969563 := bstep (se 1 (by rfl) ⟨727172, by rfl⟩ : syracuseStep 969563 = 1454345) B1454345
theorem B510943 : Blo 507795 510943 := bstep (se 1 (by rfl) ⟨383207, by rfl⟩ : syracuseStep 510943 = 766415) B766415
theorem B2444269 : Blo 507795 2444269 := bstep (se 3 (by rfl) ⟨458300, by rfl⟩ : syracuseStep 2444269 = 916601) B916601
theorem B3263483 : Blo 507795 3263483 := bstep (se 1 (by rfl) ⟨2447612, by rfl⟩ : syracuseStep 3263483 = 4895225) B4895225
theorem B510971 : Blo 507795 510971 := bstep (se 1 (by rfl) ⟨383228, by rfl⟩ : syracuseStep 510971 = 766457) B766457
theorem B511039 : Blo 507795 511039 := bstep (se 1 (by rfl) ⟨383279, by rfl⟩ : syracuseStep 511039 = 766559) B766559
theorem B511359 : Blo 507795 511359 := bstep (se 1 (by rfl) ⟨383519, by rfl⟩ : syracuseStep 511359 = 767039) B767039
theorem B511387 : Blo 507795 511387 := bstep (se 1 (by rfl) ⟨383540, by rfl⟩ : syracuseStep 511387 = 767081) B767081
theorem B511455 : Blo 507795 511455 := bstep (se 1 (by rfl) ⟨383591, by rfl⟩ : syracuseStep 511455 = 767183) B767183
theorem B511591 : Blo 507795 511591 := bstep (se 1 (by rfl) ⟨383693, by rfl⟩ : syracuseStep 511591 = 767387) B767387
theorem B511739 : Blo 507795 511739 := bstep (se 1 (by rfl) ⟨383804, by rfl⟩ : syracuseStep 511739 = 767609) B767609
theorem B643135 : Blo 507795 643135 := bstep (se 1 (by rfl) ⟨482351, by rfl⟩ : syracuseStep 643135 = 964703) B964703
theorem B13095755 : Blo 507795 13095755 := bstep (se 1 (by rfl) ⟨9821816, by rfl⟩ : syracuseStep 13095755 = 19643633) B19643633
theorem B2577257 : Blo 507795 2577257 := bstep (se 2 (by rfl) ⟨966471, by rfl⟩ : syracuseStep 2577257 = 1932943) B1932943
theorem B1627231 : Blo 507795 1627231 := bstep (se 1 (by rfl) ⟨1220423, by rfl⟩ : syracuseStep 1627231 = 2440847) B2440847
theorem B1037519 : Blo 507795 1037519 := bstep (se 1 (by rfl) ⟨778139, by rfl⟩ : syracuseStep 1037519 = 1556279) B1556279
theorem B13981081 : Blo 507795 13981081 := bstep (se 2 (by rfl) ⟨5242905, by rfl⟩ : syracuseStep 13981081 = 10485811) B10485811
theorem B6641189 : Blo 507795 6641189 := bstep (se 4 (by rfl) ⟨622611, by rfl⟩ : syracuseStep 6641189 = 1245223) B1245223
theorem B645023 : Blo 507795 645023 := bstep (se 1 (by rfl) ⟨483767, by rfl⟩ : syracuseStep 645023 = 967535) B967535
theorem B1726433 : Blo 507795 1726433 := bstep (se 2 (by rfl) ⟨647412, by rfl⟩ : syracuseStep 1726433 = 1294825) B1294825
theorem B3856409 : Blo 507795 3856409 := bstep (se 2 (by rfl) ⟨1446153, by rfl⟩ : syracuseStep 3856409 = 2892307) B2892307
theorem B2185633 : Blo 507795 2185633 := bstep (se 2 (by rfl) ⟨819612, by rfl⟩ : syracuseStep 2185633 = 1639225) B1639225
theorem B4413971 : Blo 507795 4413971 := bstep (se 1 (by rfl) ⟨3310478, by rfl⟩ : syracuseStep 4413971 = 6620957) B6620957
theorem B4905683 : Blo 507795 4905683 := bstep (se 1 (by rfl) ⟨3679262, by rfl⟩ : syracuseStep 4905683 = 7358525) B7358525
theorem B1629281 : Blo 507795 1629281 := bstep (se 2 (by rfl) ⟨610980, by rfl⟩ : syracuseStep 1629281 = 1221961) B1221961
theorem B7462205 : Blo 507795 7462205 := bstep (se 3 (by rfl) ⟨1399163, by rfl⟩ : syracuseStep 7462205 = 2798327) B2798327
theorem B646471 : Blo 507795 646471 := bstep (se 1 (by rfl) ⟨484853, by rfl⟩ : syracuseStep 646471 = 969707) B969707
theorem B5791175 : Blo 507795 5791175 := bstep (se 1 (by rfl) ⟨4343381, by rfl⟩ : syracuseStep 5791175 = 8686763) B8686763
theorem B22076945 : Blo 507795 22076945 := bstep (se 2 (by rfl) ⟨8278854, by rfl⟩ : syracuseStep 22076945 = 16557709) B16557709
theorem B18538105 : Blo 507795 18538105 := bstep (se 2 (by rfl) ⟨6951789, by rfl⟩ : syracuseStep 18538105 = 13903579) B13903579
theorem B1629821 : Blo 507795 1629821 := bstep (se 3 (by rfl) ⟨305591, by rfl⟩ : syracuseStep 1629821 = 611183) B611183
theorem B4349807 : Blo 507795 4349807 := bstep (se 1 (by rfl) ⟨3262355, by rfl⟩ : syracuseStep 4349807 = 6524711) B6524711
theorem B2580335 : Blo 507795 2580335 := bstep (se 1 (by rfl) ⟨1935251, by rfl⟩ : syracuseStep 2580335 = 3870503) B3870503
theorem B647023 : Blo 507795 647023 := bstep (se 1 (by rfl) ⟨485267, by rfl⟩ : syracuseStep 647023 = 970535) B970535
theorem B9527759 : Blo 507795 9527759 := bstep (se 1 (by rfl) ⟨7145819, by rfl⟩ : syracuseStep 9527759 = 14291639) B14291639
theorem B6218291 : Blo 507795 6218291 := bstep (se 1 (by rfl) ⟨4663718, by rfl⟩ : syracuseStep 6218291 = 9327437) B9327437
theorem B1303247 : Blo 507795 1303247 := bstep (se 1 (by rfl) ⟨977435, by rfl⟩ : syracuseStep 1303247 = 1954871) B1954871
theorem B4908221 : Blo 507795 4908221 := bstep (se 3 (by rfl) ⟨920291, by rfl⟩ : syracuseStep 4908221 = 1840583) B1840583
theorem B16541101 : Blo 507795 16541101 := bstep (se 3 (by rfl) ⟨3101456, by rfl⟩ : syracuseStep 16541101 = 6202913) B6202913
theorem B4351583 : Blo 507795 4351583 := bstep (se 1 (by rfl) ⟨3263687, by rfl⟩ : syracuseStep 4351583 = 6527375) B6527375
theorem B3107297 : Blo 507795 3107297 := bstep (se 2 (by rfl) ⟨1165236, by rfl⟩ : syracuseStep 3107297 = 2330473) B2330473
theorem B813559 : Blo 507795 813559 := bstep (se 1 (by rfl) ⟨610169, by rfl⟩ : syracuseStep 813559 = 1220339) B1220339
theorem B18868889 : Blo 507795 18868889 := bstep (se 2 (by rfl) ⟨7075833, by rfl⟩ : syracuseStep 18868889 = 14151667) B14151667
theorem B107342779 : Blo 507795 107342779 := bstep (se 1 (by rfl) ⟨80507084, by rfl⟩ : syracuseStep 107342779 = 161014169) B161014169
theorem B8350937 : Blo 507795 8350937 := bstep (se 2 (by rfl) ⟨3131601, by rfl⟩ : syracuseStep 8350937 = 6263203) B6263203
theorem B2485727 : Blo 507795 2485727 := bstep (se 1 (by rfl) ⟨1864295, by rfl⟩ : syracuseStep 2485727 = 3728591) B3728591
theorem B1929041 : Blo 507795 1929041 := bstep (se 2 (by rfl) ⟨723390, by rfl⟩ : syracuseStep 1929041 = 1446781) B1446781
theorem B1142747 : Blo 507795 1142747 := bstep (se 1 (by rfl) ⟨857060, by rfl⟩ : syracuseStep 1142747 = 1714121) B1714121
theorem B2912219 : Blo 507795 2912219 := bstep (se 1 (by rfl) ⟨2184164, by rfl⟩ : syracuseStep 2912219 = 4368329) B4368329
theorem B1142927 : Blo 507795 1142927 := bstep (se 1 (by rfl) ⟨857195, by rfl⟩ : syracuseStep 1142927 = 1714391) B1714391
theorem B1929359 : Blo 507795 1929359 := bstep (se 1 (by rfl) ⟨1447019, by rfl⟩ : syracuseStep 1929359 = 2894039) B2894039
theorem B1143017 : Blo 507795 1143017 := bstep (se 2 (by rfl) ⟨428631, by rfl⟩ : syracuseStep 1143017 = 857263) B857263
theorem B2912537 : Blo 507795 2912537 := bstep (se 2 (by rfl) ⟨1092201, by rfl⟩ : syracuseStep 2912537 = 2184403) B2184403
theorem B1143143 : Blo 507795 1143143 := bstep (se 1 (by rfl) ⟨857357, by rfl⟩ : syracuseStep 1143143 = 1714715) B1714715
theorem B2912719 : Blo 507795 2912719 := bstep (se 1 (by rfl) ⟨2184539, by rfl⟩ : syracuseStep 2912719 = 4369079) B4369079
theorem B2290351 : Blo 507795 2290351 := bstep (se 1 (by rfl) ⟨1717763, by rfl⟩ : syracuseStep 2290351 = 3435527) B3435527
theorem B1143719 : Blo 507795 1143719 := bstep (se 1 (by rfl) ⟨857789, by rfl⟩ : syracuseStep 1143719 = 1715579) B1715579
theorem B816551 : Blo 507795 816551 := bstep (se 1 (by rfl) ⟨612413, by rfl⟩ : syracuseStep 816551 = 1224827) B1224827
theorem B6288835 : Blo 507795 6288835 := bstep (se 1 (by rfl) ⟨4716626, by rfl⟩ : syracuseStep 6288835 = 9433253) B9433253
theorem B1832539 : Blo 507795 1832539 := bstep (se 1 (by rfl) ⟨1374404, by rfl⟩ : syracuseStep 1832539 = 2748809) B2748809
theorem B1144655 : Blo 507795 1144655 := bstep (se 1 (by rfl) ⟨858491, by rfl⟩ : syracuseStep 1144655 = 1716983) B1716983
theorem B1145015 : Blo 507795 1145015 := bstep (se 1 (by rfl) ⟨858761, by rfl⟩ : syracuseStep 1145015 = 1717523) B1717523
theorem B2914703 : Blo 507795 2914703 := bstep (se 1 (by rfl) ⟨2186027, by rfl⟩ : syracuseStep 2914703 = 4372055) B4372055
theorem B1145375 : Blo 507795 1145375 := bstep (se 1 (by rfl) ⟨859031, by rfl⟩ : syracuseStep 1145375 = 1718063) B1718063
theorem B1145609 : Blo 507795 1145609 := bstep (se 2 (by rfl) ⟨429603, by rfl⟩ : syracuseStep 1145609 = 859207) B859207
theorem B1244441 : Blo 507795 1244441 := bstep (se 2 (by rfl) ⟨466665, by rfl⟩ : syracuseStep 1244441 = 933331) B933331
theorem B1146185 : Blo 507795 1146185 := bstep (se 2 (by rfl) ⟨429819, by rfl⟩ : syracuseStep 1146185 = 859639) B859639
theorem B1146295 : Blo 507795 1146295 := bstep (se 1 (by rfl) ⟨859721, by rfl⟩ : syracuseStep 1146295 = 1719443) B1719443
theorem B1932929 : Blo 507795 1932929 := bstep (se 2 (by rfl) ⟨724848, by rfl⟩ : syracuseStep 1932929 = 1449697) B1449697
theorem B1146599 : Blo 507795 1146599 := bstep (se 1 (by rfl) ⟨859949, by rfl⟩ : syracuseStep 1146599 = 1719899) B1719899
theorem B3670265 : Blo 507795 3670265 := bstep (se 2 (by rfl) ⟨1376349, by rfl⟩ : syracuseStep 3670265 = 2752699) B2752699
theorem B1638713 : Blo 507795 1638713 := bstep (se 2 (by rfl) ⟨614517, by rfl⟩ : syracuseStep 1638713 = 1229035) B1229035
theorem B1147679 : Blo 507795 1147679 := bstep (se 1 (by rfl) ⟨860759, by rfl⟩ : syracuseStep 1147679 = 1721519) B1721519
theorem B1475399 : Blo 507795 1475399 := bstep (se 1 (by rfl) ⟨1106549, by rfl⟩ : syracuseStep 1475399 = 2213099) B2213099
theorem B918793 : Blo 507795 918793 := bstep (se 2 (by rfl) ⟨344547, by rfl⟩ : syracuseStep 918793 = 689095) B689095
theorem B2590217 : Blo 507795 2590217 := bstep (se 2 (by rfl) ⟨971331, by rfl⟩ : syracuseStep 2590217 = 1942663) B1942663
theorem B9799217 : Blo 507795 9799217 := bstep (se 2 (by rfl) ⟨3674706, by rfl⟩ : syracuseStep 9799217 = 7349413) B7349413
theorem B3475325 : Blo 507795 3475325 := bstep (se 3 (by rfl) ⟨651623, by rfl⟩ : syracuseStep 3475325 = 1303247) B1303247
theorem B22054801 : Blo 507795 22054801 := bstep (se 2 (by rfl) ⟨8270550, by rfl⟩ : syracuseStep 22054801 = 16541101) B16541101
theorem B4197203 : Blo 507795 4197203 := bstep (se 1 (by rfl) ⟨3147902, by rfl⟩ : syracuseStep 4197203 = 6295805) B6295805
theorem B1084745 : Blo 507795 1084745 := bstep (se 2 (by rfl) ⟨406779, by rfl⟩ : syracuseStep 1084745 = 813559) B813559
theorem B691679 : Blo 507795 691679 := bstep (se 1 (by rfl) ⟨518759, by rfl⟩ : syracuseStep 691679 = 1037519) B1037519
theorem B4427459 : Blo 507795 4427459 := bstep (se 1 (by rfl) ⟨3320594, by rfl⟩ : syracuseStep 4427459 = 6641189) B6641189
theorem B1150955 : Blo 507795 1150955 := bstep (se 1 (by rfl) ⟨863216, by rfl⟩ : syracuseStep 1150955 = 1726433) B1726433
theorem B725287 : Blo 507795 725287 := bstep (se 1 (by rfl) ⟨543965, by rfl⟩ : syracuseStep 725287 = 1087931) B1087931
theorem B14717963 : Blo 507795 14717963 := bstep (se 1 (by rfl) ⟨11038472, by rfl⟩ : syracuseStep 14717963 = 22076945) B22076945
theorem B1086547 : Blo 507795 1086547 := bstep (se 1 (by rfl) ⟨814910, by rfl⟩ : syracuseStep 1086547 = 1629821) B1629821
theorem B1447247 : Blo 507795 1447247 := bstep (se 1 (by rfl) ⟨1085435, by rfl⟩ : syracuseStep 1447247 = 2170871) B2170871
theorem B857513 : Blo 507795 857513 := bstep (se 2 (by rfl) ⟨321567, by rfl⟩ : syracuseStep 857513 = 643135) B643135
theorem B857567 : Blo 507795 857567 := bstep (se 1 (by rfl) ⟨643175, by rfl⟩ : syracuseStep 857567 = 1286351) B1286351
theorem B7346065 : Blo 507795 7346065 := bstep (se 2 (by rfl) ⟨2754774, by rfl⟩ : syracuseStep 7346065 = 5509549) B5509549
theorem B727223 : Blo 507795 727223 := bstep (se 1 (by rfl) ⟨545417, by rfl⟩ : syracuseStep 727223 = 1090835) B1090835
theorem B3053801 : Blo 507795 3053801 := bstep (se 2 (by rfl) ⟨1145175, by rfl⟩ : syracuseStep 3053801 = 2290351) B2290351
theorem B1448239 : Blo 507795 1448239 := bstep (se 1 (by rfl) ⟨1086179, by rfl⟩ : syracuseStep 1448239 = 2172359) B2172359
theorem B1940233 : Blo 507795 1940233 := bstep (se 2 (by rfl) ⟨727587, by rfl⟩ : syracuseStep 1940233 = 1455175) B1455175
theorem B2169641 : Blo 507795 2169641 := bstep (se 2 (by rfl) ⟨813615, by rfl⟩ : syracuseStep 2169641 = 1627231) B1627231
theorem B2071531 : Blo 507795 2071531 := bstep (se 1 (by rfl) ⟨1553648, by rfl⟩ : syracuseStep 2071531 = 3107297) B3107297
theorem B1286027 : Blo 507795 1286027 := bstep (se 1 (by rfl) ⟨964520, by rfl⟩ : syracuseStep 1286027 = 1929041) B1929041
theorem B761831 : Blo 507795 761831 := bstep (se 1 (by rfl) ⟨571373, by rfl⟩ : syracuseStep 761831 = 1142747) B1142747
theorem B1941479 : Blo 507795 1941479 := bstep (se 1 (by rfl) ⟨1456109, by rfl⟩ : syracuseStep 1941479 = 2912219) B2912219
theorem B1449971 : Blo 507795 1449971 := bstep (se 1 (by rfl) ⟨1087478, by rfl⟩ : syracuseStep 1449971 = 2174957) B2174957
theorem B9281537 : Blo 507795 9281537 := bstep (se 2 (by rfl) ⟨3480576, by rfl⟩ : syracuseStep 9281537 = 6961153) B6961153
theorem B761951 : Blo 507795 761951 := bstep (se 1 (by rfl) ⟨571463, by rfl⟩ : syracuseStep 761951 = 1142927) B1142927
theorem B1286239 : Blo 507795 1286239 := bstep (se 1 (by rfl) ⟨964679, by rfl⟩ : syracuseStep 1286239 = 1929359) B1929359
theorem B762011 : Blo 507795 762011 := bstep (se 1 (by rfl) ⟨571508, by rfl⟩ : syracuseStep 762011 = 1143017) B1143017
theorem B22126769 : Blo 507795 22126769 := bstep (se 2 (by rfl) ⟨8297538, by rfl⟩ : syracuseStep 22126769 = 16595077) B16595077
theorem B1941691 : Blo 507795 1941691 := bstep (se 1 (by rfl) ⟨1456268, by rfl⟩ : syracuseStep 1941691 = 2912537) B2912537
theorem B11804879 : Blo 507795 11804879 := bstep (se 1 (by rfl) ⟨8853659, by rfl⟩ : syracuseStep 11804879 = 17707319) B17707319
theorem B762095 : Blo 507795 762095 := bstep (se 1 (by rfl) ⟨571571, by rfl⟩ : syracuseStep 762095 = 1143143) B1143143
theorem B762473 : Blo 507795 762473 := bstep (se 2 (by rfl) ⟨285927, by rfl⟩ : syracuseStep 762473 = 571855) B571855
theorem B762479 : Blo 507795 762479 := bstep (se 1 (by rfl) ⟨571859, by rfl⟩ : syracuseStep 762479 = 1143719) B1143719
theorem B3318509 : Blo 507795 3318509 := bstep (se 3 (by rfl) ⟨622220, by rfl⟩ : syracuseStep 3318509 = 1244441) B1244441
theorem B763103 : Blo 507795 763103 := bstep (se 1 (by rfl) ⟨572327, by rfl⟩ : syracuseStep 763103 = 1144655) B1144655
theorem B763343 : Blo 507795 763343 := bstep (se 1 (by rfl) ⟨572507, by rfl⟩ : syracuseStep 763343 = 1145015) B1145015
theorem B861691 : Blo 507795 861691 := bstep (se 1 (by rfl) ⟨646268, by rfl⟩ : syracuseStep 861691 = 1292537) B1292537
theorem B1943135 : Blo 507795 1943135 := bstep (se 1 (by rfl) ⟨1457351, by rfl⟩ : syracuseStep 1943135 = 2914703) B2914703
theorem B1287809 : Blo 507795 1287809 := bstep (se 2 (by rfl) ⟨482928, by rfl⟩ : syracuseStep 1287809 = 965857) B965857
theorem B763529 : Blo 507795 763529 := bstep (se 2 (by rfl) ⟨286323, by rfl⟩ : syracuseStep 763529 = 572647) B572647
theorem B763583 : Blo 507795 763583 := bstep (se 1 (by rfl) ⟨572687, by rfl⟩ : syracuseStep 763583 = 1145375) B1145375
theorem B861961 : Blo 507795 861961 := bstep (se 2 (by rfl) ⟨323235, by rfl⟩ : syracuseStep 861961 = 646471) B646471
theorem B763739 : Blo 507795 763739 := bstep (se 1 (by rfl) ⟨572804, by rfl⟩ : syracuseStep 763739 = 1145609) B1145609
theorem B24717473 : Blo 507795 24717473 := bstep (se 2 (by rfl) ⟨9269052, by rfl⟩ : syracuseStep 24717473 = 18538105) B18538105
theorem B764123 : Blo 507795 764123 := bstep (se 1 (by rfl) ⟨573092, by rfl⟩ : syracuseStep 764123 = 1146185) B1146185
theorem B862427 : Blo 507795 862427 := bstep (se 1 (by rfl) ⟨646820, by rfl⟩ : syracuseStep 862427 = 1293641) B1293641
theorem B1288619 : Blo 507795 1288619 := bstep (se 1 (by rfl) ⟨966464, by rfl⟩ : syracuseStep 1288619 = 1932929) B1932929
theorem B1714607 : Blo 507795 1714607 := bstep (se 1 (by rfl) ⟨1285955, by rfl⟩ : syracuseStep 1714607 = 2571911) B2571911
theorem B764393 : Blo 507795 764393 := bstep (se 2 (by rfl) ⟨286647, by rfl⟩ : syracuseStep 764393 = 573295) B573295
theorem B862697 : Blo 507795 862697 := bstep (se 2 (by rfl) ⟨323511, by rfl⟩ : syracuseStep 862697 = 647023) B647023
theorem B764399 : Blo 507795 764399 := bstep (se 1 (by rfl) ⟨573299, by rfl⟩ : syracuseStep 764399 = 1146599) B1146599
theorem B764711 : Blo 507795 764711 := bstep (se 1 (by rfl) ⟨573533, by rfl⟩ : syracuseStep 764711 = 1147067) B1147067
theorem B764783 : Blo 507795 764783 := bstep (se 1 (by rfl) ⟨573587, by rfl⟩ : syracuseStep 764783 = 1147175) B1147175
theorem B765035 : Blo 507795 765035 := bstep (se 1 (by rfl) ⟨573776, by rfl⟩ : syracuseStep 765035 = 1147553) B1147553
theorem B863419 : Blo 507795 863419 := bstep (se 1 (by rfl) ⟨647564, by rfl⟩ : syracuseStep 863419 = 1295129) B1295129
theorem B765275 : Blo 507795 765275 := bstep (se 1 (by rfl) ⟨573956, by rfl⟩ : syracuseStep 765275 = 1147913) B1147913
theorem B765305 : Blo 507795 765305 := bstep (se 2 (by rfl) ⟨286989, by rfl⟩ : syracuseStep 765305 = 573979) B573979
theorem B2796923 : Blo 507795 2796923 := bstep (se 1 (by rfl) ⟨2097692, by rfl⟩ : syracuseStep 2796923 = 4195385) B4195385
theorem B765311 : Blo 507795 765311 := bstep (se 1 (by rfl) ⟨573983, by rfl⟩ : syracuseStep 765311 = 1147967) B1147967
theorem B1715687 : Blo 507795 1715687 := bstep (se 1 (by rfl) ⟨1286765, by rfl⟩ : syracuseStep 1715687 = 2573531) B2573531
theorem B765545 : Blo 507795 765545 := bstep (se 2 (by rfl) ⟨287079, by rfl⟩ : syracuseStep 765545 = 574159) B574159
theorem B1290107 : Blo 507795 1290107 := bstep (se 1 (by rfl) ⟨967580, by rfl⟩ : syracuseStep 1290107 = 1935161) B1935161
theorem B765935 : Blo 507795 765935 := bstep (se 1 (by rfl) ⟨574451, by rfl⟩ : syracuseStep 765935 = 1148903) B1148903
theorem B766055 : Blo 507795 766055 := bstep (se 1 (by rfl) ⟨574541, by rfl⟩ : syracuseStep 766055 = 1149083) B1149083
theorem B766175 : Blo 507795 766175 := bstep (se 1 (by rfl) ⟨574631, by rfl⟩ : syracuseStep 766175 = 1149263) B1149263
theorem B766235 : Blo 507795 766235 := bstep (se 1 (by rfl) ⟨574676, by rfl⟩ : syracuseStep 766235 = 1149353) B1149353
theorem B2175655 : Blo 507795 2175655 := bstep (se 1 (by rfl) ⟨1631741, by rfl⟩ : syracuseStep 2175655 = 3263483) B3263483
theorem B766631 : Blo 507795 766631 := bstep (se 1 (by rfl) ⟨574973, by rfl⟩ : syracuseStep 766631 = 1149947) B1149947
theorem B766751 : Blo 507795 766751 := bstep (se 1 (by rfl) ⟨575063, by rfl⟩ : syracuseStep 766751 = 1150127) B1150127
theorem B766775 : Blo 507795 766775 := bstep (se 1 (by rfl) ⟨575081, by rfl⟩ : syracuseStep 766775 = 1150163) B1150163
theorem B766889 : Blo 507795 766889 := bstep (se 2 (by rfl) ⟨287583, by rfl⟩ : syracuseStep 766889 = 575167) B575167
theorem B766955 : Blo 507795 766955 := bstep (se 1 (by rfl) ⟨575216, by rfl⟩ : syracuseStep 766955 = 1150433) B1150433
theorem B767231 : Blo 507795 767231 := bstep (se 1 (by rfl) ⟨575423, by rfl⟩ : syracuseStep 767231 = 1150847) B1150847
theorem B767273 : Blo 507795 767273 := bstep (se 2 (by rfl) ⟨287727, by rfl⟩ : syracuseStep 767273 = 575455) B575455
theorem B1226267 : Blo 507795 1226267 := bstep (se 1 (by rfl) ⟨919700, by rfl⟩ : syracuseStep 1226267 = 1839401) B1839401
theorem B964315 : Blo 507795 964315 := bstep (se 1 (by rfl) ⟨723236, by rfl⟩ : syracuseStep 964315 = 1446473) B1446473
theorem B1226459 : Blo 507795 1226459 := bstep (se 1 (by rfl) ⟨919844, by rfl⟩ : syracuseStep 1226459 = 1839689) B1839689
theorem B1292051 : Blo 507795 1292051 := bstep (se 1 (by rfl) ⟨969038, by rfl⟩ : syracuseStep 1292051 = 1938077) B1938077
theorem B8730503 : Blo 507795 8730503 := bstep (se 1 (by rfl) ⟨6547877, by rfl⟩ : syracuseStep 8730503 = 13095755) B13095755
theorem B1718171 : Blo 507795 1718171 := bstep (se 1 (by rfl) ⟨1288628, by rfl⟩ : syracuseStep 1718171 = 2577257) B2577257
theorem B964543 : Blo 507795 964543 := bstep (se 1 (by rfl) ⟨723407, by rfl⟩ : syracuseStep 964543 = 1446815) B1446815
theorem B52869131 : Blo 507795 52869131 := bstep (se 1 (by rfl) ⟨39651848, by rfl⟩ : syracuseStep 52869131 = 79303697) B79303697
theorem B571495 : Blo 507795 571495 := bstep (se 1 (by rfl) ⟨428621, by rfl⟩ : syracuseStep 571495 = 857243) B857243
theorem B1292395 : Blo 507795 1292395 := bstep (se 1 (by rfl) ⟨969296, by rfl⟩ : syracuseStep 1292395 = 1938593) B1938593
theorem B3258767 : Blo 507795 3258767 := bstep (se 1 (by rfl) ⟨2444075, by rfl⟩ : syracuseStep 3258767 = 4888151) B4888151
theorem B1292831 : Blo 507795 1292831 := bstep (se 1 (by rfl) ⟨969623, by rfl⟩ : syracuseStep 1292831 = 1939247) B1939247
theorem B3259025 : Blo 507795 3259025 := bstep (se 2 (by rfl) ⟨1222134, by rfl⟩ : syracuseStep 3259025 = 2444269) B2444269
theorem B2570939 : Blo 507795 2570939 := bstep (se 1 (by rfl) ⟨1928204, by rfl⟩ : syracuseStep 2570939 = 3856409) B3856409
theorem B1293043 : Blo 507795 1293043 := bstep (se 1 (by rfl) ⟨969782, by rfl⟩ : syracuseStep 1293043 = 1939565) B1939565
theorem B4406525 : Blo 507795 4406525 := bstep (se 3 (by rfl) ⟨826223, by rfl⟩ : syracuseStep 4406525 = 1652447) B1652447
theorem B2800939 : Blo 507795 2800939 := bstep (se 1 (by rfl) ⟨2100704, by rfl⟩ : syracuseStep 2800939 = 4201409) B4201409
theorem B5815961 : Blo 507795 5815961 := bstep (se 2 (by rfl) ⟨2180985, by rfl⟩ : syracuseStep 5815961 = 4361971) B4361971
theorem B1720061 : Blo 507795 1720061 := bstep (se 3 (by rfl) ⟨322511, by rfl⟩ : syracuseStep 1720061 = 645023) B645023
theorem B1720223 : Blo 507795 1720223 := bstep (se 1 (by rfl) ⟨1290167, by rfl⟩ : syracuseStep 1720223 = 2580335) B2580335
theorem B507807 : Blo 507795 507807 := bstep (se 1 (by rfl) ⟨380855, by rfl⟩ : syracuseStep 507807 = 761711) B761711
theorem B2899871 : Blo 507795 2899871 := bstep (se 1 (by rfl) ⟨2174903, by rfl⟩ : syracuseStep 2899871 = 4349807) B4349807
theorem B2572397 : Blo 507795 2572397 := bstep (se 3 (by rfl) ⟨482324, by rfl⟩ : syracuseStep 2572397 = 964649) B964649
theorem B508263 : Blo 507795 508263 := bstep (se 1 (by rfl) ⟨381197, by rfl⟩ : syracuseStep 508263 = 762395) B762395
theorem B573799 : Blo 507795 573799 := bstep (se 1 (by rfl) ⟨430349, by rfl⟩ : syracuseStep 573799 = 860699) B860699
theorem B4145527 : Blo 507795 4145527 := bstep (se 1 (by rfl) ⟨3109145, by rfl⟩ : syracuseStep 4145527 = 6218291) B6218291
theorem B508383 : Blo 507795 508383 := bstep (se 1 (by rfl) ⟨381287, by rfl⟩ : syracuseStep 508383 = 762575) B762575
theorem B508391 : Blo 507795 508391 := bstep (se 1 (by rfl) ⟨381293, by rfl⟩ : syracuseStep 508391 = 762587) B762587
theorem B3883625 : Blo 507795 3883625 := bstep (se 2 (by rfl) ⟨1456359, by rfl⟩ : syracuseStep 3883625 = 2912719) B2912719
theorem B508667 : Blo 507795 508667 := bstep (se 1 (by rfl) ⟨381500, by rfl⟩ : syracuseStep 508667 = 763001) B763001
theorem B1295099 : Blo 507795 1295099 := bstep (se 1 (by rfl) ⟨971324, by rfl⟩ : syracuseStep 1295099 = 1942649) B1942649
theorem B2901055 : Blo 507795 2901055 := bstep (se 1 (by rfl) ⟨2175791, by rfl⟩ : syracuseStep 2901055 = 4351583) B4351583
theorem B967801 : Blo 507795 967801 := bstep (se 2 (by rfl) ⟨362925, by rfl⟩ : syracuseStep 967801 = 725851) B725851
theorem B509247 : Blo 507795 509247 := bstep (se 1 (by rfl) ⟨381935, by rfl⟩ : syracuseStep 509247 = 763871) B763871
theorem B509255 : Blo 507795 509255 := bstep (se 1 (by rfl) ⟨381941, by rfl⟩ : syracuseStep 509255 = 763883) B763883
theorem B509287 : Blo 507795 509287 := bstep (se 1 (by rfl) ⟨381965, by rfl⟩ : syracuseStep 509287 = 763931) B763931
theorem B509531 : Blo 507795 509531 := bstep (se 1 (by rfl) ⟨382148, by rfl⟩ : syracuseStep 509531 = 764297) B764297
theorem B60311141 : Blo 507795 60311141 := bstep (se 4 (by rfl) ⟨5654169, by rfl⟩ : syracuseStep 60311141 = 11308339) B11308339
theorem B1034047 : Blo 507795 1034047 := bstep (se 1 (by rfl) ⟨775535, by rfl⟩ : syracuseStep 1034047 = 1551071) B1551071
theorem B2443385 : Blo 507795 2443385 := bstep (se 2 (by rfl) ⟨916269, by rfl⟩ : syracuseStep 2443385 = 1832539) B1832539
theorem B510159 : Blo 507795 510159 := bstep (se 1 (by rfl) ⟨382619, by rfl⟩ : syracuseStep 510159 = 765239) B765239
theorem B510271 : Blo 507795 510271 := bstep (se 1 (by rfl) ⟨382703, by rfl⟩ : syracuseStep 510271 = 765407) B765407
theorem B1657151 : Blo 507795 1657151 := bstep (se 1 (by rfl) ⟨1242863, by rfl⟩ : syracuseStep 1657151 = 2485727) B2485727
theorem B510415 : Blo 507795 510415 := bstep (se 1 (by rfl) ⟨382811, by rfl⟩ : syracuseStep 510415 = 765623) B765623
theorem B510555 : Blo 507795 510555 := bstep (se 1 (by rfl) ⟨382916, by rfl⟩ : syracuseStep 510555 = 765833) B765833
theorem B510719 : Blo 507795 510719 := bstep (se 1 (by rfl) ⟨383039, by rfl⟩ : syracuseStep 510719 = 766079) B766079
theorem B969479 : Blo 507795 969479 := bstep (se 1 (by rfl) ⟨727109, by rfl⟩ : syracuseStep 969479 = 1454219) B1454219
theorem B4344749 : Blo 507795 4344749 := bstep (se 3 (by rfl) ⟨814640, by rfl⟩ : syracuseStep 4344749 = 1629281) B1629281
theorem B511143 : Blo 507795 511143 := bstep (se 1 (by rfl) ⟨383357, by rfl⟩ : syracuseStep 511143 = 766715) B766715
theorem B10996955 : Blo 507795 10996955 := bstep (se 1 (by rfl) ⟨8247716, by rfl⟩ : syracuseStep 10996955 = 16495433) B16495433
theorem B511439 : Blo 507795 511439 := bstep (se 1 (by rfl) ⟨383579, by rfl⟩ : syracuseStep 511439 = 767159) B767159
theorem B544367 : Blo 507795 544367 := bstep (se 1 (by rfl) ⟨408275, by rfl⟩ : syracuseStep 544367 = 816551) B816551
theorem B511599 : Blo 507795 511599 := bstep (se 1 (by rfl) ⟨383699, by rfl⟩ : syracuseStep 511599 = 767399) B767399
theorem B511719 : Blo 507795 511719 := bstep (se 1 (by rfl) ⟨383789, by rfl⟩ : syracuseStep 511719 = 767579) B767579
theorem B1528393 : Blo 507795 1528393 := bstep (se 2 (by rfl) ⟨573147, by rfl⟩ : syracuseStep 1528393 = 1146295) B1146295
theorem B645403 : Blo 507795 645403 := bstep (se 1 (by rfl) ⟨484052, by rfl⟩ : syracuseStep 645403 = 968105) B968105
theorem B2185703 : Blo 507795 2185703 := bstep (se 1 (by rfl) ⟨1639277, by rfl⟩ : syracuseStep 2185703 = 3278555) B3278555
theorem B13425209 : Blo 507795 13425209 := bstep (se 2 (by rfl) ⟨5034453, by rfl⟩ : syracuseStep 13425209 = 10068907) B10068907
theorem B2579039 : Blo 507795 2579039 := bstep (se 1 (by rfl) ⟨1934279, by rfl⟩ : syracuseStep 2579039 = 3868559) B3868559
theorem B1727135 : Blo 507795 1727135 := bstep (se 1 (by rfl) ⟨1295351, by rfl⟩ : syracuseStep 1727135 = 2590703) B2590703
theorem B645823 : Blo 507795 645823 := bstep (se 1 (by rfl) ⟨484367, by rfl⟩ : syracuseStep 645823 = 968735) B968735
theorem B1629065 : Blo 507795 1629065 := bstep (se 2 (by rfl) ⟨610899, by rfl⟩ : syracuseStep 1629065 = 1221799) B1221799
theorem B646375 : Blo 507795 646375 := bstep (se 1 (by rfl) ⟨484781, by rfl⟩ : syracuseStep 646375 = 969563) B969563
theorem B613759 : Blo 507795 613759 := bstep (se 1 (by rfl) ⟨460319, by rfl⟩ : syracuseStep 613759 = 920639) B920639
theorem B1400743 : Blo 507795 1400743 := bstep (se 1 (by rfl) ⟨1050557, by rfl⟩ : syracuseStep 1400743 = 2101115) B2101115
theorem B2122247 : Blo 507795 2122247 := bstep (se 1 (by rfl) ⟨1591685, by rfl⟩ : syracuseStep 2122247 = 3183371) B3183371
theorem B5530139 : Blo 507795 5530139 := bstep (se 1 (by rfl) ⟨4147604, by rfl⟩ : syracuseStep 5530139 = 8295209) B8295209
theorem B143123705 : Blo 507795 143123705 := bstep (se 2 (by rfl) ⟨53671389, by rfl⟩ : syracuseStep 143123705 = 107342779) B107342779
theorem B2450843 : Blo 507795 2450843 := bstep (se 1 (by rfl) ⟨1838132, by rfl⟩ : syracuseStep 2450843 = 3676265) B3676265
theorem B2942647 : Blo 507795 2942647 := bstep (se 1 (by rfl) ⟨2206985, by rfl⟩ : syracuseStep 2942647 = 4413971) B4413971
theorem B3270455 : Blo 507795 3270455 := bstep (se 1 (by rfl) ⟨2452841, by rfl⟩ : syracuseStep 3270455 = 4905683) B4905683
theorem B4974803 : Blo 507795 4974803 := bstep (se 1 (by rfl) ⟨3731102, by rfl⟩ : syracuseStep 4974803 = 7462205) B7462205
theorem B3860783 : Blo 507795 3860783 := bstep (se 1 (by rfl) ⟨2895587, by rfl⟩ : syracuseStep 3860783 = 5791175) B5791175
theorem B4418023 : Blo 507795 4418023 := bstep (se 1 (by rfl) ⟨3313517, by rfl⟩ : syracuseStep 4418023 = 6627035) B6627035
theorem B2976641 : Blo 507795 2976641 := bstep (se 2 (by rfl) ⟨1116240, by rfl⟩ : syracuseStep 2976641 = 2232481) B2232481
theorem B6351839 : Blo 507795 6351839 := bstep (se 1 (by rfl) ⟨4763879, by rfl⟩ : syracuseStep 6351839 = 9527759) B9527759
theorem B2125111 : Blo 507795 2125111 := bstep (se 1 (by rfl) ⟨1593833, by rfl⟩ : syracuseStep 2125111 = 3187667) B3187667
theorem B3272147 : Blo 507795 3272147 := bstep (se 1 (by rfl) ⟨2454110, by rfl⟩ : syracuseStep 3272147 = 4908221) B4908221
theorem B12579259 : Blo 507795 12579259 := bstep (se 1 (by rfl) ⟨9434444, by rfl⟩ : syracuseStep 12579259 = 18868889) B18868889
theorem B18641441 : Blo 507795 18641441 := bstep (se 2 (by rfl) ⟨6990540, by rfl⟩ : syracuseStep 18641441 = 13981081) B13981081
theorem B8385113 : Blo 507795 8385113 := bstep (se 2 (by rfl) ⟨3144417, by rfl⟩ : syracuseStep 8385113 = 6288835) B6288835
theorem B5567291 : Blo 507795 5567291 := bstep (se 1 (by rfl) ⟨4175468, by rfl⟩ : syracuseStep 5567291 = 8350937) B8350937
theorem B5502629 : Blo 507795 5502629 := bstep (se 4 (by rfl) ⟨515871, by rfl⟩ : syracuseStep 5502629 = 1031743) B1031743
theorem B2914177 : Blo 507795 2914177 := bstep (se 2 (by rfl) ⟨1092816, by rfl⟩ : syracuseStep 2914177 = 2185633) B2185633
theorem B1144799 : Blo 507795 1144799 := bstep (se 1 (by rfl) ⟨858599, by rfl⟩ : syracuseStep 1144799 = 1717199) B1717199
theorem B1931303 : Blo 507795 1931303 := bstep (se 1 (by rfl) ⟨1448477, by rfl⟩ : syracuseStep 1931303 = 2896955) B2896955
theorem B1144871 : Blo 507795 1144871 := bstep (se 1 (by rfl) ⟨858653, by rfl⟩ : syracuseStep 1144871 = 1717307) B1717307
theorem B2455591 : Blo 507795 2455591 := bstep (se 1 (by rfl) ⟨1841693, by rfl⟩ : syracuseStep 2455591 = 3683387) B3683387
theorem B2914451 : Blo 507795 2914451 := bstep (se 1 (by rfl) ⟨2185838, by rfl⟩ : syracuseStep 2914451 = 4371677) B4371677
theorem B1145051 : Blo 507795 1145051 := bstep (se 1 (by rfl) ⟨858788, by rfl⟩ : syracuseStep 1145051 = 1717577) B1717577
theorem B1145249 : Blo 507795 1145249 := bstep (se 2 (by rfl) ⟨429468, by rfl⟩ : syracuseStep 1145249 = 858937) B858937
theorem B1145321 : Blo 507795 1145321 := bstep (se 2 (by rfl) ⟨429495, by rfl⟩ : syracuseStep 1145321 = 858991) B858991
theorem B8288851 : Blo 507795 8288851 := bstep (se 1 (by rfl) ⟨6216638, by rfl⟩ : syracuseStep 8288851 = 12433277) B12433277
theorem B2587463 : Blo 507795 2587463 := bstep (se 1 (by rfl) ⟨1940597, by rfl⟩ : syracuseStep 2587463 = 3881195) B3881195
theorem B1145951 : Blo 507795 1145951 := bstep (se 1 (by rfl) ⟨859463, by rfl⟩ : syracuseStep 1145951 = 1718927) B1718927
theorem B1932443 : Blo 507795 1932443 := bstep (se 1 (by rfl) ⟨1449332, by rfl⟩ : syracuseStep 1932443 = 2898665) B2898665
theorem B10452239 : Blo 507795 10452239 := bstep (se 1 (by rfl) ⟨7839179, by rfl⟩ : syracuseStep 10452239 = 15678359) B15678359
theorem B1146167 : Blo 507795 1146167 := bstep (se 1 (by rfl) ⟨859625, by rfl⟩ : syracuseStep 1146167 = 1719251) B1719251
theorem B2456993 : Blo 507795 2456993 := bstep (se 2 (by rfl) ⟨921372, by rfl⟩ : syracuseStep 2456993 = 1842745) B1842745
theorem B1146347 : Blo 507795 1146347 := bstep (se 1 (by rfl) ⟨859760, by rfl⟩ : syracuseStep 1146347 = 1719521) B1719521
theorem B1146779 : Blo 507795 1146779 := bstep (se 1 (by rfl) ⟨860084, by rfl⟩ : syracuseStep 1146779 = 1720169) B1720169
theorem B2588921 : Blo 507795 2588921 := bstep (se 2 (by rfl) ⟨970845, by rfl⟩ : syracuseStep 2588921 = 1941691) B1941691
theorem B2589083 : Blo 507795 2589083 := bstep (se 1 (by rfl) ⟨1941812, by rfl⟩ : syracuseStep 2589083 = 3883625) B3883625
theorem B983599 : Blo 507795 983599 := bstep (se 1 (by rfl) ⟨737699, by rfl⟩ : syracuseStep 983599 = 1475399) B1475399
theorem B40207427 : Blo 507795 40207427 := bstep (se 1 (by rfl) ⟨30155570, by rfl⟩ : syracuseStep 40207427 = 60311141) B60311141
theorem B3868073 : Blo 507795 3868073 := bstep (se 2 (by rfl) ⟨1450527, by rfl⟩ : syracuseStep 3868073 = 2901055) B2901055
theorem B1148921 : Blo 507795 1148921 := bstep (se 2 (by rfl) ⟨430845, by rfl⟩ : syracuseStep 1148921 = 861691) B861691
theorem B723163 : Blo 507795 723163 := bstep (se 1 (by rfl) ⟨542372, by rfl⟩ : syracuseStep 723163 = 1084745) B1084745
theorem B1149281 : Blo 507795 1149281 := bstep (se 2 (by rfl) ⟨430980, by rfl⟩ : syracuseStep 1149281 = 861961) B861961
theorem B1378729 : Blo 507795 1378729 := bstep (se 2 (by rfl) ⟨517023, by rfl⟩ : syracuseStep 1378729 = 1034047) B1034047
theorem B2951639 : Blo 507795 2951639 := bstep (se 1 (by rfl) ⟨2213729, by rfl⟩ : syracuseStep 2951639 = 4427459) B4427459
theorem B2035867 : Blo 507795 2035867 := bstep (se 1 (by rfl) ⟨1526900, by rfl⟩ : syracuseStep 2035867 = 3053801) B3053801
theorem B1151225 : Blo 507795 1151225 := bstep (se 2 (by rfl) ⟨431709, by rfl⟩ : syracuseStep 1151225 = 863419) B863419
theorem B8950139 : Blo 507795 8950139 := bstep (se 1 (by rfl) ⟨6712604, by rfl⟩ : syracuseStep 8950139 = 13425209) B13425209
theorem B1151423 : Blo 507795 1151423 := bstep (se 1 (by rfl) ⟨863567, by rfl⟩ : syracuseStep 1151423 = 1727135) B1727135
theorem B1446427 : Blo 507795 1446427 := bstep (se 1 (by rfl) ⟨1084820, by rfl⟩ : syracuseStep 1446427 = 2169641) B2169641
theorem B1086043 : Blo 507795 1086043 := bstep (se 1 (by rfl) ⟨814532, by rfl⟩ : syracuseStep 1086043 = 1629065) B1629065
theorem B857351 : Blo 507795 857351 := bstep (se 1 (by rfl) ⟨643013, by rfl⟩ : syracuseStep 857351 = 1286027) B1286027
theorem B14751179 : Blo 507795 14751179 := bstep (se 1 (by rfl) ⟨11063384, by rfl⟩ : syracuseStep 14751179 = 22126769) B22126769
theorem B7869919 : Blo 507795 7869919 := bstep (se 1 (by rfl) ⟨5902439, by rfl⟩ : syracuseStep 7869919 = 11804879) B11804879
theorem B1414831 : Blo 507795 1414831 := bstep (se 1 (by rfl) ⟨1061123, by rfl⟩ : syracuseStep 1414831 = 2122247) B2122247
theorem B1939261 : Blo 507795 1939261 := bstep (se 3 (by rfl) ⟨363611, by rfl⟩ : syracuseStep 1939261 = 727223) B727223
theorem B2037857 : Blo 507795 2037857 := bstep (se 2 (by rfl) ⟨764196, by rfl⟩ : syracuseStep 2037857 = 1528393) B1528393
theorem B858539 : Blo 507795 858539 := bstep (se 1 (by rfl) ⟨643904, by rfl⟩ : syracuseStep 858539 = 1287809) B1287809
theorem B1448729 : Blo 507795 1448729 := bstep (se 2 (by rfl) ⟨543273, by rfl⟩ : syracuseStep 1448729 = 1086547) B1086547
theorem B3316535 : Blo 507795 3316535 := bstep (se 1 (by rfl) ⟨2487401, by rfl⟩ : syracuseStep 3316535 = 4974803) B4974803
theorem B859079 : Blo 507795 859079 := bstep (se 1 (by rfl) ⟨644309, by rfl⟩ : syracuseStep 859079 = 1288619) B1288619
theorem B4234559 : Blo 507795 4234559 := bstep (se 1 (by rfl) ⟨3175919, by rfl⟩ : syracuseStep 4234559 = 6351839) B6351839
theorem B1285753 : Blo 507795 1285753 := bstep (se 2 (by rfl) ⟨482157, by rfl⟩ : syracuseStep 1285753 = 964315) B964315
theorem B860071 : Blo 507795 860071 := bstep (se 1 (by rfl) ⟨645053, by rfl⟩ : syracuseStep 860071 = 1290107) B1290107
theorem B1286057 : Blo 507795 1286057 := bstep (se 2 (by rfl) ⟨482271, by rfl⟩ : syracuseStep 1286057 = 964543) B964543
theorem B761993 : Blo 507795 761993 := bstep (se 2 (by rfl) ⟨285747, by rfl⟩ : syracuseStep 761993 = 571495) B571495
theorem B12427627 : Blo 507795 12427627 := bstep (se 1 (by rfl) ⟨9320720, by rfl⟩ : syracuseStep 12427627 = 18641441) B18641441
theorem B860537 : Blo 507795 860537 := bstep (se 2 (by rfl) ⟨322701, by rfl⟩ : syracuseStep 860537 = 645403) B645403
theorem B3711527 : Blo 507795 3711527 := bstep (se 1 (by rfl) ⟨2783645, by rfl⟩ : syracuseStep 3711527 = 5567291) B5567291
theorem B11051801 : Blo 507795 11051801 := bstep (se 2 (by rfl) ⟨4144425, by rfl⟩ : syracuseStep 11051801 = 8288851) B8288851
theorem B861097 : Blo 507795 861097 := bstep (se 2 (by rfl) ⟨322911, by rfl⟩ : syracuseStep 861097 = 645823) B645823
theorem B861367 : Blo 507795 861367 := bstep (se 1 (by rfl) ⟨646025, by rfl⟩ : syracuseStep 861367 = 1292051) B1292051
theorem B1844477 : Blo 507795 1844477 := bstep (se 3 (by rfl) ⟨345839, by rfl⟩ : syracuseStep 1844477 = 691679) B691679
theorem B2762041 : Blo 507795 2762041 := bstep (se 2 (by rfl) ⟨1035765, by rfl⟩ : syracuseStep 2762041 = 2071531) B2071531
theorem B763199 : Blo 507795 763199 := bstep (se 1 (by rfl) ⟨572399, by rfl⟩ : syracuseStep 763199 = 1144799) B1144799
theorem B1287535 : Blo 507795 1287535 := bstep (se 1 (by rfl) ⟨965651, by rfl⟩ : syracuseStep 1287535 = 1931303) B1931303
theorem B763247 : Blo 507795 763247 := bstep (se 1 (by rfl) ⟨572435, by rfl⟩ : syracuseStep 763247 = 1144871) B1144871
theorem B1942967 : Blo 507795 1942967 := bstep (se 1 (by rfl) ⟨1457225, by rfl⟩ : syracuseStep 1942967 = 2914451) B2914451
theorem B763367 : Blo 507795 763367 := bstep (se 1 (by rfl) ⟨572525, by rfl⟩ : syracuseStep 763367 = 1145051) B1145051
theorem B2172511 : Blo 507795 2172511 := bstep (se 1 (by rfl) ⟨1629383, by rfl⟩ : syracuseStep 2172511 = 3258767) B3258767
theorem B763499 : Blo 507795 763499 := bstep (se 1 (by rfl) ⟨572624, by rfl⟩ : syracuseStep 763499 = 1145249) B1145249
theorem B1451645 : Blo 507795 1451645 := bstep (se 3 (by rfl) ⟨272183, by rfl⟩ : syracuseStep 1451645 = 544367) B544367
theorem B861833 : Blo 507795 861833 := bstep (se 2 (by rfl) ⟨323187, by rfl⟩ : syracuseStep 861833 = 646375) B646375
theorem B763547 : Blo 507795 763547 := bstep (se 1 (by rfl) ⟨572660, by rfl⟩ : syracuseStep 763547 = 1145321) B1145321
theorem B861887 : Blo 507795 861887 := bstep (se 1 (by rfl) ⟨646415, by rfl⟩ : syracuseStep 861887 = 1292831) B1292831
theorem B2172683 : Blo 507795 2172683 := bstep (se 1 (by rfl) ⟨1629512, by rfl⟩ : syracuseStep 2172683 = 3259025) B3259025
theorem B1713959 : Blo 507795 1713959 := bstep (se 1 (by rfl) ⟨1285469, by rfl⟩ : syracuseStep 1713959 = 2570939) B2570939
theorem B763967 : Blo 507795 763967 := bstep (se 1 (by rfl) ⟨572975, by rfl⟩ : syracuseStep 763967 = 1145951) B1145951
theorem B1288295 : Blo 507795 1288295 := bstep (se 1 (by rfl) ⟨966221, by rfl⟩ : syracuseStep 1288295 = 1932443) B1932443
theorem B764111 : Blo 507795 764111 := bstep (se 1 (by rfl) ⟨573083, by rfl⟩ : syracuseStep 764111 = 1146167) B1146167
theorem B764231 : Blo 507795 764231 := bstep (se 1 (by rfl) ⟨573173, by rfl⟩ : syracuseStep 764231 = 1146347) B1146347
theorem B3877307 : Blo 507795 3877307 := bstep (se 1 (by rfl) ⟨2907980, by rfl⟩ : syracuseStep 3877307 = 5815961) B5815961
theorem B764519 : Blo 507795 764519 := bstep (se 1 (by rfl) ⟨573389, by rfl⟩ : syracuseStep 764519 = 1146779) B1146779
theorem B1714931 : Blo 507795 1714931 := bstep (se 1 (by rfl) ⟨1286198, by rfl⟩ : syracuseStep 1714931 = 2572397) B2572397
theorem B1714985 : Blo 507795 1714985 := bstep (se 2 (by rfl) ⟨643119, by rfl⟩ : syracuseStep 1714985 = 1286239) B1286239
theorem B1092475 : Blo 507795 1092475 := bstep (se 1 (by rfl) ⟨819356, by rfl⟩ : syracuseStep 1092475 = 1638713) B1638713
theorem B765065 : Blo 507795 765065 := bstep (se 2 (by rfl) ⟨286899, by rfl⟩ : syracuseStep 765065 = 573799) B573799
theorem B863399 : Blo 507795 863399 := bstep (se 1 (by rfl) ⟨647549, by rfl⟩ : syracuseStep 863399 = 1295099) B1295099
theorem B765119 : Blo 507795 765119 := bstep (se 1 (by rfl) ⟨573839, by rfl⟩ : syracuseStep 765119 = 1147679) B1147679
theorem B6532811 : Blo 507795 6532811 := bstep (se 1 (by rfl) ⟨4899608, by rfl⟩ : syracuseStep 6532811 = 9799217) B9799217
theorem B1290401 : Blo 507795 1290401 := bstep (se 2 (by rfl) ⟨483900, by rfl⟩ : syracuseStep 1290401 = 967801) B967801
theorem B1225057 : Blo 507795 1225057 := bstep (se 2 (by rfl) ⟨459396, by rfl⟩ : syracuseStep 1225057 = 918793) B918793
theorem B2798135 : Blo 507795 2798135 := bstep (se 1 (by rfl) ⟨2098601, by rfl⟩ : syracuseStep 2798135 = 4197203) B4197203
theorem B2896499 : Blo 507795 2896499 := bstep (se 1 (by rfl) ⟨2172374, by rfl⟩ : syracuseStep 2896499 = 4344749) B4344749
theorem B29406401 : Blo 507795 29406401 := bstep (se 2 (by rfl) ⟨11027400, by rfl⟩ : syracuseStep 29406401 = 22054801) B22054801
theorem B767303 : Blo 507795 767303 := bstep (se 1 (by rfl) ⟨575477, by rfl⟩ : syracuseStep 767303 = 1150955) B1150955
theorem B9811975 : Blo 507795 9811975 := bstep (se 1 (by rfl) ⟨7358981, by rfl⟩ : syracuseStep 9811975 = 14717963) B14717963
theorem B571675 : Blo 507795 571675 := bstep (se 1 (by rfl) ⟨428756, by rfl⟩ : syracuseStep 571675 = 857513) B857513
theorem B571711 : Blo 507795 571711 := bstep (se 1 (by rfl) ⟨428783, by rfl⟩ : syracuseStep 571711 = 857567) B857567
theorem B1457135 : Blo 507795 1457135 := bstep (se 1 (by rfl) ⟨1092851, by rfl⟩ : syracuseStep 1457135 = 2185703) B2185703
theorem B1719359 : Blo 507795 1719359 := bstep (se 1 (by rfl) ⟨1289519, by rfl⟩ : syracuseStep 1719359 = 2579039) B2579039
theorem B2833481 : Blo 507795 2833481 := bstep (se 2 (by rfl) ⟨1062555, by rfl⟩ : syracuseStep 2833481 = 2125111) B2125111
theorem B507887 : Blo 507795 507887 := bstep (se 1 (by rfl) ⟨380915, by rfl⟩ : syracuseStep 507887 = 761831) B761831
theorem B1294319 : Blo 507795 1294319 := bstep (se 1 (by rfl) ⟨970739, by rfl⟩ : syracuseStep 1294319 = 1941479) B1941479
theorem B966647 : Blo 507795 966647 := bstep (se 1 (by rfl) ⟨724985, by rfl⟩ : syracuseStep 966647 = 1449971) B1449971
theorem B507967 : Blo 507795 507967 := bstep (se 1 (by rfl) ⟨380975, by rfl⟩ : syracuseStep 507967 = 761951) B761951
theorem B508007 : Blo 507795 508007 := bstep (se 1 (by rfl) ⟨381005, by rfl⟩ : syracuseStep 508007 = 762011) B762011
theorem B508063 : Blo 507795 508063 := bstep (se 1 (by rfl) ⟨381047, by rfl⟩ : syracuseStep 508063 = 762095) B762095
theorem B3686759 : Blo 507795 3686759 := bstep (se 1 (by rfl) ⟨2765069, by rfl⟩ : syracuseStep 3686759 = 5530139) B5530139
theorem B967049 : Blo 507795 967049 := bstep (se 2 (by rfl) ⟨362643, by rfl⟩ : syracuseStep 967049 = 725287) B725287
theorem B508315 : Blo 507795 508315 := bstep (se 1 (by rfl) ⟨381236, by rfl⟩ : syracuseStep 508315 = 762473) B762473
theorem B508319 : Blo 507795 508319 := bstep (se 1 (by rfl) ⟨381239, by rfl⟩ : syracuseStep 508319 = 762479) B762479
theorem B2212339 : Blo 507795 2212339 := bstep (se 1 (by rfl) ⟨1659254, by rfl⟩ : syracuseStep 2212339 = 3318509) B3318509
theorem B508735 : Blo 507795 508735 := bstep (se 1 (by rfl) ⟨381551, by rfl⟩ : syracuseStep 508735 = 763103) B763103
theorem B2900873 : Blo 507795 2900873 := bstep (se 2 (by rfl) ⟨1087827, by rfl⟩ : syracuseStep 2900873 = 2175655) B2175655
theorem B508895 : Blo 507795 508895 := bstep (se 1 (by rfl) ⟨381671, by rfl⟩ : syracuseStep 508895 = 763343) B763343
theorem B1295423 : Blo 507795 1295423 := bstep (se 1 (by rfl) ⟨971567, by rfl⟩ : syracuseStep 1295423 = 1943135) B1943135
theorem B509019 : Blo 507795 509019 := bstep (se 1 (by rfl) ⟨381764, by rfl⟩ : syracuseStep 509019 = 763529) B763529
theorem B509055 : Blo 507795 509055 := bstep (se 1 (by rfl) ⟨381791, by rfl⟩ : syracuseStep 509055 = 763583) B763583
theorem B2180303 : Blo 507795 2180303 := bstep (se 1 (by rfl) ⟨1635227, by rfl⟩ : syracuseStep 2180303 = 3270455) B3270455
theorem B509159 : Blo 507795 509159 := bstep (se 1 (by rfl) ⟨381869, by rfl⟩ : syracuseStep 509159 = 763739) B763739
theorem B509415 : Blo 507795 509415 := bstep (se 1 (by rfl) ⟨382061, by rfl⟩ : syracuseStep 509415 = 764123) B764123
theorem B574951 : Blo 507795 574951 := bstep (se 1 (by rfl) ⟨431213, by rfl⟩ : syracuseStep 574951 = 862427) B862427
theorem B2573855 : Blo 507795 2573855 := bstep (se 1 (by rfl) ⟨1930391, by rfl⟩ : syracuseStep 2573855 = 3860783) B3860783
theorem B509595 : Blo 507795 509595 := bstep (se 1 (by rfl) ⟨382196, by rfl⟩ : syracuseStep 509595 = 764393) B764393
theorem B575131 : Blo 507795 575131 := bstep (se 1 (by rfl) ⟨431348, by rfl⟩ : syracuseStep 575131 = 862697) B862697
theorem B509599 : Blo 507795 509599 := bstep (se 1 (by rfl) ⟨382199, by rfl⟩ : syracuseStep 509599 = 764399) B764399
theorem B509807 : Blo 507795 509807 := bstep (se 1 (by rfl) ⟨382355, by rfl⟩ : syracuseStep 509807 = 764711) B764711
theorem B509855 : Blo 507795 509855 := bstep (se 1 (by rfl) ⟨382391, by rfl⟩ : syracuseStep 509855 = 764783) B764783
theorem B1984427 : Blo 507795 1984427 := bstep (se 1 (by rfl) ⟨1488320, by rfl⟩ : syracuseStep 1984427 = 2976641) B2976641
theorem B510023 : Blo 507795 510023 := bstep (se 1 (by rfl) ⟨382517, by rfl⟩ : syracuseStep 510023 = 765035) B765035
theorem B510183 : Blo 507795 510183 := bstep (se 1 (by rfl) ⟨382637, by rfl⟩ : syracuseStep 510183 = 765275) B765275
theorem B510203 : Blo 507795 510203 := bstep (se 1 (by rfl) ⟨382652, by rfl⟩ : syracuseStep 510203 = 765305) B765305
theorem B510207 : Blo 507795 510207 := bstep (se 1 (by rfl) ⟨382655, by rfl⟩ : syracuseStep 510207 = 765311) B765311
theorem B2181431 : Blo 507795 2181431 := bstep (se 1 (by rfl) ⟨1636073, by rfl⟩ : syracuseStep 2181431 = 3272147) B3272147
theorem B510363 : Blo 507795 510363 := bstep (se 1 (by rfl) ⟨382772, by rfl⟩ : syracuseStep 510363 = 765545) B765545
theorem B3885569 : Blo 507795 3885569 := bstep (se 2 (by rfl) ⟨1457088, by rfl⟩ : syracuseStep 3885569 = 2914177) B2914177
theorem B510623 : Blo 507795 510623 := bstep (se 1 (by rfl) ⟨382967, by rfl⟩ : syracuseStep 510623 = 765935) B765935
theorem B510703 : Blo 507795 510703 := bstep (se 1 (by rfl) ⟨383027, by rfl⟩ : syracuseStep 510703 = 766055) B766055
theorem B1723193 : Blo 507795 1723193 := bstep (se 2 (by rfl) ⟨646197, by rfl⟩ : syracuseStep 1723193 = 1292395) B1292395
theorem B510783 : Blo 507795 510783 := bstep (se 1 (by rfl) ⟨383087, by rfl⟩ : syracuseStep 510783 = 766175) B766175
theorem B510823 : Blo 507795 510823 := bstep (se 1 (by rfl) ⟨383117, by rfl⟩ : syracuseStep 510823 = 766235) B766235
theorem B5590075 : Blo 507795 5590075 := bstep (se 1 (by rfl) ⟨4192556, by rfl⟩ : syracuseStep 5590075 = 8385113) B8385113
theorem B511087 : Blo 507795 511087 := bstep (se 1 (by rfl) ⟨383315, by rfl⟩ : syracuseStep 511087 = 766631) B766631
theorem B511167 : Blo 507795 511167 := bstep (se 1 (by rfl) ⟨383375, by rfl⟩ : syracuseStep 511167 = 766751) B766751
theorem B511183 : Blo 507795 511183 := bstep (se 1 (by rfl) ⟨383387, by rfl⟩ : syracuseStep 511183 = 766775) B766775
theorem B511259 : Blo 507795 511259 := bstep (se 1 (by rfl) ⟨383444, by rfl⟩ : syracuseStep 511259 = 766889) B766889
theorem B511303 : Blo 507795 511303 := bstep (se 1 (by rfl) ⟨383477, by rfl⟩ : syracuseStep 511303 = 766955) B766955
theorem B511487 : Blo 507795 511487 := bstep (se 1 (by rfl) ⟨383615, by rfl⟩ : syracuseStep 511487 = 767231) B767231
theorem B511515 : Blo 507795 511515 := bstep (se 1 (by rfl) ⟨383636, by rfl⟩ : syracuseStep 511515 = 767273) B767273
theorem B1724057 : Blo 507795 1724057 := bstep (se 2 (by rfl) ⟨646521, by rfl⟩ : syracuseStep 1724057 = 1293043) B1293043
theorem B5820335 : Blo 507795 5820335 := bstep (se 1 (by rfl) ⟨4365251, by rfl⟩ : syracuseStep 5820335 = 8730503) B8730503
theorem B35246087 : Blo 507795 35246087 := bstep (se 1 (by rfl) ⟨26434565, by rfl⟩ : syracuseStep 35246087 = 52869131) B52869131
theorem B1724975 : Blo 507795 1724975 := bstep (se 1 (by rfl) ⟨1293731, by rfl⟩ : syracuseStep 1724975 = 2587463) B2587463
theorem B2937683 : Blo 507795 2937683 := bstep (se 1 (by rfl) ⟨2203262, by rfl⟩ : syracuseStep 2937683 = 4406525) B4406525
theorem B6968159 : Blo 507795 6968159 := bstep (se 1 (by rfl) ⟨5226119, by rfl⟩ : syracuseStep 6968159 = 10452239) B10452239
theorem B2446843 : Blo 507795 2446843 := bstep (se 1 (by rfl) ⟨1835132, by rfl⟩ : syracuseStep 2446843 = 3670265) B3670265
theorem B5527369 : Blo 507795 5527369 := bstep (se 2 (by rfl) ⟨2072763, by rfl⟩ : syracuseStep 5527369 = 4145527) B4145527
theorem B1726811 : Blo 507795 1726811 := bstep (se 1 (by rfl) ⟨1295108, by rfl⟩ : syracuseStep 1726811 = 2590217) B2590217
theorem B2316883 : Blo 507795 2316883 := bstep (se 1 (by rfl) ⟨1737662, by rfl⟩ : syracuseStep 2316883 = 3475325) B3475325
theorem B1628923 : Blo 507795 1628923 := bstep (se 1 (by rfl) ⟨1221692, by rfl⟩ : syracuseStep 1628923 = 2443385) B2443385
theorem B1104767 : Blo 507795 1104767 := bstep (se 1 (by rfl) ⟨828575, by rfl⟩ : syracuseStep 1104767 = 1657151) B1657151
theorem B646319 : Blo 507795 646319 := bstep (se 1 (by rfl) ⟨484739, by rfl⟩ : syracuseStep 646319 = 969479) B969479
theorem B7331303 : Blo 507795 7331303 := bstep (se 1 (by rfl) ⟨5498477, by rfl⟩ : syracuseStep 7331303 = 10996955) B10996955
theorem B5890697 : Blo 507795 5890697 := bstep (se 2 (by rfl) ⟨2209011, by rfl⟩ : syracuseStep 5890697 = 4418023) B4418023
theorem B3859325 : Blo 507795 3859325 := bstep (se 3 (by rfl) ⟨723623, by rfl⟩ : syracuseStep 3859325 = 1447247) B1447247
theorem B3270557 : Blo 507795 3270557 := bstep (se 3 (by rfl) ⟨613229, by rfl⟩ : syracuseStep 3270557 = 1226459) B1226459
theorem B6187691 : Blo 507795 6187691 := bstep (se 1 (by rfl) ⟨4640768, by rfl⟩ : syracuseStep 6187691 = 9281537) B9281537
theorem B16772345 : Blo 507795 16772345 := bstep (se 2 (by rfl) ⟨6289629, by rfl⟩ : syracuseStep 16772345 = 12579259) B12579259
theorem B95415803 : Blo 507795 95415803 := bstep (se 1 (by rfl) ⟨71561852, by rfl⟩ : syracuseStep 95415803 = 143123705) B143123705
theorem B1633895 : Blo 507795 1633895 := bstep (se 1 (by rfl) ⟨1225421, by rfl⟩ : syracuseStep 1633895 = 2450843) B2450843
theorem B16478315 : Blo 507795 16478315 := bstep (se 1 (by rfl) ⟨12358736, by rfl⟩ : syracuseStep 16478315 = 24717473) B24717473
theorem B1143071 : Blo 507795 1143071 := bstep (se 1 (by rfl) ⟨857303, by rfl⟩ : syracuseStep 1143071 = 1714607) B1714607
theorem B1864615 : Blo 507795 1864615 := bstep (se 1 (by rfl) ⟨1398461, by rfl⟩ : syracuseStep 1864615 = 2796923) B2796923
theorem B1143791 : Blo 507795 1143791 := bstep (se 1 (by rfl) ⟨857843, by rfl⟩ : syracuseStep 1143791 = 1715687) B1715687
theorem B9794753 : Blo 507795 9794753 := bstep (se 2 (by rfl) ⟨3673032, by rfl⟩ : syracuseStep 9794753 = 7346065) B7346065
theorem B3274121 : Blo 507795 3274121 := bstep (se 2 (by rfl) ⟨1227795, by rfl⟩ : syracuseStep 3274121 = 2455591) B2455591
theorem B1930985 : Blo 507795 1930985 := bstep (se 2 (by rfl) ⟨724119, by rfl⟩ : syracuseStep 1930985 = 1448239) B1448239
theorem B15694117 : Blo 507795 15694117 := bstep (se 4 (by rfl) ⟨1471323, by rfl⟩ : syracuseStep 15694117 = 2942647) B2942647
theorem B2586977 : Blo 507795 2586977 := bstep (se 2 (by rfl) ⟨970116, by rfl⟩ : syracuseStep 2586977 = 1940233) B1940233
theorem B817511 : Blo 507795 817511 := bstep (se 1 (by rfl) ⟨613133, by rfl⟩ : syracuseStep 817511 = 1226267) B1226267
theorem B3668419 : Blo 507795 3668419 := bstep (se 1 (by rfl) ⟨2751314, by rfl⟩ : syracuseStep 3668419 = 5502629) B5502629
theorem B1145447 : Blo 507795 1145447 := bstep (se 1 (by rfl) ⟨859085, by rfl⟩ : syracuseStep 1145447 = 1718171) B1718171
theorem B3734585 : Blo 507795 3734585 := bstep (se 2 (by rfl) ⟨1400469, by rfl⟩ : syracuseStep 3734585 = 2800939) B2800939
theorem B818345 : Blo 507795 818345 := bstep (se 2 (by rfl) ⟨306879, by rfl⟩ : syracuseStep 818345 = 613759) B613759
theorem B1637995 : Blo 507795 1637995 := bstep (se 1 (by rfl) ⟨1228496, by rfl⟩ : syracuseStep 1637995 = 2456993) B2456993
theorem B1146707 : Blo 507795 1146707 := bstep (se 1 (by rfl) ⟨860030, by rfl⟩ : syracuseStep 1146707 = 1720061) B1720061
theorem B1867657 : Blo 507795 1867657 := bstep (se 2 (by rfl) ⟨700371, by rfl⟩ : syracuseStep 1867657 = 1400743) B1400743
theorem B1933247 : Blo 507795 1933247 := bstep (se 1 (by rfl) ⟨1449935, by rfl⟩ : syracuseStep 1933247 = 2899871) B2899871
theorem B1146815 : Blo 507795 1146815 := bstep (se 1 (by rfl) ⟨860111, by rfl⟩ : syracuseStep 1146815 = 1720223) B1720223
theorem B2457839 : Blo 507795 2457839 := bstep (se 1 (by rfl) ⟨1843379, by rfl⟩ : syracuseStep 2457839 = 3686759) B3686759
theorem B1933915 : Blo 507795 1933915 := bstep (se 1 (by rfl) ⟨1450436, by rfl⟩ : syracuseStep 1933915 = 2900873) B2900873
theorem B2949785 : Blo 507795 2949785 := bstep (se 2 (by rfl) ⟨1106169, by rfl⟩ : syracuseStep 2949785 = 2212339) B2212339
theorem B26804951 : Blo 507795 26804951 := bstep (se 1 (by rfl) ⟨20103713, by rfl⟩ : syracuseStep 26804951 = 40207427) B40207427
theorem B1148129 : Blo 507795 1148129 := bstep (se 2 (by rfl) ⟨430548, by rfl⟩ : syracuseStep 1148129 = 861097) B861097
theorem B1148489 : Blo 507795 1148489 := bstep (se 2 (by rfl) ⟨430683, by rfl⟩ : syracuseStep 1148489 = 861367) B861367
theorem B1967759 : Blo 507795 1967759 := bstep (se 1 (by rfl) ⟨1475819, by rfl⟩ : syracuseStep 1967759 = 2951639) B2951639
theorem B2590379 : Blo 507795 2590379 := bstep (se 1 (by rfl) ⟨1942784, by rfl⟩ : syracuseStep 2590379 = 3885569) B3885569
theorem B1148795 : Blo 507795 1148795 := bstep (se 1 (by rfl) ⟨861596, by rfl⟩ : syracuseStep 1148795 = 1723193) B1723193
theorem B19564901 : Blo 507795 19564901 := bstep (se 4 (by rfl) ⟨1834209, by rfl⟩ : syracuseStep 19564901 = 3668419) B3668419
theorem B1149371 : Blo 507795 1149371 := bstep (se 1 (by rfl) ⟨862028, by rfl⟩ : syracuseStep 1149371 = 1724057) B1724057
theorem B23497391 : Blo 507795 23497391 := bstep (se 1 (by rfl) ⟨17623043, by rfl⟩ : syracuseStep 23497391 = 35246087) B35246087
theorem B5966759 : Blo 507795 5966759 := bstep (se 1 (by rfl) ⟨4475069, by rfl⟩ : syracuseStep 5966759 = 8950139) B8950139
theorem B1149983 : Blo 507795 1149983 := bstep (se 1 (by rfl) ⟨862487, by rfl⟩ : syracuseStep 1149983 = 1724975) B1724975
theorem B1838305 : Blo 507795 1838305 := bstep (se 2 (by rfl) ⟨689364, by rfl⟩ : syracuseStep 1838305 = 1378729) B1378729
theorem B9834119 : Blo 507795 9834119 := bstep (se 1 (by rfl) ⟨7375589, by rfl⟩ : syracuseStep 9834119 = 14751179) B14751179
theorem B1151207 : Blo 507795 1151207 := bstep (se 1 (by rfl) ⟨863405, by rfl⟩ : syracuseStep 1151207 = 1726811) B1726811
theorem B4887535 : Blo 507795 4887535 := bstep (se 1 (by rfl) ⟨3665651, by rfl⟩ : syracuseStep 4887535 = 7331303) B7331303
theorem B857371 : Blo 507795 857371 := bstep (se 1 (by rfl) ⟨643028, by rfl⟩ : syracuseStep 857371 = 1286057) B1286057
theorem B1448057 : Blo 507795 1448057 := bstep (se 2 (by rfl) ⟨543021, by rfl⟩ : syracuseStep 1448057 = 1086043) B1086043
theorem B1448455 : Blo 507795 1448455 := bstep (se 1 (by rfl) ⟨1086341, by rfl⟩ : syracuseStep 1448455 = 2172683) B2172683
theorem B858863 : Blo 507795 858863 := bstep (se 1 (by rfl) ⟨644147, by rfl⟩ : syracuseStep 858863 = 1288295) B1288295
theorem B10493225 : Blo 507795 10493225 := bstep (se 2 (by rfl) ⟨3934959, by rfl⟩ : syracuseStep 10493225 = 7869919) B7869919
theorem B11181563 : Blo 507795 11181563 := bstep (se 1 (by rfl) ⟨8386172, by rfl⟩ : syracuseStep 11181563 = 16772345) B16772345
theorem B63610535 : Blo 507795 63610535 := bstep (se 1 (by rfl) ⟨47707901, by rfl⟩ : syracuseStep 63610535 = 95415803) B95415803
theorem B1089263 : Blo 507795 1089263 := bstep (se 1 (by rfl) ⟨816947, by rfl⟩ : syracuseStep 1089263 = 1633895) B1633895
theorem B13082633 : Blo 507795 13082633 := bstep (se 2 (by rfl) ⟨4905987, by rfl⟩ : syracuseStep 13082633 = 9811975) B9811975
theorem B10985543 : Blo 507795 10985543 := bstep (se 1 (by rfl) ⟨8239157, by rfl⟩ : syracuseStep 10985543 = 16478315) B16478315
theorem B860267 : Blo 507795 860267 := bstep (se 1 (by rfl) ⟨645200, by rfl⟩ : syracuseStep 860267 = 1290401) B1290401
theorem B762047 : Blo 507795 762047 := bstep (se 1 (by rfl) ⟨571535, by rfl⟩ : syracuseStep 762047 = 1143071) B1143071
theorem B762233 : Blo 507795 762233 := bstep (se 2 (by rfl) ⟨285837, by rfl⟩ : syracuseStep 762233 = 571675) B571675
theorem B762281 : Blo 507795 762281 := bstep (se 2 (by rfl) ⟨285855, by rfl⟩ : syracuseStep 762281 = 571711) B571711
theorem B762527 : Blo 507795 762527 := bstep (se 1 (by rfl) ⟨571895, by rfl⟩ : syracuseStep 762527 = 1143791) B1143791
theorem B3089177 : Blo 507795 3089177 := bstep (se 2 (by rfl) ⟨1158441, by rfl⟩ : syracuseStep 3089177 = 2316883) B2316883
theorem B6529835 : Blo 507795 6529835 := bstep (se 1 (by rfl) ⟨4897376, by rfl⟩ : syracuseStep 6529835 = 9794753) B9794753
theorem B19604267 : Blo 507795 19604267 := bstep (se 1 (by rfl) ⟨14703200, by rfl⟩ : syracuseStep 19604267 = 29406401) B29406401
theorem B2171897 : Blo 507795 2171897 := bstep (se 2 (by rfl) ⟨814461, by rfl⟩ : syracuseStep 2171897 = 1628923) B1628923
theorem B1287323 : Blo 507795 1287323 := bstep (se 1 (by rfl) ⟨965492, by rfl⟩ : syracuseStep 1287323 = 1930985) B1930985
theorem B763631 : Blo 507795 763631 := bstep (se 1 (by rfl) ⟨572723, by rfl⟩ : syracuseStep 763631 = 1145447) B1145447
theorem B1714337 : Blo 507795 1714337 := bstep (se 2 (by rfl) ⟨642876, by rfl⟩ : syracuseStep 1714337 = 1285753) B1285753
theorem B764471 : Blo 507795 764471 := bstep (se 1 (by rfl) ⟨573353, by rfl⟩ : syracuseStep 764471 = 1146707) B1146707
theorem B1288831 : Blo 507795 1288831 := bstep (se 1 (by rfl) ⟨966623, by rfl⟩ : syracuseStep 1288831 = 1933247) B1933247
theorem B764543 : Blo 507795 764543 := bstep (se 1 (by rfl) ⟨573407, by rfl⟩ : syracuseStep 764543 = 1146815) B1146815
theorem B862879 : Blo 507795 862879 := bstep (se 1 (by rfl) ⟨647159, by rfl⟩ : syracuseStep 862879 = 1294319) B1294319
theorem B863615 : Blo 507795 863615 := bstep (se 1 (by rfl) ⟨647711, by rfl⟩ : syracuseStep 863615 = 1295423) B1295423
theorem B1453535 : Blo 507795 1453535 := bstep (se 1 (by rfl) ⟨1090151, by rfl⟩ : syracuseStep 1453535 = 2180303) B2180303
theorem B20983445 : Blo 507795 20983445 := bstep (se 6 (by rfl) ⟨491799, by rfl⟩ : syracuseStep 20983445 = 983599) B983599
theorem B1715903 : Blo 507795 1715903 := bstep (se 1 (by rfl) ⟨1286927, by rfl⟩ : syracuseStep 1715903 = 2573855) B2573855
theorem B1322951 : Blo 507795 1322951 := bstep (se 1 (by rfl) ⟨992213, by rfl⟩ : syracuseStep 1322951 = 1984427) B1984427
theorem B765947 : Blo 507795 765947 := bstep (se 1 (by rfl) ⟨574460, by rfl⟩ : syracuseStep 765947 = 1148921) B1148921
theorem B83701957 : Blo 507795 83701957 := bstep (se 4 (by rfl) ⟨7847058, by rfl⟩ : syracuseStep 83701957 = 15694117) B15694117
theorem B1454287 : Blo 507795 1454287 := bstep (se 1 (by rfl) ⟨1090715, by rfl⟩ : syracuseStep 1454287 = 2181431) B2181431
theorem B766187 : Blo 507795 766187 := bstep (se 1 (by rfl) ⟨574640, by rfl⟩ : syracuseStep 766187 = 1149281) B1149281
theorem B3682721 : Blo 507795 3682721 := bstep (se 2 (by rfl) ⟨1381020, by rfl⟩ : syracuseStep 3682721 = 2762041) B2762041
theorem B1716713 : Blo 507795 1716713 := bstep (se 2 (by rfl) ⟨643767, by rfl⟩ : syracuseStep 1716713 = 1287535) B1287535
theorem B766601 : Blo 507795 766601 := bstep (se 2 (by rfl) ⟨287475, by rfl⟩ : syracuseStep 766601 = 574951) B574951
theorem B2896681 : Blo 507795 2896681 := bstep (se 2 (by rfl) ⟨1086255, by rfl⟩ : syracuseStep 2896681 = 2172511) B2172511
theorem B766841 : Blo 507795 766841 := bstep (se 2 (by rfl) ⟨287565, by rfl⟩ : syracuseStep 766841 = 575131) B575131
theorem B3880223 : Blo 507795 3880223 := bstep (se 1 (by rfl) ⟨2910167, by rfl⟩ : syracuseStep 3880223 = 5820335) B5820335
theorem B767483 : Blo 507795 767483 := bstep (se 1 (by rfl) ⟨575612, by rfl⟩ : syracuseStep 767483 = 1151225) B1151225
theorem B964217 : Blo 507795 964217 := bstep (se 2 (by rfl) ⟨361581, by rfl⟩ : syracuseStep 964217 = 723163) B723163
theorem B767615 : Blo 507795 767615 := bstep (se 1 (by rfl) ⟨575711, by rfl⟩ : syracuseStep 767615 = 1151423) B1151423
theorem B571567 : Blo 507795 571567 := bstep (se 1 (by rfl) ⟨428675, by rfl⟩ : syracuseStep 571567 = 857351) B857351
theorem B1456633 : Blo 507795 1456633 := bstep (se 2 (by rfl) ⟨546237, by rfl⟩ : syracuseStep 1456633 = 1092475) B1092475
theorem B7453433 : Blo 507795 7453433 := bstep (se 2 (by rfl) ⟨2795037, by rfl⟩ : syracuseStep 7453433 = 5590075) B5590075
theorem B572359 : Blo 507795 572359 := bstep (se 1 (by rfl) ⟨429269, by rfl⟩ : syracuseStep 572359 = 858539) B858539
theorem B965819 : Blo 507795 965819 := bstep (se 1 (by rfl) ⟨724364, by rfl⟩ : syracuseStep 965819 = 1448729) B1448729
theorem B2211023 : Blo 507795 2211023 := bstep (se 1 (by rfl) ⟨1658267, by rfl⟩ : syracuseStep 2211023 = 3316535) B3316535
theorem B736511 : Blo 507795 736511 := bstep (se 1 (by rfl) ⟨552383, by rfl⟩ : syracuseStep 736511 = 1104767) B1104767
theorem B572719 : Blo 507795 572719 := bstep (se 1 (by rfl) ⟨429539, by rfl⟩ : syracuseStep 572719 = 859079) B859079
theorem B507995 : Blo 507795 507995 := bstep (se 1 (by rfl) ⟨380996, by rfl⟩ : syracuseStep 507995 = 761993) B761993
theorem B573691 : Blo 507795 573691 := bstep (se 1 (by rfl) ⟨430268, by rfl⟩ : syracuseStep 573691 = 860537) B860537
theorem B2474351 : Blo 507795 2474351 := bstep (se 1 (by rfl) ⟨1855763, by rfl⟩ : syracuseStep 2474351 = 3711527) B3711527
theorem B2572883 : Blo 507795 2572883 := bstep (se 1 (by rfl) ⟨1929662, by rfl⟩ : syracuseStep 2572883 = 3859325) B3859325
theorem B1229651 : Blo 507795 1229651 := bstep (se 1 (by rfl) ⟨922238, by rfl⟩ : syracuseStep 1229651 = 1844477) B1844477
theorem B508799 : Blo 507795 508799 := bstep (se 1 (by rfl) ⟨381599, by rfl⟩ : syracuseStep 508799 = 763199) B763199
theorem B508831 : Blo 507795 508831 := bstep (se 1 (by rfl) ⟨381623, by rfl⟩ : syracuseStep 508831 = 763247) B763247
theorem B2180029 : Blo 507795 2180029 := bstep (se 3 (by rfl) ⟨408755, by rfl⟩ : syracuseStep 2180029 = 817511) B817511
theorem B1295311 : Blo 507795 1295311 := bstep (se 1 (by rfl) ⟨971483, by rfl⟩ : syracuseStep 1295311 = 1942967) B1942967
theorem B508911 : Blo 507795 508911 := bstep (se 1 (by rfl) ⟨381683, by rfl⟩ : syracuseStep 508911 = 763367) B763367
theorem B508999 : Blo 507795 508999 := bstep (se 1 (by rfl) ⟨381749, by rfl⟩ : syracuseStep 508999 = 763499) B763499
theorem B967763 : Blo 507795 967763 := bstep (se 1 (by rfl) ⟨725822, by rfl⟩ : syracuseStep 967763 = 1451645) B1451645
theorem B574555 : Blo 507795 574555 := bstep (se 1 (by rfl) ⟨430916, by rfl⟩ : syracuseStep 574555 = 861833) B861833
theorem B509031 : Blo 507795 509031 := bstep (se 1 (by rfl) ⟨381773, by rfl⟩ : syracuseStep 509031 = 763547) B763547
theorem B574591 : Blo 507795 574591 := bstep (se 1 (by rfl) ⟨430943, by rfl⟩ : syracuseStep 574591 = 861887) B861887
theorem B2180371 : Blo 507795 2180371 := bstep (se 1 (by rfl) ⟨1635278, by rfl⟩ : syracuseStep 2180371 = 3270557) B3270557
theorem B509311 : Blo 507795 509311 := bstep (se 1 (by rfl) ⟨381983, by rfl⟩ : syracuseStep 509311 = 763967) B763967
theorem B509407 : Blo 507795 509407 := bstep (se 1 (by rfl) ⟨382055, by rfl⟩ : syracuseStep 509407 = 764111) B764111
theorem B509487 : Blo 507795 509487 := bstep (se 1 (by rfl) ⟨382115, by rfl⟩ : syracuseStep 509487 = 764231) B764231
theorem B509679 : Blo 507795 509679 := bstep (se 1 (by rfl) ⟨382259, by rfl⟩ : syracuseStep 509679 = 764519) B764519
theorem B3262457 : Blo 507795 3262457 := bstep (se 2 (by rfl) ⟨1223421, by rfl⟩ : syracuseStep 3262457 = 2446843) B2446843
theorem B510043 : Blo 507795 510043 := bstep (se 1 (by rfl) ⟨382532, by rfl⟩ : syracuseStep 510043 = 765065) B765065
theorem B575599 : Blo 507795 575599 := bstep (se 1 (by rfl) ⟨431699, by rfl⟩ : syracuseStep 575599 = 863399) B863399
theorem B510079 : Blo 507795 510079 := bstep (se 1 (by rfl) ⟨382559, by rfl⟩ : syracuseStep 510079 = 765119) B765119
theorem B1886441 : Blo 507795 1886441 := bstep (se 2 (by rfl) ⟨707415, by rfl⟩ : syracuseStep 1886441 = 1414831) B1414831
theorem B7555949 : Blo 507795 7555949 := bstep (se 3 (by rfl) ⟨1416740, by rfl⟩ : syracuseStep 7555949 = 2833481) B2833481
theorem B1723517 : Blo 507795 1723517 := bstep (se 3 (by rfl) ⟨323159, by rfl⟩ : syracuseStep 1723517 = 646319) B646319
theorem B11292157 : Blo 507795 11292157 := bstep (se 3 (by rfl) ⟨2117279, by rfl⟩ : syracuseStep 11292157 = 4234559) B4234559
theorem B511535 : Blo 507795 511535 := bstep (se 1 (by rfl) ⟨383651, by rfl⟩ : syracuseStep 511535 = 767303) B767303
theorem B2182747 : Blo 507795 2182747 := bstep (se 1 (by rfl) ⟨1637060, by rfl⟩ : syracuseStep 2182747 = 3274121) B3274121
theorem B1724651 : Blo 507795 1724651 := bstep (se 1 (by rfl) ⟨1293488, by rfl⟩ : syracuseStep 1724651 = 2586977) B2586977
theorem B971423 : Blo 507795 971423 := bstep (se 1 (by rfl) ⟨728567, by rfl⟩ : syracuseStep 971423 = 1457135) B1457135
theorem B545563 : Blo 507795 545563 := bstep (se 1 (by rfl) ⟨409172, by rfl⟩ : syracuseStep 545563 = 818345) B818345
theorem B2183993 : Blo 507795 2183993 := bstep (se 2 (by rfl) ⟨818997, by rfl⟩ : syracuseStep 2183993 = 1637995) B1637995
theorem B644431 : Blo 507795 644431 := bstep (se 1 (by rfl) ⟨483323, by rfl⟩ : syracuseStep 644431 = 966647) B966647
theorem B1725947 : Blo 507795 1725947 := bstep (se 1 (by rfl) ⟨1294460, by rfl⟩ : syracuseStep 1725947 = 2588921) B2588921
theorem B644699 : Blo 507795 644699 := bstep (se 1 (by rfl) ⟨483524, by rfl⟩ : syracuseStep 644699 = 967049) B967049
theorem B1726055 : Blo 507795 1726055 := bstep (se 1 (by rfl) ⟨1294541, by rfl⟩ : syracuseStep 1726055 = 2589083) B2589083
theorem B16570169 : Blo 507795 16570169 := bstep (se 2 (by rfl) ⟨6213813, by rfl⟩ : syracuseStep 16570169 = 12427627) B12427627
theorem B2578715 : Blo 507795 2578715 := bstep (se 1 (by rfl) ⟨1934036, by rfl⟩ : syracuseStep 2578715 = 3868073) B3868073
theorem B1958455 : Blo 507795 1958455 := bstep (se 1 (by rfl) ⟨1468841, by rfl⟩ : syracuseStep 1958455 = 2937683) B2937683
theorem B4645439 : Blo 507795 4645439 := bstep (se 1 (by rfl) ⟨3484079, by rfl⟩ : syracuseStep 4645439 = 6968159) B6968159
theorem B2714489 : Blo 507795 2714489 := bstep (se 2 (by rfl) ⟨1017933, by rfl⟩ : syracuseStep 2714489 = 2035867) B2035867
theorem B5434285 : Blo 507795 5434285 := bstep (se 3 (by rfl) ⟨1018928, by rfl⟩ : syracuseStep 5434285 = 2037857) B2037857
theorem B3927131 : Blo 507795 3927131 := bstep (se 1 (by rfl) ⟨2945348, by rfl⟩ : syracuseStep 3927131 = 5890697) B5890697
theorem B1633409 : Blo 507795 1633409 := bstep (se 2 (by rfl) ⟨612528, by rfl⟩ : syracuseStep 1633409 = 1225057) B1225057
theorem B7367867 : Blo 507795 7367867 := bstep (se 1 (by rfl) ⟨5525900, by rfl⟩ : syracuseStep 7367867 = 11051801) B11051801
theorem B1928569 : Blo 507795 1928569 := bstep (se 2 (by rfl) ⟨723213, by rfl⟩ : syracuseStep 1928569 = 1446427) B1446427
theorem B1142639 : Blo 507795 1142639 := bstep (se 1 (by rfl) ⟨856979, by rfl⟩ : syracuseStep 1142639 = 1713959) B1713959
theorem B2486153 : Blo 507795 2486153 := bstep (se 2 (by rfl) ⟨932307, by rfl⟩ : syracuseStep 2486153 = 1864615) B1864615
theorem B2584871 : Blo 507795 2584871 := bstep (se 1 (by rfl) ⟨1938653, by rfl⟩ : syracuseStep 2584871 = 3877307) B3877307
theorem B4125127 : Blo 507795 4125127 := bstep (se 1 (by rfl) ⟨3093845, by rfl⟩ : syracuseStep 4125127 = 6187691) B6187691
theorem B1143287 : Blo 507795 1143287 := bstep (se 1 (by rfl) ⟨857465, by rfl⟩ : syracuseStep 1143287 = 1714931) B1714931
theorem B1143323 : Blo 507795 1143323 := bstep (se 1 (by rfl) ⟨857492, by rfl⟩ : syracuseStep 1143323 = 1714985) B1714985
theorem B2585681 : Blo 507795 2585681 := bstep (se 2 (by rfl) ⟨969630, by rfl⟩ : syracuseStep 2585681 = 1939261) B1939261
theorem B7369825 : Blo 507795 7369825 := bstep (se 2 (by rfl) ⟨2763684, by rfl⟩ : syracuseStep 7369825 = 5527369) B5527369
theorem B4355207 : Blo 507795 4355207 := bstep (se 1 (by rfl) ⟨3266405, by rfl⟩ : syracuseStep 4355207 = 6532811) B6532811
theorem B1865423 : Blo 507795 1865423 := bstep (se 1 (by rfl) ⟨1399067, by rfl⟩ : syracuseStep 1865423 = 2798135) B2798135
theorem B1930999 : Blo 507795 1930999 := bstep (se 1 (by rfl) ⟨1448249, by rfl⟩ : syracuseStep 1930999 = 2896499) B2896499
theorem B2489723 : Blo 507795 2489723 := bstep (se 1 (by rfl) ⟨1867292, by rfl⟩ : syracuseStep 2489723 = 3734585) B3734585
theorem B1146239 : Blo 507795 1146239 := bstep (se 1 (by rfl) ⟨859679, by rfl⟩ : syracuseStep 1146239 = 1719359) B1719359
theorem B2490209 : Blo 507795 2490209 := bstep (se 2 (by rfl) ⟨933828, by rfl⟩ : syracuseStep 2490209 = 1867657) B1867657
theorem B1146761 : Blo 507795 1146761 := bstep (se 2 (by rfl) ⟨430035, by rfl⟩ : syracuseStep 1146761 = 860071) B860071
theorem B1638559 : Blo 507795 1638559 := bstep (se 1 (by rfl) ⟨1228919, by rfl⟩ : syracuseStep 1638559 = 2457839) B2457839
theorem B1966523 : Blo 507795 1966523 := bstep (se 1 (by rfl) ⟨1474892, by rfl⟩ : syracuseStep 1966523 = 2949785) B2949785
theorem B819767 : Blo 507795 819767 := bstep (se 1 (by rfl) ⟨614825, by rfl⟩ : syracuseStep 819767 = 1229651) B1229651
theorem B1311839 : Blo 507795 1311839 := bstep (se 1 (by rfl) ⟨983879, by rfl⟩ : syracuseStep 1311839 = 1967759) B1967759
theorem B13043267 : Blo 507795 13043267 := bstep (se 1 (by rfl) ⟨9782450, by rfl⟩ : syracuseStep 13043267 = 19564901) B19564901
theorem B15664927 : Blo 507795 15664927 := bstep (se 1 (by rfl) ⟨11748695, by rfl⟩ : syracuseStep 15664927 = 23497391) B23497391
theorem B1149011 : Blo 507795 1149011 := bstep (se 1 (by rfl) ⟨861758, by rfl⟩ : syracuseStep 1149011 = 1723517) B1723517
theorem B6556079 : Blo 507795 6556079 := bstep (se 1 (by rfl) ⟨4917059, by rfl⟩ : syracuseStep 6556079 = 9834119) B9834119
theorem B20122037 : Blo 507795 20122037 := bstep (se 5 (by rfl) ⟨943220, by rfl⟩ : syracuseStep 20122037 = 1886441) B1886441
theorem B1149767 : Blo 507795 1149767 := bstep (se 1 (by rfl) ⟨862325, by rfl⟩ : syracuseStep 1149767 = 1724651) B1724651
theorem B1150505 : Blo 507795 1150505 := bstep (se 2 (by rfl) ⟨431439, by rfl⟩ : syracuseStep 1150505 = 862879) B862879
theorem B1150631 : Blo 507795 1150631 := bstep (se 1 (by rfl) ⟨862973, by rfl⟩ : syracuseStep 1150631 = 1725947) B1725947
theorem B1150703 : Blo 507795 1150703 := bstep (se 1 (by rfl) ⟨863027, by rfl⟩ : syracuseStep 1150703 = 1726055) B1726055
theorem B11046779 : Blo 507795 11046779 := bstep (se 1 (by rfl) ⟨8285084, by rfl⟩ : syracuseStep 11046779 = 16570169) B16570169
theorem B7245713 : Blo 507795 7245713 := bstep (se 2 (by rfl) ⟨2717142, by rfl⟩ : syracuseStep 7245713 = 5434285) B5434285
theorem B42407023 : Blo 507795 42407023 := bstep (se 1 (by rfl) ⟨31805267, by rfl⟩ : syracuseStep 42407023 = 63610535) B63610535
theorem B726175 : Blo 507795 726175 := bstep (se 1 (by rfl) ⟨544631, by rfl⟩ : syracuseStep 726175 = 1089263) B1089263
theorem B8721755 : Blo 507795 8721755 := bstep (se 1 (by rfl) ⟨6541316, by rfl⟩ : syracuseStep 8721755 = 13082633) B13082633
theorem B1939049 : Blo 507795 1939049 := bstep (se 2 (by rfl) ⟨727143, by rfl⟩ : syracuseStep 1939049 = 1454287) B1454287
theorem B1447931 : Blo 507795 1447931 := bstep (se 1 (by rfl) ⟨1085948, by rfl⟩ : syracuseStep 1447931 = 2171897) B2171897
theorem B858215 : Blo 507795 858215 := bstep (se 1 (by rfl) ⟨643661, by rfl⟩ : syracuseStep 858215 = 1287323) B1287323
theorem B727417 : Blo 507795 727417 := bstep (se 2 (by rfl) ⟨272781, by rfl⟩ : syracuseStep 727417 = 545563) B545563
theorem B859241 : Blo 507795 859241 := bstep (se 2 (by rfl) ⟨322215, by rfl⟩ : syracuseStep 859241 = 644431) B644431
theorem B1809659 : Blo 507795 1809659 := bstep (se 1 (by rfl) ⟨1357244, by rfl⟩ : syracuseStep 1809659 = 2714489) B2714489
theorem B1088939 : Blo 507795 1088939 := bstep (se 1 (by rfl) ⟨816704, by rfl⟩ : syracuseStep 1088939 = 1633409) B1633409
theorem B761759 : Blo 507795 761759 := bstep (se 1 (by rfl) ⟨571319, by rfl⟩ : syracuseStep 761759 = 1142639) B1142639
theorem B762089 : Blo 507795 762089 := bstep (se 2 (by rfl) ⟨285783, by rfl⟩ : syracuseStep 762089 = 571567) B571567
theorem B762191 : Blo 507795 762191 := bstep (se 1 (by rfl) ⟨571643, by rfl⟩ : syracuseStep 762191 = 1143287) B1143287
theorem B762215 : Blo 507795 762215 := bstep (se 1 (by rfl) ⟨571661, by rfl⟩ : syracuseStep 762215 = 1143323) B1143323
theorem B1942177 : Blo 507795 1942177 := bstep (se 2 (by rfl) ⟨728316, by rfl⟩ : syracuseStep 1942177 = 1456633) B1456633
theorem B763145 : Blo 507795 763145 := bstep (se 2 (by rfl) ⟨286179, by rfl⟩ : syracuseStep 763145 = 572359) B572359
theorem B763625 : Blo 507795 763625 := bstep (se 2 (by rfl) ⟨286359, by rfl⟩ : syracuseStep 763625 = 572719) B572719
theorem B764159 : Blo 507795 764159 := bstep (se 1 (by rfl) ⟨573119, by rfl⟩ : syracuseStep 764159 = 1146239) B1146239
theorem B764507 : Blo 507795 764507 := bstep (se 1 (by rfl) ⟨573380, by rfl⟩ : syracuseStep 764507 = 1146761) B1146761
theorem B1649567 : Blo 507795 1649567 := bstep (se 1 (by rfl) ⟨1237175, by rfl⟩ : syracuseStep 1649567 = 2474351) B2474351
theorem B764921 : Blo 507795 764921 := bstep (se 2 (by rfl) ⟨286845, by rfl⟩ : syracuseStep 764921 = 573691) B573691
theorem B1715255 : Blo 507795 1715255 := bstep (se 1 (by rfl) ⟨1286441, by rfl⟩ : syracuseStep 1715255 = 2572883) B2572883
theorem B17869967 : Blo 507795 17869967 := bstep (se 1 (by rfl) ⟨13402475, by rfl⟩ : syracuseStep 17869967 = 26804951) B26804951
theorem B765419 : Blo 507795 765419 := bstep (se 1 (by rfl) ⟨574064, by rfl⟩ : syracuseStep 765419 = 1148129) B1148129
theorem B765659 : Blo 507795 765659 := bstep (se 1 (by rfl) ⟨574244, by rfl⟩ : syracuseStep 765659 = 1148489) B1148489
theorem B765863 : Blo 507795 765863 := bstep (se 1 (by rfl) ⟨574397, by rfl⟩ : syracuseStep 765863 = 1148795) B1148795
theorem B766073 : Blo 507795 766073 := bstep (se 2 (by rfl) ⟨287277, by rfl⟩ : syracuseStep 766073 = 574555) B574555
theorem B766121 : Blo 507795 766121 := bstep (se 2 (by rfl) ⟨287295, by rfl⟩ : syracuseStep 766121 = 574591) B574591
theorem B766247 : Blo 507795 766247 := bstep (se 1 (by rfl) ⟨574685, by rfl⟩ : syracuseStep 766247 = 1149371) B1149371
theorem B3977839 : Blo 507795 3977839 := bstep (se 1 (by rfl) ⟨2983379, by rfl⟩ : syracuseStep 3977839 = 5966759) B5966759
theorem B766655 : Blo 507795 766655 := bstep (se 1 (by rfl) ⟨574991, by rfl⟩ : syracuseStep 766655 = 1149983) B1149983
theorem B767465 : Blo 507795 767465 := bstep (se 2 (by rfl) ⟨287799, by rfl⟩ : syracuseStep 767465 = 575599) B575599
theorem B767471 : Blo 507795 767471 := bstep (se 1 (by rfl) ⟨575603, by rfl⟩ : syracuseStep 767471 = 1151207) B1151207
theorem B1455995 : Blo 507795 1455995 := bstep (se 1 (by rfl) ⟨1091996, by rfl⟩ : syracuseStep 1455995 = 2183993) B2183993
theorem B1718441 : Blo 507795 1718441 := bstep (se 2 (by rfl) ⟨644415, by rfl⟩ : syracuseStep 1718441 = 1288831) B1288831
theorem B965371 : Blo 507795 965371 := bstep (se 1 (by rfl) ⟨724028, by rfl⟩ : syracuseStep 965371 = 1448057) B1448057
theorem B1719143 : Blo 507795 1719143 := bstep (se 1 (by rfl) ⟨1289357, by rfl⟩ : syracuseStep 1719143 = 2578715) B2578715
theorem B1719197 : Blo 507795 1719197 := bstep (se 3 (by rfl) ⟨322349, by rfl⟩ : syracuseStep 1719197 = 644699) B644699
theorem B572575 : Blo 507795 572575 := bstep (se 1 (by rfl) ⟨429431, by rfl⟩ : syracuseStep 572575 = 858863) B858863
theorem B2571425 : Blo 507795 2571425 := bstep (se 2 (by rfl) ⟨964284, by rfl⟩ : syracuseStep 2571425 = 1928569) B1928569
theorem B15056209 : Blo 507795 15056209 := bstep (se 2 (by rfl) ⟨5646078, by rfl⟩ : syracuseStep 15056209 = 11292157) B11292157
theorem B6995483 : Blo 507795 6995483 := bstep (se 1 (by rfl) ⟨5246612, by rfl⟩ : syracuseStep 6995483 = 10493225) B10493225
theorem B7454375 : Blo 507795 7454375 := bstep (se 1 (by rfl) ⟨5590781, by rfl⟩ : syracuseStep 7454375 = 11181563) B11181563
theorem B8699885 : Blo 507795 8699885 := bstep (se 3 (by rfl) ⟨1631228, by rfl⟩ : syracuseStep 8699885 = 3262457) B3262457
theorem B7323695 : Blo 507795 7323695 := bstep (se 1 (by rfl) ⟨5492771, by rfl⟩ : syracuseStep 7323695 = 10985543) B10985543
theorem B573511 : Blo 507795 573511 := bstep (se 1 (by rfl) ⟨430133, by rfl⟩ : syracuseStep 573511 = 860267) B860267
theorem B508031 : Blo 507795 508031 := bstep (se 1 (by rfl) ⟨381023, by rfl⟩ : syracuseStep 508031 = 762047) B762047
theorem B508155 : Blo 507795 508155 := bstep (se 1 (by rfl) ⟨381116, by rfl⟩ : syracuseStep 508155 = 762233) B762233
theorem B508187 : Blo 507795 508187 := bstep (se 1 (by rfl) ⟨381140, by rfl⟩ : syracuseStep 508187 = 762281) B762281
theorem B3096959 : Blo 507795 3096959 := bstep (se 1 (by rfl) ⟨2322719, by rfl⟩ : syracuseStep 3096959 = 4645439) B4645439
theorem B508351 : Blo 507795 508351 := bstep (se 1 (by rfl) ⟨381263, by rfl⟩ : syracuseStep 508351 = 762527) B762527
theorem B509087 : Blo 507795 509087 := bstep (se 1 (by rfl) ⟨381815, by rfl⟩ : syracuseStep 509087 = 763631) B763631
theorem B509647 : Blo 507795 509647 := bstep (se 1 (by rfl) ⟨382235, by rfl⟩ : syracuseStep 509647 = 764471) B764471
theorem B509695 : Blo 507795 509695 := bstep (se 1 (by rfl) ⟨382271, by rfl⟩ : syracuseStep 509695 = 764543) B764543
theorem B575743 : Blo 507795 575743 := bstep (se 1 (by rfl) ⟨431807, by rfl⟩ : syracuseStep 575743 = 863615) B863615
theorem B969023 : Blo 507795 969023 := bstep (se 1 (by rfl) ⟨726767, by rfl⟩ : syracuseStep 969023 = 1453535) B1453535
theorem B2574665 : Blo 507795 2574665 := bstep (se 2 (by rfl) ⟨965499, by rfl⟩ : syracuseStep 2574665 = 1930999) B1930999
theorem B1657435 : Blo 507795 1657435 := bstep (se 1 (by rfl) ⟨1243076, by rfl⟩ : syracuseStep 1657435 = 2486153) B2486153
theorem B510631 : Blo 507795 510631 := bstep (se 1 (by rfl) ⟨382973, by rfl⟩ : syracuseStep 510631 = 765947) B765947
theorem B510791 : Blo 507795 510791 := bstep (se 1 (by rfl) ⟨383093, by rfl⟩ : syracuseStep 510791 = 766187) B766187
theorem B1723247 : Blo 507795 1723247 := bstep (se 1 (by rfl) ⟨1292435, by rfl⟩ : syracuseStep 1723247 = 2584871) B2584871
theorem B511067 : Blo 507795 511067 := bstep (se 1 (by rfl) ⟨383300, by rfl⟩ : syracuseStep 511067 = 766601) B766601
theorem B511227 : Blo 507795 511227 := bstep (se 1 (by rfl) ⟨383420, by rfl⟩ : syracuseStep 511227 = 766841) B766841
theorem B1723787 : Blo 507795 1723787 := bstep (se 1 (by rfl) ⟨1292840, by rfl⟩ : syracuseStep 1723787 = 2585681) B2585681
theorem B2903471 : Blo 507795 2903471 := bstep (se 1 (by rfl) ⟨2177603, by rfl⟩ : syracuseStep 2903471 = 4355207) B4355207
theorem B511655 : Blo 507795 511655 := bstep (se 1 (by rfl) ⟨383741, by rfl⟩ : syracuseStep 511655 = 767483) B767483
theorem B642811 : Blo 507795 642811 := bstep (se 1 (by rfl) ⟨482108, by rfl⟩ : syracuseStep 642811 = 964217) B964217
theorem B511743 : Blo 507795 511743 := bstep (se 1 (by rfl) ⟨383807, by rfl⟩ : syracuseStep 511743 = 767615) B767615
theorem B4968955 : Blo 507795 4968955 := bstep (se 1 (by rfl) ⟨3726716, by rfl⟩ : syracuseStep 4968955 = 7453433) B7453433
theorem B643879 : Blo 507795 643879 := bstep (se 1 (by rfl) ⟨482909, by rfl⟩ : syracuseStep 643879 = 965819) B965819
theorem B1659815 : Blo 507795 1659815 := bstep (se 1 (by rfl) ⟨1244861, by rfl⟩ : syracuseStep 1659815 = 2489723) B2489723
theorem B3527869 : Blo 507795 3527869 := bstep (se 3 (by rfl) ⟨661475, by rfl⟩ : syracuseStep 3527869 = 1322951) B1322951
theorem B1660139 : Blo 507795 1660139 := bstep (se 1 (by rfl) ⟨1245104, by rfl⟩ : syracuseStep 1660139 = 2490209) B2490209
theorem B645175 : Blo 507795 645175 := bstep (se 1 (by rfl) ⟨483881, by rfl⟩ : syracuseStep 645175 = 967763) B967763
theorem B2611273 : Blo 507795 2611273 := bstep (se 2 (by rfl) ⟨979227, by rfl⟩ : syracuseStep 2611273 = 1958455) B1958455
theorem B2578553 : Blo 507795 2578553 := bstep (se 2 (by rfl) ⟨966957, by rfl⟩ : syracuseStep 2578553 = 1933915) B1933915
theorem B1726919 : Blo 507795 1726919 := bstep (se 1 (by rfl) ⟨1295189, by rfl⟩ : syracuseStep 1726919 = 2590379) B2590379
theorem B2906705 : Blo 507795 2906705 := bstep (se 2 (by rfl) ⟨1090014, by rfl⟩ : syracuseStep 2906705 = 2180029) B2180029
theorem B1727081 : Blo 507795 1727081 := bstep (se 2 (by rfl) ⟨647655, by rfl⟩ : syracuseStep 1727081 = 1295311) B1295311
theorem B2907161 : Blo 507795 2907161 := bstep (se 2 (by rfl) ⟨1090185, by rfl⟩ : syracuseStep 2907161 = 2180371) B2180371
theorem B5037299 : Blo 507795 5037299 := bstep (se 1 (by rfl) ⟨3777974, by rfl⟩ : syracuseStep 5037299 = 7555949) B7555949
theorem B647615 : Blo 507795 647615 := bstep (se 1 (by rfl) ⟨485711, by rfl⟩ : syracuseStep 647615 = 971423) B971423
theorem B2451073 : Blo 507795 2451073 := bstep (se 2 (by rfl) ⟨919152, by rfl⟩ : syracuseStep 2451073 = 1838305) B1838305
theorem B2910329 : Blo 507795 2910329 := bstep (se 2 (by rfl) ⟨1091373, by rfl⟩ : syracuseStep 2910329 = 2182747) B2182747
theorem B111602609 : Blo 507795 111602609 := bstep (se 2 (by rfl) ⟨41850978, by rfl⟩ : syracuseStep 111602609 = 83701957) B83701957
theorem B2059451 : Blo 507795 2059451 := bstep (se 1 (by rfl) ⟨1544588, by rfl⟩ : syracuseStep 2059451 = 3089177) B3089177
theorem B4353223 : Blo 507795 4353223 := bstep (se 1 (by rfl) ⟨3264917, by rfl⟩ : syracuseStep 4353223 = 6529835) B6529835
theorem B13069511 : Blo 507795 13069511 := bstep (se 1 (by rfl) ⟨9802133, by rfl⟩ : syracuseStep 13069511 = 19604267) B19604267
theorem B5500169 : Blo 507795 5500169 := bstep (se 2 (by rfl) ⟨2062563, by rfl⟩ : syracuseStep 5500169 = 4125127) B4125127
theorem B3862241 : Blo 507795 3862241 := bstep (se 2 (by rfl) ⟨1448340, by rfl⟩ : syracuseStep 3862241 = 2896681) B2896681
theorem B6516713 : Blo 507795 6516713 := bstep (se 2 (by rfl) ⟨2443767, by rfl⟩ : syracuseStep 6516713 = 4887535) B4887535
theorem B1142891 : Blo 507795 1142891 := bstep (se 1 (by rfl) ⟨857168, by rfl⟩ : syracuseStep 1142891 = 1714337) B1714337
theorem B9826433 : Blo 507795 9826433 := bstep (se 2 (by rfl) ⟨3684912, by rfl⟩ : syracuseStep 9826433 = 7369825) B7369825
theorem B1143161 : Blo 507795 1143161 := bstep (se 2 (by rfl) ⟨428685, by rfl⟩ : syracuseStep 1143161 = 857371) B857371
theorem B2618087 : Blo 507795 2618087 := bstep (se 1 (by rfl) ⟨1963565, by rfl⟩ : syracuseStep 2618087 = 3927131) B3927131
theorem B4911911 : Blo 507795 4911911 := bstep (se 1 (by rfl) ⟨3683933, by rfl⟩ : syracuseStep 4911911 = 7367867) B7367867
theorem B13988963 : Blo 507795 13988963 := bstep (se 1 (by rfl) ⟨10491722, by rfl⟩ : syracuseStep 13988963 = 20983445) B20983445
theorem B1143935 : Blo 507795 1143935 := bstep (se 1 (by rfl) ⟨857951, by rfl⟩ : syracuseStep 1143935 = 1715903) B1715903
theorem B2455147 : Blo 507795 2455147 := bstep (se 1 (by rfl) ⟨1841360, by rfl⟩ : syracuseStep 2455147 = 3682721) B3682721
theorem B1144475 : Blo 507795 1144475 := bstep (se 1 (by rfl) ⟨858356, by rfl⟩ : syracuseStep 1144475 = 1716713) B1716713
theorem B5896061 : Blo 507795 5896061 := bstep (se 3 (by rfl) ⟨1105511, by rfl⟩ : syracuseStep 5896061 = 2211023) B2211023
theorem B1964029 : Blo 507795 1964029 := bstep (se 3 (by rfl) ⟨368255, by rfl⟩ : syracuseStep 1964029 = 736511) B736511
theorem B1931273 : Blo 507795 1931273 := bstep (se 2 (by rfl) ⟨724227, by rfl⟩ : syracuseStep 1931273 = 1448455) B1448455
theorem B2586815 : Blo 507795 2586815 := bstep (se 1 (by rfl) ⟨1940111, by rfl⟩ : syracuseStep 2586815 = 3880223) B3880223
theorem B1243615 : Blo 507795 1243615 := bstep (se 1 (by rfl) ⟨932711, by rfl⟩ : syracuseStep 1243615 = 1865423) B1865423
theorem B4882463 : Blo 507795 4882463 := bstep (se 1 (by rfl) ⟨3661847, by rfl⟩ : syracuseStep 4882463 = 7323695) B7323695
theorem B2589569 : Blo 507795 2589569 := bstep (se 2 (by rfl) ⟨971088, by rfl⟩ : syracuseStep 2589569 = 1942177) B1942177
theorem B8258557 : Blo 507795 8258557 := bstep (se 3 (by rfl) ⟨1548479, by rfl⟩ : syracuseStep 8258557 = 3096959) B3096959
theorem B5244061 : Blo 507795 5244061 := bstep (se 3 (by rfl) ⟨983261, by rfl⟩ : syracuseStep 5244061 = 1966523) B1966523
theorem B1148831 : Blo 507795 1148831 := bstep (se 1 (by rfl) ⟨861623, by rfl⟩ : syracuseStep 1148831 = 1723247) B1723247
theorem B6981565 : Blo 507795 6981565 := bstep (se 3 (by rfl) ⟨1309043, by rfl⟩ : syracuseStep 6981565 = 2618087) B2618087
theorem B1149191 : Blo 507795 1149191 := bstep (se 1 (by rfl) ⟨861893, by rfl⟩ : syracuseStep 1149191 = 1723787) B1723787
theorem B1935647 : Blo 507795 1935647 := bstep (se 1 (by rfl) ⟨1451735, by rfl⟩ : syracuseStep 1935647 = 2903471) B2903471
theorem B5804297 : Blo 507795 5804297 := bstep (se 2 (by rfl) ⟨2176611, by rfl⟩ : syracuseStep 5804297 = 4353223) B4353223
theorem B1151279 : Blo 507795 1151279 := bstep (se 1 (by rfl) ⟨863459, by rfl⟩ : syracuseStep 1151279 = 1726919) B1726919
theorem B1937803 : Blo 507795 1937803 := bstep (se 1 (by rfl) ⟨1453352, by rfl⟩ : syracuseStep 1937803 = 2906705) B2906705
theorem B1151387 : Blo 507795 1151387 := bstep (se 1 (by rfl) ⟨863540, by rfl⟩ : syracuseStep 1151387 = 1727081) B1727081
theorem B1938107 : Blo 507795 1938107 := bstep (se 1 (by rfl) ⟨1453580, by rfl⟩ : syracuseStep 1938107 = 2907161) B2907161
theorem B725959 : Blo 507795 725959 := bstep (se 1 (by rfl) ⟨544469, by rfl⟩ : syracuseStep 725959 = 1088939) B1088939
theorem B857081 : Blo 507795 857081 := bstep (se 2 (by rfl) ⟨321405, by rfl⟩ : syracuseStep 857081 = 642811) B642811
theorem B6625273 : Blo 507795 6625273 := bstep (se 2 (by rfl) ⟨2484477, by rfl⟩ : syracuseStep 6625273 = 4968955) B4968955
theorem B3872933 : Blo 507795 3872933 := bstep (se 4 (by rfl) ⟨363087, by rfl⟩ : syracuseStep 3872933 = 726175) B726175
theorem B858505 : Blo 507795 858505 := bstep (se 2 (by rfl) ⟨321939, by rfl⟩ : syracuseStep 858505 = 643879) B643879
theorem B1940219 : Blo 507795 1940219 := bstep (se 1 (by rfl) ⟨1455164, by rfl⟩ : syracuseStep 1940219 = 2910329) B2910329
theorem B761927 : Blo 507795 761927 := bstep (se 1 (by rfl) ⟨571445, by rfl⟩ : syracuseStep 761927 = 1142891) B1142891
theorem B860233 : Blo 507795 860233 := bstep (se 2 (by rfl) ⟨322587, by rfl⟩ : syracuseStep 860233 = 645175) B645175
theorem B3481697 : Blo 507795 3481697 := bstep (se 2 (by rfl) ⟨1305636, by rfl⟩ : syracuseStep 3481697 = 2611273) B2611273
theorem B762107 : Blo 507795 762107 := bstep (se 1 (by rfl) ⟨571580, by rfl⟩ : syracuseStep 762107 = 1143161) B1143161
theorem B4825757 : Blo 507795 4825757 := bstep (se 3 (by rfl) ⟨904829, by rfl⟩ : syracuseStep 4825757 = 1809659) B1809659
theorem B762623 : Blo 507795 762623 := bstep (se 1 (by rfl) ⟨571967, by rfl⟩ : syracuseStep 762623 = 1143935) B1143935
theorem B1287161 : Blo 507795 1287161 := bstep (se 2 (by rfl) ⟨482685, by rfl⟩ : syracuseStep 1287161 = 965371) B965371
theorem B762983 : Blo 507795 762983 := bstep (se 1 (by rfl) ⟨572237, by rfl⟩ : syracuseStep 762983 = 1144475) B1144475
theorem B1287515 : Blo 507795 1287515 := bstep (se 1 (by rfl) ⟨965636, by rfl⟩ : syracuseStep 1287515 = 1931273) B1931273
theorem B763433 : Blo 507795 763433 := bstep (se 2 (by rfl) ⟨286287, by rfl⟩ : syracuseStep 763433 = 572575) B572575
theorem B1714283 : Blo 507795 1714283 := bstep (se 1 (by rfl) ⟨1285712, by rfl⟩ : syracuseStep 1714283 = 2571425) B2571425
theorem B4663655 : Blo 507795 4663655 := bstep (se 1 (by rfl) ⟨3497741, by rfl⟩ : syracuseStep 4663655 = 6995483) B6995483
theorem B764681 : Blo 507795 764681 := bstep (se 2 (by rfl) ⟨286755, by rfl⟩ : syracuseStep 764681 = 573511) B573511
theorem B8695511 : Blo 507795 8695511 := bstep (se 1 (by rfl) ⟨6521633, by rfl⟩ : syracuseStep 8695511 = 13043267) B13043267
theorem B766007 : Blo 507795 766007 := bstep (se 1 (by rfl) ⟨574505, by rfl⟩ : syracuseStep 766007 = 1149011) B1149011
theorem B1716443 : Blo 507795 1716443 := bstep (se 1 (by rfl) ⟨1287332, by rfl⟩ : syracuseStep 1716443 = 2574665) B2574665
theorem B4370719 : Blo 507795 4370719 := bstep (se 1 (by rfl) ⟨3278039, by rfl⟩ : syracuseStep 4370719 = 6556079) B6556079
theorem B13414691 : Blo 507795 13414691 := bstep (se 1 (by rfl) ⟨10061018, by rfl⟩ : syracuseStep 13414691 = 20122037) B20122037
theorem B766511 : Blo 507795 766511 := bstep (se 1 (by rfl) ⟨574883, by rfl⟩ : syracuseStep 766511 = 1149767) B1149767
theorem B767003 : Blo 507795 767003 := bstep (se 1 (by rfl) ⟨575252, by rfl⟩ : syracuseStep 767003 = 1150505) B1150505
theorem B20886569 : Blo 507795 20886569 := bstep (se 2 (by rfl) ⟨7832463, by rfl⟩ : syracuseStep 20886569 = 15664927) B15664927
theorem B767087 : Blo 507795 767087 := bstep (se 1 (by rfl) ⟨575315, by rfl⟩ : syracuseStep 767087 = 1150631) B1150631
theorem B767135 : Blo 507795 767135 := bstep (se 1 (by rfl) ⟨575351, by rfl⟩ : syracuseStep 767135 = 1150703) B1150703
theorem B4830475 : Blo 507795 4830475 := bstep (se 1 (by rfl) ⟨3622856, by rfl⟩ : syracuseStep 4830475 = 7245713) B7245713
theorem B37303901 : Blo 507795 37303901 := bstep (se 3 (by rfl) ⟨6994481, by rfl⟩ : syracuseStep 37303901 = 13988963) B13988963
theorem B767657 : Blo 507795 767657 := bstep (se 2 (by rfl) ⟨287871, by rfl⟩ : syracuseStep 767657 = 575743) B575743
theorem B21215141 : Blo 507795 21215141 := bstep (se 4 (by rfl) ⟨1988919, by rfl⟩ : syracuseStep 21215141 = 3977839) B3977839
theorem B2209913 : Blo 507795 2209913 := bstep (se 2 (by rfl) ⟨828717, by rfl⟩ : syracuseStep 2209913 = 1657435) B1657435
theorem B5814503 : Blo 507795 5814503 := bstep (se 1 (by rfl) ⟨4360877, by rfl⟩ : syracuseStep 5814503 = 8721755) B8721755
theorem B1292699 : Blo 507795 1292699 := bstep (se 1 (by rfl) ⟨969524, by rfl⟩ : syracuseStep 1292699 = 1939049) B1939049
theorem B965287 : Blo 507795 965287 := bstep (se 1 (by rfl) ⟨723965, by rfl⟩ : syracuseStep 965287 = 1447931) B1447931
theorem B572143 : Blo 507795 572143 := bstep (se 1 (by rfl) ⟨429107, by rfl⟩ : syracuseStep 572143 = 858215) B858215
theorem B1719035 : Blo 507795 1719035 := bstep (se 1 (by rfl) ⟨1289276, by rfl⟩ : syracuseStep 1719035 = 2578553) B2578553
theorem B572827 : Blo 507795 572827 := bstep (se 1 (by rfl) ⟨429620, by rfl⟩ : syracuseStep 572827 = 859241) B859241
theorem B3358199 : Blo 507795 3358199 := bstep (se 1 (by rfl) ⟨2518649, by rfl⟩ : syracuseStep 3358199 = 5037299) B5037299
theorem B3882653 : Blo 507795 3882653 := bstep (se 3 (by rfl) ⟨727997, by rfl⟩ : syracuseStep 3882653 = 1455995) B1455995
theorem B507839 : Blo 507795 507839 := bstep (se 1 (by rfl) ⟨380879, by rfl⟩ : syracuseStep 507839 = 761759) B761759
theorem B508059 : Blo 507795 508059 := bstep (se 1 (by rfl) ⟨381044, by rfl⟩ : syracuseStep 508059 = 762089) B762089
theorem B508127 : Blo 507795 508127 := bstep (se 1 (by rfl) ⟨381095, by rfl⟩ : syracuseStep 508127 = 762191) B762191
theorem B508143 : Blo 507795 508143 := bstep (se 1 (by rfl) ⟨381107, by rfl⟩ : syracuseStep 508143 = 762215) B762215
theorem B508763 : Blo 507795 508763 := bstep (se 1 (by rfl) ⟨381572, by rfl⟩ : syracuseStep 508763 = 763145) B763145
theorem B509083 : Blo 507795 509083 := bstep (se 1 (by rfl) ⟨381812, by rfl⟩ : syracuseStep 509083 = 763625) B763625
theorem B56542697 : Blo 507795 56542697 := bstep (se 2 (by rfl) ⟨21203511, by rfl⟩ : syracuseStep 56542697 = 42407023) B42407023
theorem B509439 : Blo 507795 509439 := bstep (se 1 (by rfl) ⟨382079, by rfl⟩ : syracuseStep 509439 = 764159) B764159
theorem B4703825 : Blo 507795 4703825 := bstep (se 2 (by rfl) ⟨1763934, by rfl⟩ : syracuseStep 4703825 = 3527869) B3527869
theorem B509671 : Blo 507795 509671 := bstep (se 1 (by rfl) ⟨382253, by rfl⟩ : syracuseStep 509671 = 764507) B764507
theorem B80299781 : Blo 507795 80299781 := bstep (se 4 (by rfl) ⟨7528104, by rfl⟩ : syracuseStep 80299781 = 15056209) B15056209
theorem B1099711 : Blo 507795 1099711 := bstep (se 1 (by rfl) ⟨824783, by rfl⟩ : syracuseStep 1099711 = 1649567) B1649567
theorem B74401739 : Blo 507795 74401739 := bstep (se 1 (by rfl) ⟨55801304, by rfl⟩ : syracuseStep 74401739 = 111602609) B111602609
theorem B509947 : Blo 507795 509947 := bstep (se 1 (by rfl) ⟨382460, by rfl⟩ : syracuseStep 509947 = 764921) B764921
theorem B11913311 : Blo 507795 11913311 := bstep (se 1 (by rfl) ⟨8934983, by rfl⟩ : syracuseStep 11913311 = 17869967) B17869967
theorem B510279 : Blo 507795 510279 := bstep (se 1 (by rfl) ⟨382709, by rfl⟩ : syracuseStep 510279 = 765419) B765419
theorem B510439 : Blo 507795 510439 := bstep (se 1 (by rfl) ⟨382829, by rfl⟩ : syracuseStep 510439 = 765659) B765659
theorem B2574827 : Blo 507795 2574827 := bstep (se 1 (by rfl) ⟨1931120, by rfl⟩ : syracuseStep 2574827 = 3862241) B3862241
theorem B510575 : Blo 507795 510575 := bstep (se 1 (by rfl) ⟨382931, by rfl⟩ : syracuseStep 510575 = 765863) B765863
theorem B4344475 : Blo 507795 4344475 := bstep (se 1 (by rfl) ⟨3258356, by rfl⟩ : syracuseStep 4344475 = 6516713) B6516713
theorem B510715 : Blo 507795 510715 := bstep (se 1 (by rfl) ⟨383036, by rfl⟩ : syracuseStep 510715 = 766073) B766073
theorem B510747 : Blo 507795 510747 := bstep (se 1 (by rfl) ⟨383060, by rfl⟩ : syracuseStep 510747 = 766121) B766121
theorem B510831 : Blo 507795 510831 := bstep (se 1 (by rfl) ⟨383123, by rfl⟩ : syracuseStep 510831 = 766247) B766247
theorem B511103 : Blo 507795 511103 := bstep (se 1 (by rfl) ⟨383327, by rfl⟩ : syracuseStep 511103 = 766655) B766655
theorem B969889 : Blo 507795 969889 := bstep (se 2 (by rfl) ⟨363708, by rfl⟩ : syracuseStep 969889 = 727417) B727417
theorem B1658153 : Blo 507795 1658153 := bstep (se 2 (by rfl) ⟨621807, by rfl⟩ : syracuseStep 1658153 = 1243615) B1243615
theorem B511643 : Blo 507795 511643 := bstep (se 1 (by rfl) ⟨383732, by rfl⟩ : syracuseStep 511643 = 767465) B767465
theorem B511647 : Blo 507795 511647 := bstep (se 1 (by rfl) ⟨383735, by rfl⟩ : syracuseStep 511647 = 767471) B767471
theorem B1724543 : Blo 507795 1724543 := bstep (se 1 (by rfl) ⟨1293407, by rfl⟩ : syracuseStep 1724543 = 2586815) B2586815
theorem B4969583 : Blo 507795 4969583 := bstep (se 1 (by rfl) ⟨3727187, by rfl⟩ : syracuseStep 4969583 = 7454375) B7454375
theorem B2184745 : Blo 507795 2184745 := bstep (se 2 (by rfl) ⟨819279, by rfl⟩ : syracuseStep 2184745 = 1638559) B1638559
theorem B546511 : Blo 507795 546511 := bstep (se 1 (by rfl) ⟨409883, by rfl⟩ : syracuseStep 546511 = 819767) B819767
theorem B874559 : Blo 507795 874559 := bstep (se 1 (by rfl) ⟨655919, by rfl⟩ : syracuseStep 874559 = 1311839) B1311839
theorem B1726973 : Blo 507795 1726973 := bstep (se 3 (by rfl) ⟨323807, by rfl⟩ : syracuseStep 1726973 = 647615) B647615
theorem B3268097 : Blo 507795 3268097 := bstep (se 2 (by rfl) ⟨1225536, by rfl⟩ : syracuseStep 3268097 = 2451073) B2451073
theorem B7364519 : Blo 507795 7364519 := bstep (se 1 (by rfl) ⟨5523389, by rfl⟩ : syracuseStep 7364519 = 11046779) B11046779
theorem B1106543 : Blo 507795 1106543 := bstep (se 1 (by rfl) ⟨829907, by rfl⟩ : syracuseStep 1106543 = 1659815) B1659815
theorem B1106759 : Blo 507795 1106759 := bstep (se 1 (by rfl) ⟨830069, by rfl⟩ : syracuseStep 1106759 = 1660139) B1660139
theorem B2584061 : Blo 507795 2584061 := bstep (se 3 (by rfl) ⟨484511, by rfl⟩ : syracuseStep 2584061 = 969023) B969023
theorem B1143503 : Blo 507795 1143503 := bstep (se 1 (by rfl) ⟨857627, by rfl⟩ : syracuseStep 1143503 = 1715255) B1715255
theorem B1372967 : Blo 507795 1372967 := bstep (se 1 (by rfl) ⟨1029725, by rfl⟩ : syracuseStep 1372967 = 2059451) B2059451
theorem B8713007 : Blo 507795 8713007 := bstep (se 1 (by rfl) ⟨6534755, by rfl⟩ : syracuseStep 8713007 = 13069511) B13069511
theorem B3273529 : Blo 507795 3273529 := bstep (se 2 (by rfl) ⟨1227573, by rfl⟩ : syracuseStep 3273529 = 2455147) B2455147
theorem B3666779 : Blo 507795 3666779 := bstep (se 1 (by rfl) ⟨2750084, by rfl⟩ : syracuseStep 3666779 = 5500169) B5500169
theorem B2618705 : Blo 507795 2618705 := bstep (se 2 (by rfl) ⟨982014, by rfl⟩ : syracuseStep 2618705 = 1964029) B1964029
theorem B6550955 : Blo 507795 6550955 := bstep (se 1 (by rfl) ⟨4913216, by rfl⟩ : syracuseStep 6550955 = 9826433) B9826433
theorem B3274607 : Blo 507795 3274607 := bstep (se 1 (by rfl) ⟨2455955, by rfl⟩ : syracuseStep 3274607 = 4911911) B4911911
theorem B3930707 : Blo 507795 3930707 := bstep (se 1 (by rfl) ⟨2948030, by rfl⟩ : syracuseStep 3930707 = 5896061) B5896061
theorem B1145627 : Blo 507795 1145627 := bstep (se 1 (by rfl) ⟨859220, by rfl⟩ : syracuseStep 1145627 = 1718441) B1718441
theorem B1146095 : Blo 507795 1146095 := bstep (se 1 (by rfl) ⟨859571, by rfl⟩ : syracuseStep 1146095 = 1719143) B1719143
theorem B1146131 : Blo 507795 1146131 := bstep (se 1 (by rfl) ⟨859598, by rfl⟩ : syracuseStep 1146131 = 1719197) B1719197
theorem B5799923 : Blo 507795 5799923 := bstep (se 1 (by rfl) ⟨4349942, by rfl⟩ : syracuseStep 5799923 = 8699885) B8699885
theorem B1146977 : Blo 507795 1146977 := bstep (se 2 (by rfl) ⟨430116, by rfl⟩ : syracuseStep 1146977 = 860233) B860233
theorem B11011409 : Blo 507795 11011409 := bstep (se 2 (by rfl) ⟨4129278, by rfl⟩ : syracuseStep 11011409 = 8258557) B8258557
theorem B9308753 : Blo 507795 9308753 := bstep (se 2 (by rfl) ⟨3490782, by rfl⟩ : syracuseStep 9308753 = 6981565) B6981565
theorem B1149695 : Blo 507795 1149695 := bstep (se 1 (by rfl) ⟨862271, by rfl⟩ : syracuseStep 1149695 = 1724543) B1724543
theorem B3869531 : Blo 507795 3869531 := bstep (se 1 (by rfl) ⟨2902148, by rfl⟩ : syracuseStep 3869531 = 5804297) B5804297
theorem B3313055 : Blo 507795 3313055 := bstep (se 1 (by rfl) ⟨2484791, by rfl⟩ : syracuseStep 3313055 = 4969583) B4969583
theorem B1151315 : Blo 507795 1151315 := bstep (se 1 (by rfl) ⟨863486, by rfl⟩ : syracuseStep 1151315 = 1726973) B1726973
theorem B3217171 : Blo 507795 3217171 := bstep (se 1 (by rfl) ⟨2412878, by rfl⟩ : syracuseStep 3217171 = 4825757) B4825757
theorem B858107 : Blo 507795 858107 := bstep (se 1 (by rfl) ⟨643580, by rfl⟩ : syracuseStep 858107 = 1287161) B1287161
theorem B858343 : Blo 507795 858343 := bstep (se 1 (by rfl) ⟨643757, by rfl⟩ : syracuseStep 858343 = 1287515) B1287515
theorem B4364705 : Blo 507795 4364705 := bstep (se 2 (by rfl) ⟨1636764, by rfl⟩ : syracuseStep 4364705 = 3273529) B3273529
theorem B728681 : Blo 507795 728681 := bstep (se 2 (by rfl) ⟨273255, by rfl⟩ : syracuseStep 728681 = 546511) B546511
theorem B762335 : Blo 507795 762335 := bstep (se 1 (by rfl) ⟨571751, by rfl⟩ : syracuseStep 762335 = 1143503) B1143503
theorem B5808671 : Blo 507795 5808671 := bstep (se 1 (by rfl) ⟨4356503, by rfl⟩ : syracuseStep 5808671 = 8713007) B8713007
theorem B1287049 : Blo 507795 1287049 := bstep (se 2 (by rfl) ⟨482643, by rfl⟩ : syracuseStep 1287049 = 965287) B965287
theorem B1745803 : Blo 507795 1745803 := bstep (se 1 (by rfl) ⟨1309352, by rfl⟩ : syracuseStep 1745803 = 2618705) B2618705
theorem B4367303 : Blo 507795 4367303 := bstep (se 1 (by rfl) ⟨3275477, by rfl⟩ : syracuseStep 4367303 = 6550955) B6550955
theorem B762857 : Blo 507795 762857 := bstep (se 2 (by rfl) ⟨286071, by rfl⟩ : syracuseStep 762857 = 572143) B572143
theorem B8955197 : Blo 507795 8955197 := bstep (se 3 (by rfl) ⟨1679099, by rfl⟩ : syracuseStep 8955197 = 3358199) B3358199
theorem B3876335 : Blo 507795 3876335 := bstep (se 1 (by rfl) ⟨2907251, by rfl⟩ : syracuseStep 3876335 = 5814503) B5814503
theorem B861799 : Blo 507795 861799 := bstep (se 1 (by rfl) ⟨646349, by rfl⟩ : syracuseStep 861799 = 1292699) B1292699
theorem B763751 : Blo 507795 763751 := bstep (se 1 (by rfl) ⟨572813, by rfl⟩ : syracuseStep 763751 = 1145627) B1145627
theorem B763769 : Blo 507795 763769 := bstep (se 2 (by rfl) ⟨286413, by rfl⟩ : syracuseStep 763769 = 572827) B572827
theorem B764063 : Blo 507795 764063 := bstep (se 1 (by rfl) ⟨573047, by rfl⟩ : syracuseStep 764063 = 1146095) B1146095
theorem B764087 : Blo 507795 764087 := bstep (se 1 (by rfl) ⟨573065, by rfl⟩ : syracuseStep 764087 = 1146131) B1146131
theorem B3254975 : Blo 507795 3254975 := bstep (se 1 (by rfl) ⟨2441231, by rfl⟩ : syracuseStep 3254975 = 4882463) B4882463
theorem B37695131 : Blo 507795 37695131 := bstep (se 1 (by rfl) ⟨28271348, by rfl⟩ : syracuseStep 37695131 = 56542697) B56542697
theorem B765887 : Blo 507795 765887 := bstep (se 1 (by rfl) ⟨574415, by rfl⟩ : syracuseStep 765887 = 1148831) B1148831
theorem B7942207 : Blo 507795 7942207 := bstep (se 1 (by rfl) ⟨5956655, by rfl⟩ : syracuseStep 7942207 = 11913311) B11913311
theorem B766127 : Blo 507795 766127 := bstep (se 1 (by rfl) ⟨574595, by rfl⟩ : syracuseStep 766127 = 1149191) B1149191
theorem B1290431 : Blo 507795 1290431 := bstep (se 1 (by rfl) ⟨967823, by rfl⟩ : syracuseStep 1290431 = 1935647) B1935647
theorem B6992081 : Blo 507795 6992081 := bstep (se 2 (by rfl) ⟨2622030, by rfl⟩ : syracuseStep 6992081 = 5244061) B5244061
theorem B1716551 : Blo 507795 1716551 := bstep (se 1 (by rfl) ⟨1287413, by rfl⟩ : syracuseStep 1716551 = 2574827) B2574827
theorem B767519 : Blo 507795 767519 := bstep (se 1 (by rfl) ⟨575639, by rfl⟩ : syracuseStep 767519 = 1151279) B1151279
theorem B767591 : Blo 507795 767591 := bstep (se 1 (by rfl) ⟨575693, by rfl⟩ : syracuseStep 767591 = 1151387) B1151387
theorem B1292071 : Blo 507795 1292071 := bstep (se 1 (by rfl) ⟨969053, by rfl⟩ : syracuseStep 1292071 = 1938107) B1938107
theorem B571387 : Blo 507795 571387 := bstep (se 1 (by rfl) ⟨428540, by rfl⟩ : syracuseStep 571387 = 857081) B857081
theorem B1293185 : Blo 507795 1293185 := bstep (se 2 (by rfl) ⟨484944, by rfl⟩ : syracuseStep 1293185 = 969889) B969889
theorem B1293479 : Blo 507795 1293479 := bstep (se 1 (by rfl) ⟨970109, by rfl⟩ : syracuseStep 1293479 = 1940219) B1940219
theorem B2178731 : Blo 507795 2178731 := bstep (se 1 (by rfl) ⟨1634048, by rfl⟩ : syracuseStep 2178731 = 3268097) B3268097
theorem B507951 : Blo 507795 507951 := bstep (se 1 (by rfl) ⟨380963, by rfl⟩ : syracuseStep 507951 = 761927) B761927
theorem B508071 : Blo 507795 508071 := bstep (se 1 (by rfl) ⟨381053, by rfl⟩ : syracuseStep 508071 = 762107) B762107
theorem B737695 : Blo 507795 737695 := bstep (se 1 (by rfl) ⟨553271, by rfl⟩ : syracuseStep 737695 = 1106543) B1106543
theorem B508415 : Blo 507795 508415 := bstep (se 1 (by rfl) ⟨381311, by rfl⟩ : syracuseStep 508415 = 762623) B762623
theorem B737839 : Blo 507795 737839 := bstep (se 1 (by rfl) ⟨553379, by rfl⟩ : syracuseStep 737839 = 1106759) B1106759
theorem B508655 : Blo 507795 508655 := bstep (se 1 (by rfl) ⟨381491, by rfl⟩ : syracuseStep 508655 = 762983) B762983
theorem B508955 : Blo 507795 508955 := bstep (se 1 (by rfl) ⟨381716, by rfl⟩ : syracuseStep 508955 = 763433) B763433
theorem B967945 : Blo 507795 967945 := bstep (se 2 (by rfl) ⟨362979, by rfl⟩ : syracuseStep 967945 = 725959) B725959
theorem B6440633 : Blo 507795 6440633 := bstep (se 2 (by rfl) ⟨2415237, by rfl⟩ : syracuseStep 6440633 = 4830475) B4830475
theorem B509787 : Blo 507795 509787 := bstep (se 1 (by rfl) ⟨382340, by rfl⟩ : syracuseStep 509787 = 764681) B764681
theorem B1722707 : Blo 507795 1722707 := bstep (se 1 (by rfl) ⟨1292030, by rfl⟩ : syracuseStep 1722707 = 2584061) B2584061
theorem B8833697 : Blo 507795 8833697 := bstep (se 2 (by rfl) ⟨3312636, by rfl⟩ : syracuseStep 8833697 = 6625273) B6625273
theorem B510671 : Blo 507795 510671 := bstep (se 1 (by rfl) ⟨383003, by rfl⟩ : syracuseStep 510671 = 766007) B766007
theorem B511007 : Blo 507795 511007 := bstep (se 1 (by rfl) ⟨383255, by rfl⟩ : syracuseStep 511007 = 766511) B766511
theorem B2444519 : Blo 507795 2444519 := bstep (se 1 (by rfl) ⟨1833389, by rfl⟩ : syracuseStep 2444519 = 3666779) B3666779
theorem B511335 : Blo 507795 511335 := bstep (se 1 (by rfl) ⟨383501, by rfl⟩ : syracuseStep 511335 = 767003) B767003
theorem B511391 : Blo 507795 511391 := bstep (se 1 (by rfl) ⟨383543, by rfl⟩ : syracuseStep 511391 = 767087) B767087
theorem B511423 : Blo 507795 511423 := bstep (se 1 (by rfl) ⟨383567, by rfl⟩ : syracuseStep 511423 = 767135) B767135
theorem B511771 : Blo 507795 511771 := bstep (se 1 (by rfl) ⟨383828, by rfl⟩ : syracuseStep 511771 = 767657) B767657
theorem B2183071 : Blo 507795 2183071 := bstep (se 1 (by rfl) ⟨1637303, by rfl⟩ : syracuseStep 2183071 = 3274607) B3274607
theorem B14143427 : Blo 507795 14143427 := bstep (se 1 (by rfl) ⟨10607570, by rfl⟩ : syracuseStep 14143427 = 21215141) B21215141
theorem B1726379 : Blo 507795 1726379 := bstep (se 1 (by rfl) ⟨1294784, by rfl⟩ : syracuseStep 1726379 = 2589569) B2589569
theorem B35772509 : Blo 507795 35772509 := bstep (se 3 (by rfl) ⟨6707345, by rfl⟩ : syracuseStep 35772509 = 13414691) B13414691
theorem B3135883 : Blo 507795 3135883 := bstep (se 1 (by rfl) ⟨2351912, by rfl⟩ : syracuseStep 3135883 = 4703825) B4703825
theorem B53533187 : Blo 507795 53533187 := bstep (se 1 (by rfl) ⟨40149890, by rfl⟩ : syracuseStep 53533187 = 80299781) B80299781
theorem B49601159 : Blo 507795 49601159 := bstep (se 1 (by rfl) ⟨37200869, by rfl⟩ : syracuseStep 49601159 = 74401739) B74401739
theorem B1105435 : Blo 507795 1105435 := bstep (se 1 (by rfl) ⟨829076, by rfl⟩ : syracuseStep 1105435 = 1658153) B1658153
theorem B1466281 : Blo 507795 1466281 := bstep (se 2 (by rfl) ⟨549855, by rfl⟩ : syracuseStep 1466281 = 1099711) B1099711
theorem B5792633 : Blo 507795 5792633 := bstep (se 2 (by rfl) ⟨2172237, by rfl⟩ : syracuseStep 5792633 = 4344475) B4344475
theorem B583039 : Blo 507795 583039 := bstep (se 1 (by rfl) ⟨437279, by rfl⟩ : syracuseStep 583039 = 874559) B874559
theorem B2581955 : Blo 507795 2581955 := bstep (se 1 (by rfl) ⟨1936466, by rfl⟩ : syracuseStep 2581955 = 3872933) B3872933
theorem B4909679 : Blo 507795 4909679 := bstep (se 1 (by rfl) ⟨3682259, by rfl⟩ : syracuseStep 4909679 = 7364519) B7364519
theorem B2321131 : Blo 507795 2321131 := bstep (se 1 (by rfl) ⟨1740848, by rfl⟩ : syracuseStep 2321131 = 3481697) B3481697
theorem B5827625 : Blo 507795 5827625 := bstep (se 2 (by rfl) ⟨2185359, by rfl⟩ : syracuseStep 5827625 = 4370719) B4370719
theorem B2583737 : Blo 507795 2583737 := bstep (se 2 (by rfl) ⟨968901, by rfl⟩ : syracuseStep 2583737 = 1937803) B1937803
theorem B1142855 : Blo 507795 1142855 := bstep (se 1 (by rfl) ⟨857141, by rfl⟩ : syracuseStep 1142855 = 1714283) B1714283
theorem B3109103 : Blo 507795 3109103 := bstep (se 1 (by rfl) ⟨2331827, by rfl⟩ : syracuseStep 3109103 = 4663655) B4663655
theorem B2912993 : Blo 507795 2912993 := bstep (se 2 (by rfl) ⟨1092372, by rfl⟩ : syracuseStep 2912993 = 2184745) B2184745
theorem B5797007 : Blo 507795 5797007 := bstep (se 1 (by rfl) ⟨4347755, by rfl⟩ : syracuseStep 5797007 = 8695511) B8695511
theorem B1144295 : Blo 507795 1144295 := bstep (se 1 (by rfl) ⟨858221, by rfl⟩ : syracuseStep 1144295 = 1716443) B1716443
theorem B1144673 : Blo 507795 1144673 := bstep (se 2 (by rfl) ⟨429252, by rfl⟩ : syracuseStep 1144673 = 858505) B858505
theorem B915311 : Blo 507795 915311 := bstep (se 1 (by rfl) ⟨686483, by rfl⟩ : syracuseStep 915311 = 1372967) B1372967
theorem B13924379 : Blo 507795 13924379 := bstep (se 1 (by rfl) ⟨10443284, by rfl⟩ : syracuseStep 13924379 = 20886569) B20886569
theorem B24869267 : Blo 507795 24869267 := bstep (se 1 (by rfl) ⟨18651950, by rfl⟩ : syracuseStep 24869267 = 37303901) B37303901
theorem B1473275 : Blo 507795 1473275 := bstep (se 1 (by rfl) ⟨1104956, by rfl⟩ : syracuseStep 1473275 = 2209913) B2209913
theorem B2620471 : Blo 507795 2620471 := bstep (se 1 (by rfl) ⟨1965353, by rfl⟩ : syracuseStep 2620471 = 3930707) B3930707
theorem B1146023 : Blo 507795 1146023 := bstep (se 1 (by rfl) ⟨859517, by rfl⟩ : syracuseStep 1146023 = 1719035) B1719035
theorem B2588435 : Blo 507795 2588435 := bstep (se 1 (by rfl) ⟨1941326, by rfl⟩ : syracuseStep 2588435 = 3882653) B3882653
theorem B3866615 : Blo 507795 3866615 := bstep (se 1 (by rfl) ⟨2899961, by rfl⟩ : syracuseStep 3866615 = 5799923) B5799923
theorem B983593 : Blo 507795 983593 := bstep (se 2 (by rfl) ⟨368847, by rfl⟩ : syracuseStep 983593 = 737695) B737695
theorem B7340939 : Blo 507795 7340939 := bstep (se 1 (by rfl) ⟨5505704, by rfl⟩ : syracuseStep 7340939 = 11011409) B11011409
theorem B4293755 : Blo 507795 4293755 := bstep (se 1 (by rfl) ⟨3220316, by rfl⟩ : syracuseStep 4293755 = 6440633) B6440633
theorem B1148471 : Blo 507795 1148471 := bstep (se 1 (by rfl) ⟨861353, by rfl⟩ : syracuseStep 1148471 = 1722707) B1722707
theorem B1149065 : Blo 507795 1149065 := bstep (se 2 (by rfl) ⟨430899, by rfl⟩ : syracuseStep 1149065 = 861799) B861799
theorem B3935141 : Blo 507795 3935141 := bstep (se 4 (by rfl) ⟨368919, by rfl⟩ : syracuseStep 3935141 = 737839) B737839
theorem B1150919 : Blo 507795 1150919 := bstep (se 1 (by rfl) ⟨863189, by rfl⟩ : syracuseStep 1150919 = 1726379) B1726379
theorem B35688791 : Blo 507795 35688791 := bstep (se 1 (by rfl) ⟨26766593, by rfl⟩ : syracuseStep 35688791 = 53533187) B53533187
theorem B33067439 : Blo 507795 33067439 := bstep (se 1 (by rfl) ⟨24800579, by rfl⟩ : syracuseStep 33067439 = 49601159) B49601159
theorem B9310949 : Blo 507795 9310949 := bstep (se 4 (by rfl) ⟨872901, by rfl⟩ : syracuseStep 9310949 = 1745803) B1745803
theorem B10589609 : Blo 507795 10589609 := bstep (se 2 (by rfl) ⟨3971103, by rfl⟩ : syracuseStep 10589609 = 7942207) B7942207
theorem B3872447 : Blo 507795 3872447 := bstep (se 1 (by rfl) ⟨2904335, by rfl⟩ : syracuseStep 3872447 = 5808671) B5808671
theorem B5970131 : Blo 507795 5970131 := bstep (se 1 (by rfl) ⟨4477598, by rfl⟩ : syracuseStep 5970131 = 8955197) B8955197
theorem B2169983 : Blo 507795 2169983 := bstep (se 1 (by rfl) ⟨1627487, by rfl⟩ : syracuseStep 2169983 = 3254975) B3254975
theorem B761849 : Blo 507795 761849 := bstep (se 2 (by rfl) ⟨285693, by rfl⟩ : syracuseStep 761849 = 571387) B571387
theorem B761903 : Blo 507795 761903 := bstep (se 1 (by rfl) ⟨571427, by rfl⟩ : syracuseStep 761903 = 1142855) B1142855
theorem B860287 : Blo 507795 860287 := bstep (se 1 (by rfl) ⟨645215, by rfl⟩ : syracuseStep 860287 = 1290431) B1290431
theorem B4661387 : Blo 507795 4661387 := bstep (se 1 (by rfl) ⟨3496040, by rfl⟩ : syracuseStep 4661387 = 6992081) B6992081
theorem B2072735 : Blo 507795 2072735 := bstep (se 1 (by rfl) ⟨1554551, by rfl⟩ : syracuseStep 2072735 = 3109103) B3109103
theorem B1941995 : Blo 507795 1941995 := bstep (se 1 (by rfl) ⟨1456496, by rfl⟩ : syracuseStep 1941995 = 2912993) B2912993
theorem B762863 : Blo 507795 762863 := bstep (se 1 (by rfl) ⟨572147, by rfl⟩ : syracuseStep 762863 = 1144295) B1144295
theorem B763115 : Blo 507795 763115 := bstep (se 1 (by rfl) ⟨572336, by rfl⟩ : syracuseStep 763115 = 1144673) B1144673
theorem B9282919 : Blo 507795 9282919 := bstep (se 1 (by rfl) ⟨6962189, by rfl⟩ : syracuseStep 9282919 = 13924379) B13924379
theorem B1943149 : Blo 507795 1943149 := bstep (se 3 (by rfl) ⟨364340, by rfl⟩ : syracuseStep 1943149 = 728681) B728681
theorem B862123 : Blo 507795 862123 := bstep (se 1 (by rfl) ⟨646592, by rfl⟩ : syracuseStep 862123 = 1293185) B1293185
theorem B764015 : Blo 507795 764015 := bstep (se 1 (by rfl) ⟨573011, by rfl⟩ : syracuseStep 764015 = 1146023) B1146023
theorem B862319 : Blo 507795 862319 := bstep (se 1 (by rfl) ⟨646739, by rfl⟩ : syracuseStep 862319 = 1293479) B1293479
theorem B1452487 : Blo 507795 1452487 := bstep (se 1 (by rfl) ⟨1089365, by rfl⟩ : syracuseStep 1452487 = 2178731) B2178731
theorem B764651 : Blo 507795 764651 := bstep (se 1 (by rfl) ⟨573488, by rfl⟩ : syracuseStep 764651 = 1146977) B1146977
theorem B1716065 : Blo 507795 1716065 := bstep (se 2 (by rfl) ⟨643524, by rfl⟩ : syracuseStep 1716065 = 1287049) B1287049
theorem B1290593 : Blo 507795 1290593 := bstep (se 2 (by rfl) ⟨483972, by rfl⟩ : syracuseStep 1290593 = 967945) B967945
theorem B6205835 : Blo 507795 6205835 := bstep (se 1 (by rfl) ⟨4654376, by rfl⟩ : syracuseStep 6205835 = 9308753) B9308753
theorem B766463 : Blo 507795 766463 := bstep (se 1 (by rfl) ⟨574847, by rfl⟩ : syracuseStep 766463 = 1149695) B1149695
theorem B2208703 : Blo 507795 2208703 := bstep (se 1 (by rfl) ⟨1656527, by rfl⟩ : syracuseStep 2208703 = 3313055) B3313055
theorem B767543 : Blo 507795 767543 := bstep (se 1 (by rfl) ⟨575657, by rfl⟩ : syracuseStep 767543 = 1151315) B1151315
theorem B3094841 : Blo 507795 3094841 := bstep (se 2 (by rfl) ⟨1160565, by rfl⟩ : syracuseStep 3094841 = 2321131) B2321131
theorem B572071 : Blo 507795 572071 := bstep (se 1 (by rfl) ⟨429053, by rfl⟩ : syracuseStep 572071 = 858107) B858107
theorem B2440829 : Blo 507795 2440829 := bstep (se 3 (by rfl) ⟨457655, by rfl⟩ : syracuseStep 2440829 = 915311) B915311
theorem B508223 : Blo 507795 508223 := bstep (se 1 (by rfl) ⟨381167, by rfl⟩ : syracuseStep 508223 = 762335) B762335
theorem B508571 : Blo 507795 508571 := bstep (se 1 (by rfl) ⟨381428, by rfl⟩ : syracuseStep 508571 = 762857) B762857
theorem B1721303 : Blo 507795 1721303 := bstep (se 1 (by rfl) ⟨1290977, by rfl⟩ : syracuseStep 1721303 = 2581955) B2581955
theorem B509167 : Blo 507795 509167 := bstep (se 1 (by rfl) ⟨381875, by rfl⟩ : syracuseStep 509167 = 763751) B763751
theorem B509179 : Blo 507795 509179 := bstep (se 1 (by rfl) ⟨381884, by rfl⟩ : syracuseStep 509179 = 763769) B763769
theorem B509375 : Blo 507795 509375 := bstep (se 1 (by rfl) ⟨382031, by rfl⟩ : syracuseStep 509375 = 764063) B764063
theorem B509391 : Blo 507795 509391 := bstep (se 1 (by rfl) ⟨382043, by rfl⟩ : syracuseStep 509391 = 764087) B764087
theorem B3885083 : Blo 507795 3885083 := bstep (se 1 (by rfl) ⟨2913812, by rfl⟩ : syracuseStep 3885083 = 5827625) B5827625
theorem B1722491 : Blo 507795 1722491 := bstep (se 1 (by rfl) ⟨1291868, by rfl⟩ : syracuseStep 1722491 = 2583737) B2583737
theorem B1722761 : Blo 507795 1722761 := bstep (se 2 (by rfl) ⟨646035, by rfl⟩ : syracuseStep 1722761 = 1292071) B1292071
theorem B510591 : Blo 507795 510591 := bstep (se 1 (by rfl) ⟨382943, by rfl⟩ : syracuseStep 510591 = 765887) B765887
theorem B510751 : Blo 507795 510751 := bstep (se 1 (by rfl) ⟨383063, by rfl⟩ : syracuseStep 510751 = 766127) B766127
theorem B4181177 : Blo 507795 4181177 := bstep (se 2 (by rfl) ⟨1567941, by rfl⟩ : syracuseStep 4181177 = 3135883) B3135883
theorem B511679 : Blo 507795 511679 := bstep (se 1 (by rfl) ⟨383759, by rfl⟩ : syracuseStep 511679 = 767519) B767519
theorem B511727 : Blo 507795 511727 := bstep (se 1 (by rfl) ⟨383795, by rfl⟩ : syracuseStep 511727 = 767591) B767591
theorem B3493961 : Blo 507795 3493961 := bstep (se 2 (by rfl) ⟨1310235, by rfl⟩ : syracuseStep 3493961 = 2620471) B2620471
theorem B7820165 : Blo 507795 7820165 := bstep (se 4 (by rfl) ⟨733140, by rfl⟩ : syracuseStep 7820165 = 1466281) B1466281
theorem B1725623 : Blo 507795 1725623 := bstep (se 1 (by rfl) ⟨1294217, by rfl⟩ : syracuseStep 1725623 = 2588435) B2588435
theorem B2577743 : Blo 507795 2577743 := bstep (se 1 (by rfl) ⟨1933307, by rfl⟩ : syracuseStep 2577743 = 3866615) B3866615
theorem B5889131 : Blo 507795 5889131 := bstep (se 1 (by rfl) ⟨4416848, by rfl⟩ : syracuseStep 5889131 = 8833697) B8833697
theorem B777385 : Blo 507795 777385 := bstep (se 2 (by rfl) ⟨291519, by rfl⟩ : syracuseStep 777385 = 583039) B583039
theorem B2579687 : Blo 507795 2579687 := bstep (se 1 (by rfl) ⟨1934765, by rfl⟩ : syracuseStep 2579687 = 3869531) B3869531
theorem B9428951 : Blo 507795 9428951 := bstep (se 1 (by rfl) ⟨7071713, by rfl⟩ : syracuseStep 9428951 = 14143427) B14143427
theorem B23848339 : Blo 507795 23848339 := bstep (se 1 (by rfl) ⟨17886254, by rfl⟩ : syracuseStep 23848339 = 35772509) B35772509
theorem B2909803 : Blo 507795 2909803 := bstep (se 1 (by rfl) ⟨2182352, by rfl⟩ : syracuseStep 2909803 = 4364705) B4364705
theorem B2910761 : Blo 507795 2910761 := bstep (se 2 (by rfl) ⟨1091535, by rfl⟩ : syracuseStep 2910761 = 2183071) B2183071
theorem B3861755 : Blo 507795 3861755 := bstep (se 1 (by rfl) ⟨2896316, by rfl⟩ : syracuseStep 3861755 = 5792633) B5792633
theorem B2911535 : Blo 507795 2911535 := bstep (se 1 (by rfl) ⟨2183651, by rfl⟩ : syracuseStep 2911535 = 4367303) B4367303
theorem B2584223 : Blo 507795 2584223 := bstep (se 1 (by rfl) ⟨1938167, by rfl⟩ : syracuseStep 2584223 = 3876335) B3876335
theorem B3273119 : Blo 507795 3273119 := bstep (se 1 (by rfl) ⟨2454839, by rfl⟩ : syracuseStep 3273119 = 4909679) B4909679
theorem B3928733 : Blo 507795 3928733 := bstep (se 3 (by rfl) ⟨736637, by rfl⟩ : syracuseStep 3928733 = 1473275) B1473275
theorem B4289561 : Blo 507795 4289561 := bstep (se 2 (by rfl) ⟨1608585, by rfl⟩ : syracuseStep 4289561 = 3217171) B3217171
theorem B25130087 : Blo 507795 25130087 := bstep (se 1 (by rfl) ⟨18847565, by rfl⟩ : syracuseStep 25130087 = 37695131) B37695131
theorem B1144367 : Blo 507795 1144367 := bstep (se 1 (by rfl) ⟨858275, by rfl⟩ : syracuseStep 1144367 = 1716551) B1716551
theorem B1144457 : Blo 507795 1144457 := bstep (se 2 (by rfl) ⟨429171, by rfl⟩ : syracuseStep 1144457 = 858343) B858343
theorem B6518717 : Blo 507795 6518717 := bstep (se 3 (by rfl) ⟨1222259, by rfl⟩ : syracuseStep 6518717 = 2444519) B2444519
theorem B3864671 : Blo 507795 3864671 := bstep (se 1 (by rfl) ⟨2898503, by rfl⟩ : syracuseStep 3864671 = 5797007) B5797007
theorem B16579511 : Blo 507795 16579511 := bstep (se 1 (by rfl) ⟨12434633, by rfl⟩ : syracuseStep 16579511 = 24869267) B24869267
theorem B1473913 : Blo 507795 1473913 := bstep (se 2 (by rfl) ⟨552717, by rfl⟩ : syracuseStep 1473913 = 1105435) B1105435
theorem B1147049 : Blo 507795 1147049 := bstep (se 2 (by rfl) ⟨430143, by rfl⟩ : syracuseStep 1147049 = 860287) B860287
theorem B1147535 : Blo 507795 1147535 := bstep (se 1 (by rfl) ⟨860651, by rfl⟩ : syracuseStep 1147535 = 1721303) B1721303
theorem B16548893 : Blo 507795 16548893 := bstep (se 3 (by rfl) ⟨3102917, by rfl⟩ : syracuseStep 16548893 = 6205835) B6205835
theorem B2590055 : Blo 507795 2590055 := bstep (se 1 (by rfl) ⟨1942541, by rfl⟩ : syracuseStep 2590055 = 3885083) B3885083
theorem B1148327 : Blo 507795 1148327 := bstep (se 1 (by rfl) ⟨861245, by rfl⟩ : syracuseStep 1148327 = 1722491) B1722491
theorem B1148507 : Blo 507795 1148507 := bstep (se 1 (by rfl) ⟨861380, by rfl⟩ : syracuseStep 1148507 = 1722761) B1722761
theorem B2623427 : Blo 507795 2623427 := bstep (se 1 (by rfl) ⟨1967570, by rfl⟩ : syracuseStep 2623427 = 3935141) B3935141
theorem B2590865 : Blo 507795 2590865 := bstep (se 2 (by rfl) ⟨971574, by rfl⟩ : syracuseStep 2590865 = 1943149) B1943149
theorem B1149497 : Blo 507795 1149497 := bstep (se 2 (by rfl) ⟨431061, by rfl⟩ : syracuseStep 1149497 = 862123) B862123
theorem B2329307 : Blo 507795 2329307 := bstep (se 1 (by rfl) ⟨1746980, by rfl⟩ : syracuseStep 2329307 = 3493961) B3493961
theorem B5245829 : Blo 507795 5245829 := bstep (se 4 (by rfl) ⟨491796, by rfl⟩ : syracuseStep 5245829 = 983593) B983593
theorem B23792527 : Blo 507795 23792527 := bstep (se 1 (by rfl) ⟨17844395, by rfl⟩ : syracuseStep 23792527 = 35688791) B35688791
theorem B5213443 : Blo 507795 5213443 := bstep (se 1 (by rfl) ⟨3910082, by rfl⟩ : syracuseStep 5213443 = 7820165) B7820165
theorem B1936649 : Blo 507795 1936649 := bstep (se 2 (by rfl) ⟨726243, by rfl⟩ : syracuseStep 1936649 = 1452487) B1452487
theorem B1150415 : Blo 507795 1150415 := bstep (se 1 (by rfl) ⟨862811, by rfl⟩ : syracuseStep 1150415 = 1725623) B1725623
theorem B1446655 : Blo 507795 1446655 := bstep (se 1 (by rfl) ⟨1084991, by rfl⟩ : syracuseStep 1446655 = 2169983) B2169983
theorem B1381823 : Blo 507795 1381823 := bstep (se 1 (by rfl) ⟨1036367, by rfl⟩ : syracuseStep 1381823 = 2072735) B2072735
theorem B1940507 : Blo 507795 1940507 := bstep (se 1 (by rfl) ⟨1455380, by rfl⟩ : syracuseStep 1940507 = 2910761) B2910761
theorem B1941023 : Blo 507795 1941023 := bstep (se 1 (by rfl) ⟨1455767, by rfl⟩ : syracuseStep 1941023 = 2911535) B2911535
theorem B860395 : Blo 507795 860395 := bstep (se 1 (by rfl) ⟨645296, by rfl⟩ : syracuseStep 860395 = 1290593) B1290593
theorem B11149805 : Blo 507795 11149805 := bstep (se 3 (by rfl) ⟨2090588, by rfl⟩ : syracuseStep 11149805 = 4181177) B4181177
theorem B2859707 : Blo 507795 2859707 := bstep (se 1 (by rfl) ⟨2144780, by rfl⟩ : syracuseStep 2859707 = 4289561) B4289561
theorem B16753391 : Blo 507795 16753391 := bstep (se 1 (by rfl) ⟨12565043, by rfl⟩ : syracuseStep 16753391 = 25130087) B25130087
theorem B762761 : Blo 507795 762761 := bstep (se 2 (by rfl) ⟨286035, by rfl⟩ : syracuseStep 762761 = 572071) B572071
theorem B762911 : Blo 507795 762911 := bstep (se 1 (by rfl) ⟨572183, by rfl⟩ : syracuseStep 762911 = 1144367) B1144367
theorem B762971 : Blo 507795 762971 := bstep (se 1 (by rfl) ⟨572228, by rfl⟩ : syracuseStep 762971 = 1144457) B1144457
theorem B11053007 : Blo 507795 11053007 := bstep (se 1 (by rfl) ⟨8289755, by rfl⟩ : syracuseStep 11053007 = 16579511) B16579511
theorem B4893959 : Blo 507795 4893959 := bstep (se 1 (by rfl) ⟨3670469, by rfl⟩ : syracuseStep 4893959 = 7340939) B7340939
theorem B2862503 : Blo 507795 2862503 := bstep (se 1 (by rfl) ⟨2146877, by rfl⟩ : syracuseStep 2862503 = 4293755) B4293755
theorem B765647 : Blo 507795 765647 := bstep (se 1 (by rfl) ⟨574235, by rfl⟩ : syracuseStep 765647 = 1148471) B1148471
theorem B766043 : Blo 507795 766043 := bstep (se 1 (by rfl) ⟨574532, by rfl⟩ : syracuseStep 766043 = 1149065) B1149065
theorem B31797785 : Blo 507795 31797785 := bstep (se 2 (by rfl) ⟨11924169, by rfl⟩ : syracuseStep 31797785 = 23848339) B23848339
theorem B3879737 : Blo 507795 3879737 := bstep (se 2 (by rfl) ⟨1454901, by rfl⟩ : syracuseStep 3879737 = 2909803) B2909803
theorem B767279 : Blo 507795 767279 := bstep (se 1 (by rfl) ⟨575459, by rfl⟩ : syracuseStep 767279 = 1150919) B1150919
theorem B6207299 : Blo 507795 6207299 := bstep (se 1 (by rfl) ⟨4655474, by rfl⟩ : syracuseStep 6207299 = 9310949) B9310949
theorem B1718495 : Blo 507795 1718495 := bstep (se 1 (by rfl) ⟨1288871, by rfl⟩ : syracuseStep 1718495 = 2577743) B2577743
theorem B7059739 : Blo 507795 7059739 := bstep (se 1 (by rfl) ⟨5294804, by rfl⟩ : syracuseStep 7059739 = 10589609) B10589609
theorem B3980087 : Blo 507795 3980087 := bstep (se 1 (by rfl) ⟨2985065, by rfl⟩ : syracuseStep 3980087 = 5970131) B5970131
theorem B1719791 : Blo 507795 1719791 := bstep (se 1 (by rfl) ⟨1289843, by rfl⟩ : syracuseStep 1719791 = 2579687) B2579687
theorem B507899 : Blo 507795 507899 := bstep (se 1 (by rfl) ⟨380924, by rfl⟩ : syracuseStep 507899 = 761849) B761849
theorem B507935 : Blo 507795 507935 := bstep (se 1 (by rfl) ⟨380951, by rfl⟩ : syracuseStep 507935 = 761903) B761903
theorem B1294663 : Blo 507795 1294663 := bstep (se 1 (by rfl) ⟨970997, by rfl⟩ : syracuseStep 1294663 = 1941995) B1941995
theorem B508575 : Blo 507795 508575 := bstep (se 1 (by rfl) ⟨381431, by rfl⟩ : syracuseStep 508575 = 762863) B762863
theorem B508743 : Blo 507795 508743 := bstep (se 1 (by rfl) ⟨381557, by rfl⟩ : syracuseStep 508743 = 763115) B763115
theorem B509343 : Blo 507795 509343 := bstep (se 1 (by rfl) ⟨382007, by rfl⟩ : syracuseStep 509343 = 764015) B764015
theorem B574879 : Blo 507795 574879 := bstep (se 1 (by rfl) ⟨431159, by rfl⟩ : syracuseStep 574879 = 862319) B862319
theorem B509767 : Blo 507795 509767 := bstep (se 1 (by rfl) ⟨382325, by rfl⟩ : syracuseStep 509767 = 764651) B764651
theorem B2574503 : Blo 507795 2574503 := bstep (se 1 (by rfl) ⟨1930877, by rfl⟩ : syracuseStep 2574503 = 3861755) B3861755
theorem B1722815 : Blo 507795 1722815 := bstep (se 1 (by rfl) ⟨1292111, by rfl⟩ : syracuseStep 1722815 = 2584223) B2584223
theorem B2182079 : Blo 507795 2182079 := bstep (se 1 (by rfl) ⟨1636559, by rfl⟩ : syracuseStep 2182079 = 3273119) B3273119
theorem B510975 : Blo 507795 510975 := bstep (se 1 (by rfl) ⟨383231, by rfl⟩ : syracuseStep 510975 = 766463) B766463
theorem B511695 : Blo 507795 511695 := bstep (se 1 (by rfl) ⟨383771, by rfl⟩ : syracuseStep 511695 = 767543) B767543
theorem B4345811 : Blo 507795 4345811 := bstep (se 1 (by rfl) ⟨3259358, by rfl⟩ : syracuseStep 4345811 = 6518717) B6518717
theorem B2576447 : Blo 507795 2576447 := bstep (se 1 (by rfl) ⟨1932335, by rfl⟩ : syracuseStep 2576447 = 3864671) B3864671
theorem B1036513 : Blo 507795 1036513 := bstep (se 2 (by rfl) ⟨388692, by rfl⟩ : syracuseStep 1036513 = 777385) B777385
theorem B1627219 : Blo 507795 1627219 := bstep (se 1 (by rfl) ⟨1220414, by rfl⟩ : syracuseStep 1627219 = 2440829) B2440829
theorem B12377225 : Blo 507795 12377225 := bstep (se 2 (by rfl) ⟨4641459, by rfl⟩ : syracuseStep 12377225 = 9282919) B9282919
theorem B22044959 : Blo 507795 22044959 := bstep (se 1 (by rfl) ⟨16533719, by rfl⟩ : syracuseStep 22044959 = 33067439) B33067439
theorem B2581631 : Blo 507795 2581631 := bstep (se 1 (by rfl) ⟨1936223, by rfl⟩ : syracuseStep 2581631 = 3872447) B3872447
theorem B3926087 : Blo 507795 3926087 := bstep (se 1 (by rfl) ⟨2944565, by rfl⟩ : syracuseStep 3926087 = 5889131) B5889131
theorem B6285967 : Blo 507795 6285967 := bstep (se 1 (by rfl) ⟨4714475, by rfl⟩ : syracuseStep 6285967 = 9428951) B9428951
theorem B3107591 : Blo 507795 3107591 := bstep (se 1 (by rfl) ⟨2330693, by rfl⟩ : syracuseStep 3107591 = 4661387) B4661387
theorem B2944937 : Blo 507795 2944937 := bstep (se 2 (by rfl) ⟨1104351, by rfl⟩ : syracuseStep 2944937 = 2208703) B2208703
theorem B1144043 : Blo 507795 1144043 := bstep (se 1 (by rfl) ⟨858032, by rfl⟩ : syracuseStep 1144043 = 1716065) B1716065
theorem B2619155 : Blo 507795 2619155 := bstep (se 1 (by rfl) ⟨1964366, by rfl⟩ : syracuseStep 2619155 = 3928733) B3928733
theorem B2063227 : Blo 507795 2063227 := bstep (se 1 (by rfl) ⟨1547420, by rfl⟩ : syracuseStep 2063227 = 3094841) B3094841
theorem B1965217 : Blo 507795 1965217 := bstep (se 2 (by rfl) ⟨736956, by rfl⟩ : syracuseStep 1965217 = 1473913) B1473913
theorem B1147193 : Blo 507795 1147193 := bstep (se 2 (by rfl) ⟨430197, by rfl⟩ : syracuseStep 1147193 = 860395) B860395
theorem B1148543 : Blo 507795 1148543 := bstep (se 1 (by rfl) ⟨861407, by rfl⟩ : syracuseStep 1148543 = 1722815) B1722815
theorem B921215 : Blo 507795 921215 := bstep (se 1 (by rfl) ⟨690911, by rfl⟩ : syracuseStep 921215 = 1381823) B1381823
theorem B31723369 : Blo 507795 31723369 := bstep (se 2 (by rfl) ⟨11896263, by rfl⟩ : syracuseStep 31723369 = 23792527) B23792527
theorem B6951257 : Blo 507795 6951257 := bstep (se 2 (by rfl) ⟨2606721, by rfl⟩ : syracuseStep 6951257 = 5213443) B5213443
theorem B6984413 : Blo 507795 6984413 := bstep (se 3 (by rfl) ⟨1309577, by rfl⟩ : syracuseStep 6984413 = 2619155) B2619155
theorem B1382017 : Blo 507795 1382017 := bstep (se 2 (by rfl) ⟨518256, by rfl⟩ : syracuseStep 1382017 = 1036513) B1036513
theorem B1906471 : Blo 507795 1906471 := bstep (se 1 (by rfl) ⟨1429853, by rfl⟩ : syracuseStep 1906471 = 2859707) B2859707
theorem B2169625 : Blo 507795 2169625 := bstep (se 2 (by rfl) ⟨813609, by rfl⟩ : syracuseStep 2169625 = 1627219) B1627219
theorem B2071727 : Blo 507795 2071727 := bstep (se 1 (by rfl) ⟨1553795, by rfl⟩ : syracuseStep 2071727 = 3107591) B3107591
theorem B1908335 : Blo 507795 1908335 := bstep (se 1 (by rfl) ⟨1431251, by rfl⟩ : syracuseStep 1908335 = 2862503) B2862503
theorem B9412985 : Blo 507795 9412985 := bstep (se 2 (by rfl) ⟨3529869, by rfl⟩ : syracuseStep 9412985 = 7059739) B7059739
theorem B762695 : Blo 507795 762695 := bstep (se 1 (by rfl) ⟨572021, by rfl⟩ : syracuseStep 762695 = 1144043) B1144043
theorem B4138199 : Blo 507795 4138199 := bstep (se 1 (by rfl) ⟨3103649, by rfl⟩ : syracuseStep 4138199 = 6207299) B6207299
theorem B764699 : Blo 507795 764699 := bstep (se 1 (by rfl) ⟨573524, by rfl⟩ : syracuseStep 764699 = 1147049) B1147049
theorem B765023 : Blo 507795 765023 := bstep (se 1 (by rfl) ⟨573767, by rfl⟩ : syracuseStep 765023 = 1147535) B1147535
theorem B765551 : Blo 507795 765551 := bstep (se 1 (by rfl) ⟨574163, by rfl⟩ : syracuseStep 765551 = 1148327) B1148327
theorem B765671 : Blo 507795 765671 := bstep (se 1 (by rfl) ⟨574253, by rfl⟩ : syracuseStep 765671 = 1148507) B1148507
theorem B1748951 : Blo 507795 1748951 := bstep (se 1 (by rfl) ⟨1311713, by rfl⟩ : syracuseStep 1748951 = 2623427) B2623427
theorem B1716335 : Blo 507795 1716335 := bstep (se 1 (by rfl) ⟨1287251, by rfl⟩ : syracuseStep 1716335 = 2574503) B2574503
theorem B766331 : Blo 507795 766331 := bstep (se 1 (by rfl) ⟨574748, by rfl⟩ : syracuseStep 766331 = 1149497) B1149497
theorem B1552871 : Blo 507795 1552871 := bstep (se 1 (by rfl) ⟨1164653, by rfl⟩ : syracuseStep 1552871 = 2329307) B2329307
theorem B766505 : Blo 507795 766505 := bstep (se 2 (by rfl) ⟨287439, by rfl⟩ : syracuseStep 766505 = 574879) B574879
theorem B1291099 : Blo 507795 1291099 := bstep (se 1 (by rfl) ⟨968324, by rfl⟩ : syracuseStep 1291099 = 1936649) B1936649
theorem B766943 : Blo 507795 766943 := bstep (se 1 (by rfl) ⟨575207, by rfl⟩ : syracuseStep 766943 = 1150415) B1150415
theorem B2897207 : Blo 507795 2897207 := bstep (se 1 (by rfl) ⟨2172905, by rfl⟩ : syracuseStep 2897207 = 4345811) B4345811
theorem B1717631 : Blo 507795 1717631 := bstep (se 1 (by rfl) ⟨1288223, by rfl⟩ : syracuseStep 1717631 = 2576447) B2576447
theorem B134100629 : Blo 507795 134100629 := bstep (se 6 (by rfl) ⟨3142983, by rfl⟩ : syracuseStep 134100629 = 6285967) B6285967
theorem B1293671 : Blo 507795 1293671 := bstep (se 1 (by rfl) ⟨970253, by rfl⟩ : syracuseStep 1293671 = 1940507) B1940507
theorem B1294015 : Blo 507795 1294015 := bstep (se 1 (by rfl) ⟨970511, by rfl⟩ : syracuseStep 1294015 = 1941023) B1941023
theorem B14696639 : Blo 507795 14696639 := bstep (se 1 (by rfl) ⟨11022479, by rfl⟩ : syracuseStep 14696639 = 22044959) B22044959
theorem B508507 : Blo 507795 508507 := bstep (se 1 (by rfl) ⟨381380, by rfl⟩ : syracuseStep 508507 = 762761) B762761
theorem B508607 : Blo 507795 508607 := bstep (se 1 (by rfl) ⟨381455, by rfl⟩ : syracuseStep 508607 = 762911) B762911
theorem B508647 : Blo 507795 508647 := bstep (se 1 (by rfl) ⟨381485, by rfl⟩ : syracuseStep 508647 = 762971) B762971
theorem B1721087 : Blo 507795 1721087 := bstep (se 1 (by rfl) ⟨1290815, by rfl⟩ : syracuseStep 1721087 = 2581631) B2581631
theorem B3262639 : Blo 507795 3262639 := bstep (se 1 (by rfl) ⟨2446979, by rfl⟩ : syracuseStep 3262639 = 4893959) B4893959
theorem B510431 : Blo 507795 510431 := bstep (se 1 (by rfl) ⟨382823, by rfl⟩ : syracuseStep 510431 = 765647) B765647
theorem B5818877 : Blo 507795 5818877 := bstep (se 3 (by rfl) ⟨1091039, by rfl⟩ : syracuseStep 5818877 = 2182079) B2182079
theorem B510695 : Blo 507795 510695 := bstep (se 1 (by rfl) ⟨383021, by rfl⟩ : syracuseStep 510695 = 766043) B766043
theorem B511519 : Blo 507795 511519 := bstep (se 1 (by rfl) ⟨383639, by rfl⟩ : syracuseStep 511519 = 767279) B767279
theorem B1726217 : Blo 507795 1726217 := bstep (se 2 (by rfl) ⟨647331, by rfl⟩ : syracuseStep 1726217 = 1294663) B1294663
theorem B11032595 : Blo 507795 11032595 := bstep (se 1 (by rfl) ⟨8274446, by rfl⟩ : syracuseStep 11032595 = 16548893) B16548893
theorem B1726703 : Blo 507795 1726703 := bstep (se 1 (by rfl) ⟨1295027, by rfl⟩ : syracuseStep 1726703 = 2590055) B2590055
theorem B1727243 : Blo 507795 1727243 := bstep (se 1 (by rfl) ⟨1295432, by rfl⟩ : syracuseStep 1727243 = 2590865) B2590865
theorem B3497219 : Blo 507795 3497219 := bstep (se 1 (by rfl) ⟨2622914, by rfl⟩ : syracuseStep 3497219 = 5245829) B5245829
theorem B8251483 : Blo 507795 8251483 := bstep (se 1 (by rfl) ⟨6188612, by rfl⟩ : syracuseStep 8251483 = 12377225) B12377225
theorem B7433203 : Blo 507795 7433203 := bstep (se 1 (by rfl) ⟨5574902, by rfl⟩ : syracuseStep 7433203 = 11149805) B11149805
theorem B11168927 : Blo 507795 11168927 := bstep (se 1 (by rfl) ⟨8376695, by rfl⟩ : syracuseStep 11168927 = 16753391) B16753391
theorem B1928873 : Blo 507795 1928873 := bstep (se 2 (by rfl) ⟨723327, by rfl⟩ : syracuseStep 1928873 = 1446655) B1446655
theorem B7368671 : Blo 507795 7368671 := bstep (se 1 (by rfl) ⟨5526503, by rfl⟩ : syracuseStep 7368671 = 11053007) B11053007
theorem B2617391 : Blo 507795 2617391 := bstep (se 1 (by rfl) ⟨1963043, by rfl⟩ : syracuseStep 2617391 = 3926087) B3926087
theorem B1963291 : Blo 507795 1963291 := bstep (se 1 (by rfl) ⟨1472468, by rfl⟩ : syracuseStep 1963291 = 2944937) B2944937
theorem B21198523 : Blo 507795 21198523 := bstep (se 1 (by rfl) ⟨15898892, by rfl⟩ : syracuseStep 21198523 = 31797785) B31797785
theorem B2586491 : Blo 507795 2586491 := bstep (se 1 (by rfl) ⟨1939868, by rfl⟩ : syracuseStep 2586491 = 3879737) B3879737
theorem B2750969 : Blo 507795 2750969 := bstep (se 2 (by rfl) ⟨1031613, by rfl⟩ : syracuseStep 2750969 = 2063227) B2063227
theorem B1145663 : Blo 507795 1145663 := bstep (se 1 (by rfl) ⟨859247, by rfl⟩ : syracuseStep 1145663 = 1718495) B1718495
theorem B2620289 : Blo 507795 2620289 := bstep (se 2 (by rfl) ⟨982608, by rfl⟩ : syracuseStep 2620289 = 1965217) B1965217
theorem B2653391 : Blo 507795 2653391 := bstep (se 1 (by rfl) ⟨1990043, by rfl⟩ : syracuseStep 2653391 = 3980087) B3980087
theorem B1146527 : Blo 507795 1146527 := bstep (se 1 (by rfl) ⟨859895, by rfl⟩ : syracuseStep 1146527 = 1719791) B1719791
theorem B6979709 : Blo 507795 6979709 := bstep (se 3 (by rfl) ⟨1308695, by rfl⟩ : syracuseStep 6979709 = 2617391) B2617391
theorem B9797759 : Blo 507795 9797759 := bstep (se 1 (by rfl) ⟨7348319, by rfl⟩ : syracuseStep 9797759 = 14696639) B14696639
theorem B1147391 : Blo 507795 1147391 := bstep (se 1 (by rfl) ⟨860543, by rfl⟩ : syracuseStep 1147391 = 1721087) B1721087
theorem B4656275 : Blo 507795 4656275 := bstep (se 1 (by rfl) ⟨3492206, by rfl⟩ : syracuseStep 4656275 = 6984413) B6984413
theorem B1150811 : Blo 507795 1150811 := bstep (se 1 (by rfl) ⟨863108, by rfl⟩ : syracuseStep 1150811 = 1726217) B1726217
theorem B1151135 : Blo 507795 1151135 := bstep (se 1 (by rfl) ⟨863351, by rfl⟩ : syracuseStep 1151135 = 1726703) B1726703
theorem B1151495 : Blo 507795 1151495 := bstep (se 1 (by rfl) ⟨863621, by rfl⟩ : syracuseStep 1151495 = 1727243) B1727243
theorem B1381151 : Blo 507795 1381151 := bstep (se 1 (by rfl) ⟨1035863, by rfl⟩ : syracuseStep 1381151 = 2071727) B2071727
theorem B2331479 : Blo 507795 2331479 := bstep (se 1 (by rfl) ⟨1748609, by rfl⟩ : syracuseStep 2331479 = 3497219) B3497219
theorem B2758799 : Blo 507795 2758799 := bstep (se 1 (by rfl) ⟨2069099, by rfl⟩ : syracuseStep 2758799 = 4138199) B4138199
theorem B7445951 : Blo 507795 7445951 := bstep (se 1 (by rfl) ⟨5584463, by rfl⟩ : syracuseStep 7445951 = 11168927) B11168927
theorem B1842689 : Blo 507795 1842689 := bstep (se 2 (by rfl) ⟨691008, by rfl⟩ : syracuseStep 1842689 = 1382017) B1382017
theorem B676765205 : Blo 507795 676765205 := bstep (se 6 (by rfl) ⟨15861684, by rfl⟩ : syracuseStep 676765205 = 31723369) B31723369
theorem B1285915 : Blo 507795 1285915 := bstep (se 1 (by rfl) ⟨964436, by rfl⟩ : syracuseStep 1285915 = 1928873) B1928873
theorem B2892833 : Blo 507795 2892833 := bstep (se 2 (by rfl) ⟨1084812, by rfl⟩ : syracuseStep 2892833 = 2169625) B2169625
theorem B89400419 : Blo 507795 89400419 := bstep (se 1 (by rfl) ⟨67050314, by rfl⟩ : syracuseStep 89400419 = 134100629) B134100629
theorem B763775 : Blo 507795 763775 := bstep (se 1 (by rfl) ⟨572831, by rfl⟩ : syracuseStep 763775 = 1145663) B1145663
theorem B1746859 : Blo 507795 1746859 := bstep (se 1 (by rfl) ⟨1310144, by rfl⟩ : syracuseStep 1746859 = 2620289) B2620289
theorem B862447 : Blo 507795 862447 := bstep (se 1 (by rfl) ⟨646835, by rfl⟩ : syracuseStep 862447 = 1293671) B1293671
theorem B764351 : Blo 507795 764351 := bstep (se 1 (by rfl) ⟨573263, by rfl⟩ : syracuseStep 764351 = 1146527) B1146527
theorem B764795 : Blo 507795 764795 := bstep (se 1 (by rfl) ⟨573596, by rfl⟩ : syracuseStep 764795 = 1147193) B1147193
theorem B765695 : Blo 507795 765695 := bstep (se 1 (by rfl) ⟨574271, by rfl⟩ : syracuseStep 765695 = 1148543) B1148543
theorem B3879251 : Blo 507795 3879251 := bstep (se 1 (by rfl) ⟨2909438, by rfl⟩ : syracuseStep 3879251 = 5818877) B5818877
theorem B4634171 : Blo 507795 4634171 := bstep (se 1 (by rfl) ⟨3475628, by rfl⟩ : syracuseStep 4634171 = 6951257) B6951257
theorem B9910937 : Blo 507795 9910937 := bstep (se 2 (by rfl) ⟨3716601, by rfl⟩ : syracuseStep 9910937 = 7433203) B7433203
theorem B7355063 : Blo 507795 7355063 := bstep (se 1 (by rfl) ⟨5516297, by rfl⟩ : syracuseStep 7355063 = 11032595) B11032595
theorem B6275323 : Blo 507795 6275323 := bstep (se 1 (by rfl) ⟨4706492, by rfl⟩ : syracuseStep 6275323 = 9412985) B9412985
theorem B508463 : Blo 507795 508463 := bstep (se 1 (by rfl) ⟨381347, by rfl⟩ : syracuseStep 508463 = 762695) B762695
theorem B1721465 : Blo 507795 1721465 := bstep (se 2 (by rfl) ⟨645549, by rfl⟩ : syracuseStep 1721465 = 1291099) B1291099
theorem B509799 : Blo 507795 509799 := bstep (se 1 (by rfl) ⟨382349, by rfl⟩ : syracuseStep 509799 = 764699) B764699
theorem B510015 : Blo 507795 510015 := bstep (se 1 (by rfl) ⟨382511, by rfl⟩ : syracuseStep 510015 = 765023) B765023
theorem B28264697 : Blo 507795 28264697 := bstep (se 2 (by rfl) ⟨10599261, by rfl⟩ : syracuseStep 28264697 = 21198523) B21198523
theorem B2541961 : Blo 507795 2541961 := bstep (se 2 (by rfl) ⟨953235, by rfl⟩ : syracuseStep 2541961 = 1906471) B1906471
theorem B510367 : Blo 507795 510367 := bstep (se 1 (by rfl) ⟨382775, by rfl⟩ : syracuseStep 510367 = 765551) B765551
theorem B510447 : Blo 507795 510447 := bstep (se 1 (by rfl) ⟨382835, by rfl⟩ : syracuseStep 510447 = 765671) B765671
theorem B1165967 : Blo 507795 1165967 := bstep (se 1 (by rfl) ⟨874475, by rfl⟩ : syracuseStep 1165967 = 1748951) B1748951
theorem B510887 : Blo 507795 510887 := bstep (se 1 (by rfl) ⟨383165, by rfl⟩ : syracuseStep 510887 = 766331) B766331
theorem B1035247 : Blo 507795 1035247 := bstep (se 1 (by rfl) ⟨776435, by rfl⟩ : syracuseStep 1035247 = 1552871) B1552871
theorem B511003 : Blo 507795 511003 := bstep (se 1 (by rfl) ⟨383252, by rfl⟩ : syracuseStep 511003 = 766505) B766505
theorem B511295 : Blo 507795 511295 := bstep (se 1 (by rfl) ⟨383471, by rfl⟩ : syracuseStep 511295 = 766943) B766943
theorem B1724327 : Blo 507795 1724327 := bstep (se 1 (by rfl) ⟨1293245, by rfl⟩ : syracuseStep 1724327 = 2586491) B2586491
theorem B1725353 : Blo 507795 1725353 := bstep (se 2 (by rfl) ⟨647007, by rfl⟩ : syracuseStep 1725353 = 1294015) B1294015
theorem B614143 : Blo 507795 614143 := bstep (se 1 (by rfl) ⟨460607, by rfl⟩ : syracuseStep 614143 = 921215) B921215
theorem B11001977 : Blo 507795 11001977 := bstep (se 2 (by rfl) ⟨4125741, by rfl⟩ : syracuseStep 11001977 = 8251483) B8251483
theorem B4350185 : Blo 507795 4350185 := bstep (se 2 (by rfl) ⟨1631319, by rfl⟩ : syracuseStep 4350185 = 3262639) B3262639
theorem B1272223 : Blo 507795 1272223 := bstep (se 1 (by rfl) ⟨954167, by rfl⟩ : syracuseStep 1272223 = 1908335) B1908335
theorem B7335917 : Blo 507795 7335917 := bstep (se 3 (by rfl) ⟨1375484, by rfl⟩ : syracuseStep 7335917 = 2750969) B2750969
theorem B2617721 : Blo 507795 2617721 := bstep (se 2 (by rfl) ⟨981645, by rfl⟩ : syracuseStep 2617721 = 1963291) B1963291
theorem B4912447 : Blo 507795 4912447 := bstep (se 1 (by rfl) ⟨3684335, by rfl⟩ : syracuseStep 4912447 = 7368671) B7368671
theorem B1144223 : Blo 507795 1144223 := bstep (se 1 (by rfl) ⟨858167, by rfl⟩ : syracuseStep 1144223 = 1716335) B1716335
theorem B1931471 : Blo 507795 1931471 := bstep (se 1 (by rfl) ⟨1448603, by rfl⟩ : syracuseStep 1931471 = 2897207) B2897207
theorem B1145087 : Blo 507795 1145087 := bstep (se 1 (by rfl) ⟨858815, by rfl⟩ : syracuseStep 1145087 = 1717631) B1717631
theorem B1768927 : Blo 507795 1768927 := bstep (se 1 (by rfl) ⟨1326695, by rfl⟩ : syracuseStep 1768927 = 2653391) B2653391
theorem B4653139 : Blo 507795 4653139 := bstep (se 1 (by rfl) ⟨3489854, by rfl⟩ : syracuseStep 4653139 = 6979709) B6979709
theorem B1147643 : Blo 507795 1147643 := bstep (se 1 (by rfl) ⟨860732, by rfl⟩ : syracuseStep 1147643 = 1721465) B1721465
theorem B18843131 : Blo 507795 18843131 := bstep (se 1 (by rfl) ⟨14132348, by rfl⟩ : syracuseStep 18843131 = 28264697) B28264697
theorem B2329145 : Blo 507795 2329145 := bstep (se 2 (by rfl) ⟨873429, by rfl⟩ : syracuseStep 2329145 = 1746859) B1746859
theorem B1149551 : Blo 507795 1149551 := bstep (se 1 (by rfl) ⟨862163, by rfl⟩ : syracuseStep 1149551 = 1724327) B1724327
theorem B1149929 : Blo 507795 1149929 := bstep (se 2 (by rfl) ⟨431223, by rfl⟩ : syracuseStep 1149929 = 862447) B862447
theorem B1150235 : Blo 507795 1150235 := bstep (se 1 (by rfl) ⟨862676, by rfl⟩ : syracuseStep 1150235 = 1725353) B1725353
theorem B1380329 : Blo 507795 1380329 := bstep (se 2 (by rfl) ⟨517623, by rfl⟩ : syracuseStep 1380329 = 1035247) B1035247
theorem B1839199 : Blo 507795 1839199 := bstep (se 1 (by rfl) ⟨1379399, by rfl⟩ : syracuseStep 1839199 = 2758799) B2758799
theorem B4890611 : Blo 507795 4890611 := bstep (se 1 (by rfl) ⟨3667958, by rfl⟩ : syracuseStep 4890611 = 7335917) B7335917
theorem B1745147 : Blo 507795 1745147 := bstep (se 1 (by rfl) ⟨1308860, by rfl⟩ : syracuseStep 1745147 = 2617721) B2617721
theorem B762815 : Blo 507795 762815 := bstep (se 1 (by rfl) ⟨572111, by rfl⟩ : syracuseStep 762815 = 1144223) B1144223
theorem B3089447 : Blo 507795 3089447 := bstep (se 1 (by rfl) ⟨2317085, by rfl⟩ : syracuseStep 3089447 = 4634171) B4634171
theorem B1287647 : Blo 507795 1287647 := bstep (se 1 (by rfl) ⟨965735, by rfl⟩ : syracuseStep 1287647 = 1931471) B1931471
theorem B763391 : Blo 507795 763391 := bstep (se 1 (by rfl) ⟨572543, by rfl⟩ : syracuseStep 763391 = 1145087) B1145087
theorem B1714553 : Blo 507795 1714553 := bstep (se 2 (by rfl) ⟨642957, by rfl⟩ : syracuseStep 1714553 = 1285915) B1285915
theorem B6531839 : Blo 507795 6531839 := bstep (se 1 (by rfl) ⟨4898879, by rfl⟩ : syracuseStep 6531839 = 9797759) B9797759
theorem B8367097 : Blo 507795 8367097 := bstep (se 2 (by rfl) ⟨3137661, by rfl⟩ : syracuseStep 8367097 = 6275323) B6275323
theorem B764927 : Blo 507795 764927 := bstep (se 1 (by rfl) ⟨573695, by rfl⟩ : syracuseStep 764927 = 1147391) B1147391
theorem B3683069 : Blo 507795 3683069 := bstep (se 3 (by rfl) ⟨690575, by rfl⟩ : syracuseStep 3683069 = 1381151) B1381151
theorem B767207 : Blo 507795 767207 := bstep (se 1 (by rfl) ⟨575405, by rfl⟩ : syracuseStep 767207 = 1150811) B1150811
theorem B767423 : Blo 507795 767423 := bstep (se 1 (by rfl) ⟨575567, by rfl⟩ : syracuseStep 767423 = 1151135) B1151135
theorem B767663 : Blo 507795 767663 := bstep (se 1 (by rfl) ⟨575747, by rfl⟩ : syracuseStep 767663 = 1151495) B1151495
theorem B1554319 : Blo 507795 1554319 := bstep (se 1 (by rfl) ⟨1165739, by rfl⟩ : syracuseStep 1554319 = 2331479) B2331479
theorem B4963967 : Blo 507795 4963967 := bstep (se 1 (by rfl) ⟨3722975, by rfl⟩ : syracuseStep 4963967 = 7445951) B7445951
theorem B1228459 : Blo 507795 1228459 := bstep (se 1 (by rfl) ⟨921344, by rfl⟩ : syracuseStep 1228459 = 1842689) B1842689
theorem B2900123 : Blo 507795 2900123 := bstep (se 1 (by rfl) ⟨2175092, by rfl⟩ : syracuseStep 2900123 = 4350185) B4350185
theorem B509183 : Blo 507795 509183 := bstep (se 1 (by rfl) ⟨381887, by rfl⟩ : syracuseStep 509183 = 763775) B763775
theorem B509567 : Blo 507795 509567 := bstep (se 1 (by rfl) ⟨382175, by rfl⟩ : syracuseStep 509567 = 764351) B764351
theorem B26429165 : Blo 507795 26429165 := bstep (se 3 (by rfl) ⟨4955468, by rfl⟩ : syracuseStep 26429165 = 9910937) B9910937
theorem B509863 : Blo 507795 509863 := bstep (se 1 (by rfl) ⟨382397, by rfl⟩ : syracuseStep 509863 = 764795) B764795
theorem B510463 : Blo 507795 510463 := bstep (se 1 (by rfl) ⟨382847, by rfl⟩ : syracuseStep 510463 = 765695) B765695
theorem B4903375 : Blo 507795 4903375 := bstep (se 1 (by rfl) ⟨3677531, by rfl⟩ : syracuseStep 4903375 = 7355063) B7355063
theorem B777311 : Blo 507795 777311 := bstep (se 1 (by rfl) ⟨582983, by rfl⟩ : syracuseStep 777311 = 1165967) B1165967
theorem B13557125 : Blo 507795 13557125 := bstep (se 4 (by rfl) ⟨1270980, by rfl⟩ : syracuseStep 13557125 = 2541961) B2541961
theorem B3104183 : Blo 507795 3104183 := bstep (se 1 (by rfl) ⟨2328137, by rfl⟩ : syracuseStep 3104183 = 4656275) B4656275
theorem B1696297 : Blo 507795 1696297 := bstep (se 2 (by rfl) ⟨636111, by rfl⟩ : syracuseStep 1696297 = 1272223) B1272223
theorem B451176803 : Blo 507795 451176803 := bstep (se 1 (by rfl) ⟨338382602, by rfl⟩ : syracuseStep 451176803 = 676765205) B676765205
theorem B7334651 : Blo 507795 7334651 := bstep (se 1 (by rfl) ⟨5500988, by rfl⟩ : syracuseStep 7334651 = 11001977) B11001977
theorem B1928555 : Blo 507795 1928555 := bstep (se 1 (by rfl) ⟨1446416, by rfl⟩ : syracuseStep 1928555 = 2892833) B2892833
theorem B59600279 : Blo 507795 59600279 := bstep (se 1 (by rfl) ⟨44700209, by rfl⟩ : syracuseStep 59600279 = 89400419) B89400419
theorem B6549929 : Blo 507795 6549929 := bstep (se 2 (by rfl) ⟨2456223, by rfl⟩ : syracuseStep 6549929 = 4912447) B4912447
theorem B2586167 : Blo 507795 2586167 := bstep (se 1 (by rfl) ⟨1939625, by rfl⟩ : syracuseStep 2586167 = 3879251) B3879251
theorem B2358569 : Blo 507795 2358569 := bstep (se 2 (by rfl) ⟨884463, by rfl⟩ : syracuseStep 2358569 = 1768927) B1768927
theorem B818857 : Blo 507795 818857 := bstep (se 2 (by rfl) ⟨307071, by rfl⟩ : syracuseStep 818857 = 614143) B614143
theorem B1933415 : Blo 507795 1933415 := bstep (se 1 (by rfl) ⟨1450061, by rfl⟩ : syracuseStep 1933415 = 2900123) B2900123
theorem B2261729 : Blo 507795 2261729 := bstep (se 2 (by rfl) ⟨848148, by rfl⟩ : syracuseStep 2261729 = 1696297) B1696297
theorem B920219 : Blo 507795 920219 := bstep (se 1 (by rfl) ⟨690164, by rfl⟩ : syracuseStep 920219 = 1380329) B1380329
theorem B2069455 : Blo 507795 2069455 := bstep (se 1 (by rfl) ⟨1552091, by rfl⟩ : syracuseStep 2069455 = 3104183) B3104183
theorem B858431 : Blo 507795 858431 := bstep (se 1 (by rfl) ⟨643823, by rfl⟩ : syracuseStep 858431 = 1287647) B1287647
theorem B300784535 : Blo 507795 300784535 := bstep (se 1 (by rfl) ⟨225588401, by rfl⟩ : syracuseStep 300784535 = 451176803) B451176803
theorem B4889767 : Blo 507795 4889767 := bstep (se 1 (by rfl) ⟨3667325, by rfl⟩ : syracuseStep 4889767 = 7334651) B7334651
theorem B1285703 : Blo 507795 1285703 := bstep (se 1 (by rfl) ⟨964277, by rfl⟩ : syracuseStep 1285703 = 1928555) B1928555
theorem B4366619 : Blo 507795 4366619 := bstep (se 1 (by rfl) ⟨3274964, by rfl⟩ : syracuseStep 4366619 = 6549929) B6549929
theorem B1091809 : Blo 507795 1091809 := bstep (se 2 (by rfl) ⟨409428, by rfl⟩ : syracuseStep 1091809 = 818857) B818857
theorem B6204185 : Blo 507795 6204185 := bstep (se 2 (by rfl) ⟨2326569, by rfl⟩ : syracuseStep 6204185 = 4653139) B4653139
theorem B765095 : Blo 507795 765095 := bstep (se 1 (by rfl) ⟨573821, by rfl⟩ : syracuseStep 765095 = 1147643) B1147643
theorem B12562087 : Blo 507795 12562087 := bstep (se 1 (by rfl) ⟨9421565, by rfl⟩ : syracuseStep 12562087 = 18843131) B18843131
theorem B1552763 : Blo 507795 1552763 := bstep (se 1 (by rfl) ⟨1164572, by rfl⟩ : syracuseStep 1552763 = 2329145) B2329145
theorem B766367 : Blo 507795 766367 := bstep (se 1 (by rfl) ⟨574775, by rfl⟩ : syracuseStep 766367 = 1149551) B1149551
theorem B766619 : Blo 507795 766619 := bstep (se 1 (by rfl) ⟨574964, by rfl⟩ : syracuseStep 766619 = 1149929) B1149929
theorem B766823 : Blo 507795 766823 := bstep (se 1 (by rfl) ⟨575117, by rfl⟩ : syracuseStep 766823 = 1150235) B1150235
theorem B11156129 : Blo 507795 11156129 := bstep (se 2 (by rfl) ⟨4183548, by rfl⟩ : syracuseStep 11156129 = 8367097) B8367097
theorem B3260407 : Blo 507795 3260407 := bstep (se 1 (by rfl) ⟨2445305, by rfl⟩ : syracuseStep 3260407 = 4890611) B4890611
theorem B1163431 : Blo 507795 1163431 := bstep (se 1 (by rfl) ⟨872573, by rfl⟩ : syracuseStep 1163431 = 1745147) B1745147
theorem B6537833 : Blo 507795 6537833 := bstep (se 2 (by rfl) ⟨2451687, by rfl⟩ : syracuseStep 6537833 = 4903375) B4903375
theorem B508543 : Blo 507795 508543 := bstep (se 1 (by rfl) ⟨381407, by rfl⟩ : syracuseStep 508543 = 762815) B762815
theorem B508927 : Blo 507795 508927 := bstep (se 1 (by rfl) ⟨381695, by rfl⟩ : syracuseStep 508927 = 763391) B763391
theorem B509951 : Blo 507795 509951 := bstep (se 1 (by rfl) ⟨382463, by rfl⟩ : syracuseStep 509951 = 764927) B764927
theorem B39733519 : Blo 507795 39733519 := bstep (se 1 (by rfl) ⟨29800139, by rfl⟩ : syracuseStep 39733519 = 59600279) B59600279
theorem B511471 : Blo 507795 511471 := bstep (se 1 (by rfl) ⟨383603, by rfl⟩ : syracuseStep 511471 = 767207) B767207
theorem B511615 : Blo 507795 511615 := bstep (se 1 (by rfl) ⟨383711, by rfl⟩ : syracuseStep 511615 = 767423) B767423
theorem B1724111 : Blo 507795 1724111 := bstep (se 1 (by rfl) ⟨1293083, by rfl⟩ : syracuseStep 1724111 = 2586167) B2586167
theorem B511775 : Blo 507795 511775 := bstep (se 1 (by rfl) ⟨383831, by rfl⟩ : syracuseStep 511775 = 767663) B767663
theorem B17619443 : Blo 507795 17619443 := bstep (se 1 (by rfl) ⟨13214582, by rfl⟩ : syracuseStep 17619443 = 26429165) B26429165
theorem B518207 : Blo 507795 518207 := bstep (se 1 (by rfl) ⟨388655, by rfl⟩ : syracuseStep 518207 = 777311) B777311
theorem B9038083 : Blo 507795 9038083 := bstep (se 1 (by rfl) ⟨6778562, by rfl⟩ : syracuseStep 9038083 = 13557125) B13557125
theorem B2452265 : Blo 507795 2452265 := bstep (se 2 (by rfl) ⟨919599, by rfl⟩ : syracuseStep 2452265 = 1839199) B1839199
theorem B2059631 : Blo 507795 2059631 := bstep (se 1 (by rfl) ⟨1544723, by rfl⟩ : syracuseStep 2059631 = 3089447) B3089447
theorem B1143035 : Blo 507795 1143035 := bstep (se 1 (by rfl) ⟨857276, by rfl⟩ : syracuseStep 1143035 = 1714553) B1714553
theorem B4354559 : Blo 507795 4354559 := bstep (se 1 (by rfl) ⟨3265919, by rfl⟩ : syracuseStep 4354559 = 6531839) B6531839
theorem B2455379 : Blo 507795 2455379 := bstep (se 1 (by rfl) ⟨1841534, by rfl⟩ : syracuseStep 2455379 = 3683069) B3683069
theorem B6289517 : Blo 507795 6289517 := bstep (se 3 (by rfl) ⟨1179284, by rfl⟩ : syracuseStep 6289517 = 2358569) B2358569
theorem B8289701 : Blo 507795 8289701 := bstep (se 4 (by rfl) ⟨777159, by rfl⟩ : syracuseStep 8289701 = 1554319) B1554319
theorem B1637945 : Blo 507795 1637945 := bstep (se 2 (by rfl) ⟨614229, by rfl⟩ : syracuseStep 1637945 = 1228459) B1228459
theorem B3309311 : Blo 507795 3309311 := bstep (se 1 (by rfl) ⟨2481983, by rfl⟩ : syracuseStep 3309311 = 4963967) B4963967
theorem B4358555 : Blo 507795 4358555 := bstep (se 1 (by rfl) ⟨3268916, by rfl⟩ : syracuseStep 4358555 = 6537833) B6537833
theorem B6031277 : Blo 507795 6031277 := bstep (se 3 (by rfl) ⟨1130864, by rfl⟩ : syracuseStep 6031277 = 2261729) B2261729
theorem B1149407 : Blo 507795 1149407 := bstep (se 1 (by rfl) ⟨862055, by rfl⟩ : syracuseStep 1149407 = 1724111) B1724111
theorem B16749449 : Blo 507795 16749449 := bstep (se 2 (by rfl) ⟨6281043, by rfl⟩ : syracuseStep 16749449 = 12562087) B12562087
theorem B857135 : Blo 507795 857135 := bstep (se 1 (by rfl) ⟨642851, by rfl⟩ : syracuseStep 857135 = 1285703) B1285703
theorem B2759273 : Blo 507795 2759273 := bstep (se 2 (by rfl) ⟨1034727, by rfl⟩ : syracuseStep 2759273 = 2069455) B2069455
theorem B4136123 : Blo 507795 4136123 := bstep (se 1 (by rfl) ⟨3102092, by rfl⟩ : syracuseStep 4136123 = 6204185) B6204185
theorem B762023 : Blo 507795 762023 := bstep (se 1 (by rfl) ⟨571517, by rfl⟩ : syracuseStep 762023 = 1143035) B1143035
theorem B1091963 : Blo 507795 1091963 := bstep (se 1 (by rfl) ⟨818972, by rfl⟩ : syracuseStep 1091963 = 1637945) B1637945
theorem B2206207 : Blo 507795 2206207 := bstep (se 1 (by rfl) ⟨1654655, by rfl⟩ : syracuseStep 2206207 = 3309311) B3309311
theorem B1288943 : Blo 507795 1288943 := bstep (se 1 (by rfl) ⟨966707, by rfl⟩ : syracuseStep 1288943 = 1933415) B1933415
theorem B1551241 : Blo 507795 1551241 := bstep (se 2 (by rfl) ⟨581715, by rfl⟩ : syracuseStep 1551241 = 1163431) B1163431
theorem B1455745 : Blo 507795 1455745 := bstep (se 2 (by rfl) ⟨545904, by rfl⟩ : syracuseStep 1455745 = 1091809) B1091809
theorem B572287 : Blo 507795 572287 := bstep (se 1 (by rfl) ⟨429215, by rfl⟩ : syracuseStep 572287 = 858431) B858431
theorem B11746295 : Blo 507795 11746295 := bstep (se 1 (by rfl) ⟨8809721, by rfl⟩ : syracuseStep 11746295 = 17619443) B17619443
theorem B200523023 : Blo 507795 200523023 := bstep (se 1 (by rfl) ⟨150392267, by rfl⟩ : syracuseStep 200523023 = 300784535) B300784535
theorem B510063 : Blo 507795 510063 := bstep (se 1 (by rfl) ⟨382547, by rfl⟩ : syracuseStep 510063 = 765095) B765095
theorem B1035175 : Blo 507795 1035175 := bstep (se 1 (by rfl) ⟨776381, by rfl⟩ : syracuseStep 1035175 = 1552763) B1552763
theorem B510911 : Blo 507795 510911 := bstep (se 1 (by rfl) ⟨383183, by rfl⟩ : syracuseStep 510911 = 766367) B766367
theorem B2903039 : Blo 507795 2903039 := bstep (se 1 (by rfl) ⟨2177279, by rfl⟩ : syracuseStep 2903039 = 4354559) B4354559
theorem B511079 : Blo 507795 511079 := bstep (se 1 (by rfl) ⟨383309, by rfl⟩ : syracuseStep 511079 = 766619) B766619
theorem B511215 : Blo 507795 511215 := bstep (se 1 (by rfl) ⟨383411, by rfl⟩ : syracuseStep 511215 = 766823) B766823
theorem B5526467 : Blo 507795 5526467 := bstep (se 1 (by rfl) ⟨4144850, by rfl⟩ : syracuseStep 5526467 = 8289701) B8289701
theorem B4347209 : Blo 507795 4347209 := bstep (se 2 (by rfl) ⟨1630203, by rfl⟩ : syracuseStep 4347209 = 3260407) B3260407
theorem B5527541 : Blo 507795 5527541 := bstep (se 5 (by rfl) ⟨259103, by rfl⟩ : syracuseStep 5527541 = 518207) B518207
theorem B12050777 : Blo 507795 12050777 := bstep (se 2 (by rfl) ⟨4519041, by rfl⟩ : syracuseStep 12050777 = 9038083) B9038083
theorem B52978025 : Blo 507795 52978025 := bstep (se 2 (by rfl) ⟨19866759, by rfl⟩ : syracuseStep 52978025 = 39733519) B39733519
theorem B2911079 : Blo 507795 2911079 := bstep (se 1 (by rfl) ⟨2183309, by rfl⟩ : syracuseStep 2911079 = 4366619) B4366619
theorem B2453917 : Blo 507795 2453917 := bstep (se 3 (by rfl) ⟨460109, by rfl⟩ : syracuseStep 2453917 = 920219) B920219
theorem B1634843 : Blo 507795 1634843 := bstep (se 1 (by rfl) ⟨1226132, by rfl⟩ : syracuseStep 1634843 = 2452265) B2452265
theorem B1373087 : Blo 507795 1373087 := bstep (se 1 (by rfl) ⟨1029815, by rfl⟩ : syracuseStep 1373087 = 2059631) B2059631
theorem B1636919 : Blo 507795 1636919 := bstep (se 1 (by rfl) ⟨1227689, by rfl⟩ : syracuseStep 1636919 = 2455379) B2455379
theorem B4193011 : Blo 507795 4193011 := bstep (se 1 (by rfl) ⟨3144758, by rfl⟩ : syracuseStep 4193011 = 6289517) B6289517
theorem B6519689 : Blo 507795 6519689 := bstep (se 2 (by rfl) ⟨2444883, by rfl⟩ : syracuseStep 6519689 = 4889767) B4889767
theorem B7437419 : Blo 507795 7437419 := bstep (se 1 (by rfl) ⟨5578064, by rfl⟩ : syracuseStep 7437419 = 11156129) B11156129
theorem B4359581 : Blo 507795 4359581 := bstep (se 3 (by rfl) ⟨817421, by rfl⟩ : syracuseStep 4359581 = 1634843) B1634843
theorem B1935359 : Blo 507795 1935359 := bstep (se 1 (by rfl) ⟨1451519, by rfl⟩ : syracuseStep 1935359 = 2903039) B2903039
theorem B11766437 : Blo 507795 11766437 := bstep (se 4 (by rfl) ⟨1103103, by rfl⟩ : syracuseStep 11766437 = 2206207) B2206207
theorem B1380233 : Blo 507795 1380233 := bstep (se 2 (by rfl) ⟨517587, by rfl⟩ : syracuseStep 1380233 = 1035175) B1035175
theorem B1839515 : Blo 507795 1839515 := bstep (se 1 (by rfl) ⟨1379636, by rfl⟩ : syracuseStep 1839515 = 2759273) B2759273
theorem B2757415 : Blo 507795 2757415 := bstep (se 1 (by rfl) ⟨2068061, by rfl⟩ : syracuseStep 2757415 = 4136123) B4136123
theorem B8033851 : Blo 507795 8033851 := bstep (se 1 (by rfl) ⟨6025388, by rfl⟩ : syracuseStep 8033851 = 12050777) B12050777
theorem B727975 : Blo 507795 727975 := bstep (se 1 (by rfl) ⟨545981, by rfl⟩ : syracuseStep 727975 = 1091963) B1091963
theorem B859295 : Blo 507795 859295 := bstep (se 1 (by rfl) ⟨644471, by rfl⟩ : syracuseStep 859295 = 1288943) B1288943
theorem B1940719 : Blo 507795 1940719 := bstep (se 1 (by rfl) ⟨1455539, by rfl⟩ : syracuseStep 1940719 = 2911079) B2911079
theorem B1940993 : Blo 507795 1940993 := bstep (se 2 (by rfl) ⟨727872, by rfl⟩ : syracuseStep 1940993 = 1455745) B1455745
theorem B763049 : Blo 507795 763049 := bstep (se 2 (by rfl) ⟨286143, by rfl⟩ : syracuseStep 763049 = 572287) B572287
theorem B1091279 : Blo 507795 1091279 := bstep (se 1 (by rfl) ⟨818459, by rfl⟩ : syracuseStep 1091279 = 1636919) B1636919
theorem B4958279 : Blo 507795 4958279 := bstep (se 1 (by rfl) ⟨3718709, by rfl⟩ : syracuseStep 4958279 = 7437419) B7437419
theorem B766271 : Blo 507795 766271 := bstep (se 1 (by rfl) ⟨574703, by rfl⟩ : syracuseStep 766271 = 1149407) B1149407
theorem B3684311 : Blo 507795 3684311 := bstep (se 1 (by rfl) ⟨2763233, by rfl⟩ : syracuseStep 3684311 = 5526467) B5526467
theorem B571423 : Blo 507795 571423 := bstep (se 1 (by rfl) ⟨428567, by rfl⟩ : syracuseStep 571423 = 857135) B857135
theorem B2898139 : Blo 507795 2898139 := bstep (se 1 (by rfl) ⟨2173604, by rfl⟩ : syracuseStep 2898139 = 4347209) B4347209
theorem B22362725 : Blo 507795 22362725 := bstep (se 4 (by rfl) ⟨2096505, by rfl⟩ : syracuseStep 22362725 = 4193011) B4193011
theorem B3685027 : Blo 507795 3685027 := bstep (se 1 (by rfl) ⟨2763770, by rfl⟩ : syracuseStep 3685027 = 5527541) B5527541
theorem B8273285 : Blo 507795 8273285 := bstep (se 4 (by rfl) ⟨775620, by rfl⟩ : syracuseStep 8273285 = 1551241) B1551241
theorem B508015 : Blo 507795 508015 := bstep (se 1 (by rfl) ⟨381011, by rfl⟩ : syracuseStep 508015 = 762023) B762023
theorem B4346459 : Blo 507795 4346459 := bstep (se 1 (by rfl) ⟨3259844, by rfl⟩ : syracuseStep 4346459 = 6519689) B6519689
theorem B133682015 : Blo 507795 133682015 := bstep (se 1 (by rfl) ⟨100261511, by rfl⟩ : syracuseStep 133682015 = 200523023) B200523023
theorem B2905703 : Blo 507795 2905703 := bstep (se 1 (by rfl) ⟨2179277, by rfl⟩ : syracuseStep 2905703 = 4358555) B4358555
theorem B4020851 : Blo 507795 4020851 := bstep (se 1 (by rfl) ⟨3015638, by rfl⟩ : syracuseStep 4020851 = 6031277) B6031277
theorem B11166299 : Blo 507795 11166299 := bstep (se 1 (by rfl) ⟨8374724, by rfl⟩ : syracuseStep 11166299 = 16749449) B16749449
theorem B35318683 : Blo 507795 35318683 := bstep (se 1 (by rfl) ⟨26489012, by rfl⟩ : syracuseStep 35318683 = 52978025) B52978025
theorem B3271889 : Blo 507795 3271889 := bstep (se 2 (by rfl) ⟨1226958, by rfl⟩ : syracuseStep 3271889 = 2453917) B2453917
theorem B915391 : Blo 507795 915391 := bstep (se 1 (by rfl) ⟨686543, by rfl⟩ : syracuseStep 915391 = 1373087) B1373087
theorem B7830863 : Blo 507795 7830863 := bstep (se 1 (by rfl) ⟨5873147, by rfl⟩ : syracuseStep 7830863 = 11746295) B11746295
theorem B920155 : Blo 507795 920155 := bstep (se 1 (by rfl) ⟨690116, by rfl⟩ : syracuseStep 920155 = 1380233) B1380233
theorem B1937135 : Blo 507795 1937135 := bstep (se 1 (by rfl) ⟨1452851, by rfl⟩ : syracuseStep 1937135 = 2905703) B2905703
theorem B47091577 : Blo 507795 47091577 := bstep (se 2 (by rfl) ⟨17659341, by rfl⟩ : syracuseStep 47091577 = 35318683) B35318683
theorem B7444199 : Blo 507795 7444199 := bstep (se 1 (by rfl) ⟨5583149, by rfl⟩ : syracuseStep 7444199 = 11166299) B11166299
theorem B3676553 : Blo 507795 3676553 := bstep (se 2 (by rfl) ⟨1378707, by rfl⟩ : syracuseStep 3676553 = 2757415) B2757415
theorem B10722269 : Blo 507795 10722269 := bstep (se 3 (by rfl) ⟨2010425, by rfl⟩ : syracuseStep 10722269 = 4020851) B4020851
theorem B1220521 : Blo 507795 1220521 := bstep (se 2 (by rfl) ⟨457695, by rfl⟩ : syracuseStep 1220521 = 915391) B915391
theorem B761897 : Blo 507795 761897 := bstep (se 2 (by rfl) ⟨285711, by rfl⟩ : syracuseStep 761897 = 571423) B571423
theorem B5220575 : Blo 507795 5220575 := bstep (se 1 (by rfl) ⟨3915431, by rfl⟩ : syracuseStep 5220575 = 7830863) B7830863
theorem B5515523 : Blo 507795 5515523 := bstep (se 1 (by rfl) ⟨4136642, by rfl⟩ : syracuseStep 5515523 = 8273285) B8273285
theorem B1290239 : Blo 507795 1290239 := bstep (se 1 (by rfl) ⟨967679, by rfl⟩ : syracuseStep 1290239 = 1935359) B1935359
theorem B7844291 : Blo 507795 7844291 := bstep (se 1 (by rfl) ⟨5883218, by rfl⟩ : syracuseStep 7844291 = 11766437) B11766437
theorem B2897639 : Blo 507795 2897639 := bstep (se 1 (by rfl) ⟨2173229, by rfl⟩ : syracuseStep 2897639 = 4346459) B4346459
theorem B572863 : Blo 507795 572863 := bstep (se 1 (by rfl) ⟨429647, by rfl⟩ : syracuseStep 572863 = 859295) B859295
theorem B1293995 : Blo 507795 1293995 := bstep (se 1 (by rfl) ⟨970496, by rfl⟩ : syracuseStep 1293995 = 1940993) B1940993
theorem B508699 : Blo 507795 508699 := bstep (se 1 (by rfl) ⟨381524, by rfl⟩ : syracuseStep 508699 = 763049) B763049
theorem B2181259 : Blo 507795 2181259 := bstep (se 1 (by rfl) ⟨1635944, by rfl⟩ : syracuseStep 2181259 = 3271889) B3271889
theorem B510847 : Blo 507795 510847 := bstep (se 1 (by rfl) ⟨383135, by rfl⟩ : syracuseStep 510847 = 766271) B766271
theorem B970633 : Blo 507795 970633 := bstep (se 2 (by rfl) ⟨363987, by rfl⟩ : syracuseStep 970633 = 727975) B727975
theorem B2906387 : Blo 507795 2906387 := bstep (se 1 (by rfl) ⟨2179790, by rfl⟩ : syracuseStep 2906387 = 4359581) B4359581
theorem B4905373 : Blo 507795 4905373 := bstep (se 3 (by rfl) ⟨919757, by rfl⟩ : syracuseStep 4905373 = 1839515) B1839515
theorem B89121343 : Blo 507795 89121343 := bstep (se 1 (by rfl) ⟨66841007, by rfl⟩ : syracuseStep 89121343 = 133682015) B133682015
theorem B2910077 : Blo 507795 2910077 := bstep (se 3 (by rfl) ⟨545639, by rfl⟩ : syracuseStep 2910077 = 1091279) B1091279
theorem B3305519 : Blo 507795 3305519 := bstep (se 1 (by rfl) ⟨2479139, by rfl⟩ : syracuseStep 3305519 = 4958279) B4958279
theorem B10711801 : Blo 507795 10711801 := bstep (se 2 (by rfl) ⟨4016925, by rfl⟩ : syracuseStep 10711801 = 8033851) B8033851
theorem B3864185 : Blo 507795 3864185 := bstep (se 2 (by rfl) ⟨1449069, by rfl⟩ : syracuseStep 3864185 = 2898139) B2898139
theorem B4913369 : Blo 507795 4913369 := bstep (se 2 (by rfl) ⟨1842513, by rfl⟩ : syracuseStep 4913369 = 3685027) B3685027
theorem B2456207 : Blo 507795 2456207 := bstep (se 1 (by rfl) ⟨1842155, by rfl⟩ : syracuseStep 2456207 = 3684311) B3684311
theorem B2587625 : Blo 507795 2587625 := bstep (se 2 (by rfl) ⟨970359, by rfl⟩ : syracuseStep 2587625 = 1940719) B1940719
theorem B14908483 : Blo 507795 14908483 := bstep (se 1 (by rfl) ⟨11181362, by rfl⟩ : syracuseStep 14908483 = 22362725) B22362725
theorem B1937591 : Blo 507795 1937591 := bstep (se 1 (by rfl) ⟨1453193, by rfl⟩ : syracuseStep 1937591 = 2906387) B2906387
theorem B7148179 : Blo 507795 7148179 := bstep (se 1 (by rfl) ⟨5361134, by rfl⟩ : syracuseStep 7148179 = 10722269) B10722269
theorem B62788769 : Blo 507795 62788769 := bstep (se 2 (by rfl) ⟨23545788, by rfl⟩ : syracuseStep 62788769 = 47091577) B47091577
theorem B1940051 : Blo 507795 1940051 := bstep (se 1 (by rfl) ⟨1455038, by rfl⟩ : syracuseStep 1940051 = 2910077) B2910077
theorem B3480383 : Blo 507795 3480383 := bstep (se 1 (by rfl) ⟨2610287, by rfl⟩ : syracuseStep 3480383 = 5220575) B5220575
theorem B3677015 : Blo 507795 3677015 := bstep (se 1 (by rfl) ⟨2757761, by rfl⟩ : syracuseStep 3677015 = 5515523) B5515523
theorem B860159 : Blo 507795 860159 := bstep (se 1 (by rfl) ⟨645119, by rfl⟩ : syracuseStep 860159 = 1290239) B1290239
theorem B2203679 : Blo 507795 2203679 := bstep (se 1 (by rfl) ⟨1652759, by rfl⟩ : syracuseStep 2203679 = 3305519) B3305519
theorem B763817 : Blo 507795 763817 := bstep (se 2 (by rfl) ⟨286431, by rfl⟩ : syracuseStep 763817 = 572863) B572863
theorem B862663 : Blo 507795 862663 := bstep (se 1 (by rfl) ⟨646997, by rfl⟩ : syracuseStep 862663 = 1293995) B1293995
theorem B118828457 : Blo 507795 118828457 := bstep (se 2 (by rfl) ⟨44560671, by rfl⟩ : syracuseStep 118828457 = 89121343) B89121343
theorem B1291423 : Blo 507795 1291423 := bstep (se 1 (by rfl) ⟨968567, by rfl⟩ : syracuseStep 1291423 = 1937135) B1937135
theorem B1226873 : Blo 507795 1226873 := bstep (se 2 (by rfl) ⟨460077, by rfl⟩ : syracuseStep 1226873 = 920155) B920155
theorem B4962799 : Blo 507795 4962799 := bstep (se 1 (by rfl) ⟨3722099, by rfl⟩ : syracuseStep 4962799 = 7444199) B7444199
theorem B1294177 : Blo 507795 1294177 := bstep (se 2 (by rfl) ⟨485316, by rfl⟩ : syracuseStep 1294177 = 970633) B970633
theorem B507931 : Blo 507795 507931 := bstep (se 1 (by rfl) ⟨380948, by rfl⟩ : syracuseStep 507931 = 761897) B761897
theorem B5229527 : Blo 507795 5229527 := bstep (se 1 (by rfl) ⟨3922145, by rfl⟩ : syracuseStep 5229527 = 7844291) B7844291
theorem B6540497 : Blo 507795 6540497 := bstep (se 2 (by rfl) ⟨2452686, by rfl⟩ : syracuseStep 6540497 = 4905373) B4905373
theorem B2576123 : Blo 507795 2576123 := bstep (se 1 (by rfl) ⟨1932092, by rfl⟩ : syracuseStep 2576123 = 3864185) B3864185
theorem B19877977 : Blo 507795 19877977 := bstep (se 2 (by rfl) ⟨7454241, by rfl⟩ : syracuseStep 19877977 = 14908483) B14908483
theorem B1725083 : Blo 507795 1725083 := bstep (se 1 (by rfl) ⟨1293812, by rfl⟩ : syracuseStep 1725083 = 2587625) B2587625
theorem B1627361 : Blo 507795 1627361 := bstep (se 2 (by rfl) ⟨610260, by rfl⟩ : syracuseStep 1627361 = 1220521) B1220521
theorem B2908345 : Blo 507795 2908345 := bstep (se 2 (by rfl) ⟨1090629, by rfl⟩ : syracuseStep 2908345 = 2181259) B2181259
theorem B2451035 : Blo 507795 2451035 := bstep (se 1 (by rfl) ⟨1838276, by rfl⟩ : syracuseStep 2451035 = 3676553) B3676553
theorem B14282401 : Blo 507795 14282401 := bstep (se 2 (by rfl) ⟨5355900, by rfl⟩ : syracuseStep 14282401 = 10711801) B10711801
theorem B1931759 : Blo 507795 1931759 := bstep (se 1 (by rfl) ⟨1448819, by rfl⟩ : syracuseStep 1931759 = 2897639) B2897639
theorem B3275579 : Blo 507795 3275579 := bstep (se 1 (by rfl) ⟨2456684, by rfl⟩ : syracuseStep 3275579 = 4913369) B4913369
theorem B1637471 : Blo 507795 1637471 := bstep (se 1 (by rfl) ⟨1228103, by rfl⟩ : syracuseStep 1637471 = 2456207) B2456207
theorem B4360331 : Blo 507795 4360331 := bstep (se 1 (by rfl) ⟨3270248, by rfl⟩ : syracuseStep 4360331 = 6540497) B6540497
theorem B1150055 : Blo 507795 1150055 := bstep (se 1 (by rfl) ⟨862541, by rfl⟩ : syracuseStep 1150055 = 1725083) B1725083
theorem B1150217 : Blo 507795 1150217 := bstep (se 2 (by rfl) ⟨431331, by rfl⟩ : syracuseStep 1150217 = 862663) B862663
theorem B1084907 : Blo 507795 1084907 := bstep (se 1 (by rfl) ⟨813680, by rfl⟩ : syracuseStep 1084907 = 1627361) B1627361
theorem B19043201 : Blo 507795 19043201 := bstep (se 2 (by rfl) ⟨7141200, by rfl⟩ : syracuseStep 19043201 = 14282401) B14282401
theorem B1287839 : Blo 507795 1287839 := bstep (se 1 (by rfl) ⟨965879, by rfl⟩ : syracuseStep 1287839 = 1931759) B1931759
theorem B1091647 : Blo 507795 1091647 := bstep (se 1 (by rfl) ⟨818735, by rfl⟩ : syracuseStep 1091647 = 1637471) B1637471
theorem B3877793 : Blo 507795 3877793 := bstep (se 2 (by rfl) ⟨1454172, by rfl⟩ : syracuseStep 3877793 = 2908345) B2908345
theorem B1717415 : Blo 507795 1717415 := bstep (se 1 (by rfl) ⟨1288061, by rfl⟩ : syracuseStep 1717415 = 2576123) B2576123
theorem B1291727 : Blo 507795 1291727 := bstep (se 1 (by rfl) ⟨968795, by rfl⟩ : syracuseStep 1291727 = 1937591) B1937591
theorem B41859179 : Blo 507795 41859179 := bstep (se 1 (by rfl) ⟨31394384, by rfl⟩ : syracuseStep 41859179 = 62788769) B62788769
theorem B1293367 : Blo 507795 1293367 := bstep (se 1 (by rfl) ⟨970025, by rfl⟩ : syracuseStep 1293367 = 1940051) B1940051
theorem B573439 : Blo 507795 573439 := bstep (se 1 (by rfl) ⟨430079, by rfl⟩ : syracuseStep 573439 = 860159) B860159
theorem B509211 : Blo 507795 509211 := bstep (se 1 (by rfl) ⟨381908, by rfl⟩ : syracuseStep 509211 = 763817) B763817
theorem B1721897 : Blo 507795 1721897 := bstep (se 2 (by rfl) ⟨645711, by rfl⟩ : syracuseStep 1721897 = 1291423) B1291423
theorem B8734877 : Blo 507795 8734877 := bstep (se 3 (by rfl) ⟨1637789, by rfl⟩ : syracuseStep 8734877 = 3275579) B3275579
theorem B79218971 : Blo 507795 79218971 := bstep (se 1 (by rfl) ⟨59414228, by rfl⟩ : syracuseStep 79218971 = 118828457) B118828457
theorem B13945405 : Blo 507795 13945405 := bstep (se 3 (by rfl) ⟨2614763, by rfl⟩ : syracuseStep 13945405 = 5229527) B5229527
theorem B1725569 : Blo 507795 1725569 := bstep (se 2 (by rfl) ⟨647088, by rfl⟩ : syracuseStep 1725569 = 1294177) B1294177
theorem B2320255 : Blo 507795 2320255 := bstep (se 1 (by rfl) ⟨1740191, by rfl⟩ : syracuseStep 2320255 = 3480383) B3480383
theorem B2451343 : Blo 507795 2451343 := bstep (se 1 (by rfl) ⟨1838507, by rfl⟩ : syracuseStep 2451343 = 3677015) B3677015
theorem B1469119 : Blo 507795 1469119 := bstep (se 1 (by rfl) ⟨1101839, by rfl⟩ : syracuseStep 1469119 = 2203679) B2203679
theorem B26503969 : Blo 507795 26503969 := bstep (se 2 (by rfl) ⟨9938988, by rfl⟩ : syracuseStep 26503969 = 19877977) B19877977
theorem B3271661 : Blo 507795 3271661 := bstep (se 3 (by rfl) ⟨613436, by rfl⟩ : syracuseStep 3271661 = 1226873) B1226873
theorem B9530905 : Blo 507795 9530905 := bstep (se 2 (by rfl) ⟨3574089, by rfl⟩ : syracuseStep 9530905 = 7148179) B7148179
theorem B1634023 : Blo 507795 1634023 := bstep (se 1 (by rfl) ⟨1225517, by rfl⟩ : syracuseStep 1634023 = 2451035) B2451035
theorem B6617065 : Blo 507795 6617065 := bstep (se 2 (by rfl) ⟨2481399, by rfl⟩ : syracuseStep 6617065 = 4962799) B4962799
theorem B1147931 : Blo 507795 1147931 := bstep (se 1 (by rfl) ⟨860948, by rfl⟩ : syracuseStep 1147931 = 1721897) B1721897
theorem B723271 : Blo 507795 723271 := bstep (se 1 (by rfl) ⟨542453, by rfl⟩ : syracuseStep 723271 = 1084907) B1084907
theorem B1150379 : Blo 507795 1150379 := bstep (se 1 (by rfl) ⟨862784, by rfl⟩ : syracuseStep 1150379 = 1725569) B1725569
theorem B858559 : Blo 507795 858559 := bstep (se 1 (by rfl) ⟨643919, by rfl⟩ : syracuseStep 858559 = 1287839) B1287839
theorem B8822753 : Blo 507795 8822753 := bstep (se 2 (by rfl) ⟨3308532, by rfl⟩ : syracuseStep 8822753 = 6617065) B6617065
theorem B861151 : Blo 507795 861151 := bstep (se 1 (by rfl) ⟨645863, by rfl⟩ : syracuseStep 861151 = 1291727) B1291727
theorem B764585 : Blo 507795 764585 := bstep (se 2 (by rfl) ⟨286719, by rfl⟩ : syracuseStep 764585 = 573439) B573439
theorem B766703 : Blo 507795 766703 := bstep (se 1 (by rfl) ⟨575027, by rfl⟩ : syracuseStep 766703 = 1150055) B1150055
theorem B766811 : Blo 507795 766811 := bstep (se 1 (by rfl) ⟨575108, by rfl⟩ : syracuseStep 766811 = 1150217) B1150217
theorem B3093673 : Blo 507795 3093673 := bstep (se 2 (by rfl) ⟨1160127, by rfl⟩ : syracuseStep 3093673 = 2320255) B2320255
theorem B1455529 : Blo 507795 1455529 := bstep (se 2 (by rfl) ⟨545823, by rfl⟩ : syracuseStep 1455529 = 1091647) B1091647
theorem B12695467 : Blo 507795 12695467 := bstep (se 1 (by rfl) ⟨9521600, by rfl⟩ : syracuseStep 12695467 = 19043201) B19043201
theorem B18593873 : Blo 507795 18593873 := bstep (se 2 (by rfl) ⟨6972702, by rfl⟩ : syracuseStep 18593873 = 13945405) B13945405
theorem B35338625 : Blo 507795 35338625 := bstep (se 2 (by rfl) ⟨13251984, by rfl⟩ : syracuseStep 35338625 = 26503969) B26503969
theorem B2178697 : Blo 507795 2178697 := bstep (se 2 (by rfl) ⟨817011, by rfl⟩ : syracuseStep 2178697 = 1634023) B1634023
theorem B2181107 : Blo 507795 2181107 := bstep (se 1 (by rfl) ⟨1635830, by rfl⟩ : syracuseStep 2181107 = 3271661) B3271661
theorem B27906119 : Blo 507795 27906119 := bstep (se 1 (by rfl) ⟨20929589, by rfl⟩ : syracuseStep 27906119 = 41859179) B41859179
theorem B1724489 : Blo 507795 1724489 := bstep (se 2 (by rfl) ⟨646683, by rfl⟩ : syracuseStep 1724489 = 1293367) B1293367
theorem B2906887 : Blo 507795 2906887 := bstep (se 1 (by rfl) ⟨2180165, by rfl⟩ : syracuseStep 2906887 = 4360331) B4360331
theorem B5823251 : Blo 507795 5823251 := bstep (se 1 (by rfl) ⟨4367438, by rfl⟩ : syracuseStep 5823251 = 8734877) B8734877
theorem B52812647 : Blo 507795 52812647 := bstep (se 1 (by rfl) ⟨39609485, by rfl⟩ : syracuseStep 52812647 = 79218971) B79218971
theorem B3268457 : Blo 507795 3268457 := bstep (se 2 (by rfl) ⟨1225671, by rfl⟩ : syracuseStep 3268457 = 2451343) B2451343
theorem B1958825 : Blo 507795 1958825 := bstep (se 2 (by rfl) ⟨734559, by rfl⟩ : syracuseStep 1958825 = 1469119) B1469119
theorem B12707873 : Blo 507795 12707873 := bstep (se 2 (by rfl) ⟨4765452, by rfl⟩ : syracuseStep 12707873 = 9530905) B9530905
theorem B2585195 : Blo 507795 2585195 := bstep (se 1 (by rfl) ⟨1938896, by rfl⟩ : syracuseStep 2585195 = 3877793) B3877793
theorem B1144943 : Blo 507795 1144943 := bstep (se 1 (by rfl) ⟨858707, by rfl⟩ : syracuseStep 1144943 = 1717415) B1717415
theorem B1148201 : Blo 507795 1148201 := bstep (se 2 (by rfl) ⟨430575, by rfl⟩ : syracuseStep 1148201 = 861151) B861151
theorem B1149659 : Blo 507795 1149659 := bstep (se 1 (by rfl) ⟨862244, by rfl⟩ : syracuseStep 1149659 = 1724489) B1724489
theorem B1940705 : Blo 507795 1940705 := bstep (se 2 (by rfl) ⟨727764, by rfl⟩ : syracuseStep 1940705 = 1455529) B1455529
theorem B3875849 : Blo 507795 3875849 := bstep (se 2 (by rfl) ⟨1453443, by rfl⟩ : syracuseStep 3875849 = 2906887) B2906887
theorem B12395915 : Blo 507795 12395915 := bstep (se 1 (by rfl) ⟨9296936, by rfl⟩ : syracuseStep 12395915 = 18593873) B18593873
theorem B763295 : Blo 507795 763295 := bstep (se 1 (by rfl) ⟨572471, by rfl⟩ : syracuseStep 763295 = 1144943) B1144943
theorem B765287 : Blo 507795 765287 := bstep (se 1 (by rfl) ⟨573965, by rfl⟩ : syracuseStep 765287 = 1147931) B1147931
theorem B1454071 : Blo 507795 1454071 := bstep (se 1 (by rfl) ⟨1090553, by rfl⟩ : syracuseStep 1454071 = 2181107) B2181107
theorem B766919 : Blo 507795 766919 := bstep (se 1 (by rfl) ⟨575189, by rfl⟩ : syracuseStep 766919 = 1150379) B1150379
theorem B964361 : Blo 507795 964361 := bstep (se 2 (by rfl) ⟨361635, by rfl⟩ : syracuseStep 964361 = 723271) B723271
theorem B3882167 : Blo 507795 3882167 := bstep (se 1 (by rfl) ⟨2911625, by rfl⟩ : syracuseStep 3882167 = 5823251) B5823251
theorem B35208431 : Blo 507795 35208431 := bstep (se 1 (by rfl) ⟨26406323, by rfl⟩ : syracuseStep 35208431 = 52812647) B52812647
theorem B2178971 : Blo 507795 2178971 := bstep (se 1 (by rfl) ⟨1634228, by rfl⟩ : syracuseStep 2178971 = 3268457) B3268457
theorem B5881835 : Blo 507795 5881835 := bstep (se 1 (by rfl) ⟨4411376, by rfl⟩ : syracuseStep 5881835 = 8822753) B8822753
theorem B8471915 : Blo 507795 8471915 := bstep (se 1 (by rfl) ⟨6353936, by rfl⟩ : syracuseStep 8471915 = 12707873) B12707873
theorem B509723 : Blo 507795 509723 := bstep (se 1 (by rfl) ⟨382292, by rfl⟩ : syracuseStep 509723 = 764585) B764585
theorem B16927289 : Blo 507795 16927289 := bstep (se 2 (by rfl) ⟨6347733, by rfl⟩ : syracuseStep 16927289 = 12695467) B12695467
theorem B1723463 : Blo 507795 1723463 := bstep (se 1 (by rfl) ⟨1292597, by rfl⟩ : syracuseStep 1723463 = 2585195) B2585195
theorem B511135 : Blo 507795 511135 := bstep (se 1 (by rfl) ⟨383351, by rfl⟩ : syracuseStep 511135 = 766703) B766703
theorem B511207 : Blo 507795 511207 := bstep (se 1 (by rfl) ⟨383405, by rfl⟩ : syracuseStep 511207 = 766811) B766811
theorem B2904929 : Blo 507795 2904929 := bstep (se 2 (by rfl) ⟨1089348, by rfl⟩ : syracuseStep 2904929 = 2178697) B2178697
theorem B18604079 : Blo 507795 18604079 := bstep (se 1 (by rfl) ⟨13953059, by rfl⟩ : syracuseStep 18604079 = 27906119) B27906119
theorem B1305883 : Blo 507795 1305883 := bstep (se 1 (by rfl) ⟨979412, by rfl⟩ : syracuseStep 1305883 = 1958825) B1958825
theorem B4124897 : Blo 507795 4124897 := bstep (se 2 (by rfl) ⟨1546836, by rfl⟩ : syracuseStep 4124897 = 3093673) B3093673
theorem B1144745 : Blo 507795 1144745 := bstep (se 2 (by rfl) ⟨429279, by rfl⟩ : syracuseStep 1144745 = 858559) B858559
theorem B23559083 : Blo 507795 23559083 := bstep (se 1 (by rfl) ⟨17669312, by rfl⟩ : syracuseStep 23559083 = 35338625) B35338625
theorem B1148975 : Blo 507795 1148975 := bstep (se 1 (by rfl) ⟨861731, by rfl⟩ : syracuseStep 1148975 = 1723463) B1723463
theorem B1936619 : Blo 507795 1936619 := bstep (se 1 (by rfl) ⟨1452464, by rfl⟩ : syracuseStep 1936619 = 2904929) B2904929
theorem B1741177 : Blo 507795 1741177 := bstep (se 2 (by rfl) ⟨652941, by rfl⟩ : syracuseStep 1741177 = 1305883) B1305883
theorem B1938761 : Blo 507795 1938761 := bstep (se 2 (by rfl) ⟨727035, by rfl⟩ : syracuseStep 1938761 = 1454071) B1454071
theorem B8263943 : Blo 507795 8263943 := bstep (se 1 (by rfl) ⟨6197957, by rfl⟩ : syracuseStep 8263943 = 12395915) B12395915
theorem B763163 : Blo 507795 763163 := bstep (se 1 (by rfl) ⟨572372, by rfl⟩ : syracuseStep 763163 = 1144745) B1144745
theorem B15706055 : Blo 507795 15706055 := bstep (se 1 (by rfl) ⟨11779541, by rfl⟩ : syracuseStep 15706055 = 23559083) B23559083
theorem B23472287 : Blo 507795 23472287 := bstep (se 1 (by rfl) ⟨17604215, by rfl⟩ : syracuseStep 23472287 = 35208431) B35208431
theorem B1452647 : Blo 507795 1452647 := bstep (se 1 (by rfl) ⟨1089485, by rfl⟩ : syracuseStep 1452647 = 2178971) B2178971
theorem B765467 : Blo 507795 765467 := bstep (se 1 (by rfl) ⟨574100, by rfl⟩ : syracuseStep 765467 = 1148201) B1148201
theorem B5647943 : Blo 507795 5647943 := bstep (se 1 (by rfl) ⟨4235957, by rfl⟩ : syracuseStep 5647943 = 8471915) B8471915
theorem B11284859 : Blo 507795 11284859 := bstep (se 1 (by rfl) ⟨8463644, by rfl⟩ : syracuseStep 11284859 = 16927289) B16927289
theorem B766439 : Blo 507795 766439 := bstep (se 1 (by rfl) ⟨574829, by rfl⟩ : syracuseStep 766439 = 1149659) B1149659
theorem B1293803 : Blo 507795 1293803 := bstep (se 1 (by rfl) ⟨970352, by rfl⟩ : syracuseStep 1293803 = 1940705) B1940705
theorem B12402719 : Blo 507795 12402719 := bstep (se 1 (by rfl) ⟨9302039, by rfl⟩ : syracuseStep 12402719 = 18604079) B18604079
theorem B508863 : Blo 507795 508863 := bstep (se 1 (by rfl) ⟨381647, by rfl⟩ : syracuseStep 508863 = 763295) B763295
theorem B510191 : Blo 507795 510191 := bstep (se 1 (by rfl) ⟨382643, by rfl⟩ : syracuseStep 510191 = 765287) B765287
theorem B511279 : Blo 507795 511279 := bstep (se 1 (by rfl) ⟨383459, by rfl⟩ : syracuseStep 511279 = 766919) B766919
theorem B642907 : Blo 507795 642907 := bstep (se 1 (by rfl) ⟨482180, by rfl⟩ : syracuseStep 642907 = 964361) B964361
theorem B3921223 : Blo 507795 3921223 := bstep (se 1 (by rfl) ⟨2940917, by rfl⟩ : syracuseStep 3921223 = 5881835) B5881835
theorem B2583899 : Blo 507795 2583899 := bstep (se 1 (by rfl) ⟨1937924, by rfl⟩ : syracuseStep 2583899 = 3875849) B3875849
theorem B2749931 : Blo 507795 2749931 := bstep (se 1 (by rfl) ⟨2062448, by rfl⟩ : syracuseStep 2749931 = 4124897) B4124897
theorem B2588111 : Blo 507795 2588111 := bstep (se 1 (by rfl) ⟨1941083, by rfl⟩ : syracuseStep 2588111 = 3882167) B3882167
theorem B5509295 : Blo 507795 5509295 := bstep (se 1 (by rfl) ⟨4131971, by rfl⟩ : syracuseStep 5509295 = 8263943) B8263943
theorem B857209 : Blo 507795 857209 := bstep (se 2 (by rfl) ⟨321453, by rfl⟩ : syracuseStep 857209 = 642907) B642907
theorem B862535 : Blo 507795 862535 := bstep (se 1 (by rfl) ⟨646901, by rfl⟩ : syracuseStep 862535 = 1293803) B1293803
theorem B8268479 : Blo 507795 8268479 := bstep (se 1 (by rfl) ⟨6201359, by rfl⟩ : syracuseStep 8268479 = 12402719) B12402719
theorem B765983 : Blo 507795 765983 := bstep (se 1 (by rfl) ⟨574487, by rfl⟩ : syracuseStep 765983 = 1148975) B1148975
theorem B1291079 : Blo 507795 1291079 := bstep (se 1 (by rfl) ⟨968309, by rfl⟩ : syracuseStep 1291079 = 1936619) B1936619
theorem B1292507 : Blo 507795 1292507 := bstep (se 1 (by rfl) ⟨969380, by rfl⟩ : syracuseStep 1292507 = 1938761) B1938761
theorem B508775 : Blo 507795 508775 := bstep (se 1 (by rfl) ⟨381581, by rfl⟩ : syracuseStep 508775 = 763163) B763163
theorem B10470703 : Blo 507795 10470703 := bstep (se 1 (by rfl) ⟨7853027, by rfl⟩ : syracuseStep 10470703 = 15706055) B15706055
theorem B15648191 : Blo 507795 15648191 := bstep (se 1 (by rfl) ⟨11736143, by rfl⟩ : syracuseStep 15648191 = 23472287) B23472287
theorem B968431 : Blo 507795 968431 := bstep (se 1 (by rfl) ⟨726323, by rfl⟩ : syracuseStep 968431 = 1452647) B1452647
theorem B5228297 : Blo 507795 5228297 := bstep (se 2 (by rfl) ⟨1960611, by rfl⟩ : syracuseStep 5228297 = 3921223) B3921223
theorem B1722599 : Blo 507795 1722599 := bstep (se 1 (by rfl) ⟨1291949, by rfl⟩ : syracuseStep 1722599 = 2583899) B2583899
theorem B510311 : Blo 507795 510311 := bstep (se 1 (by rfl) ⟨382733, by rfl⟩ : syracuseStep 510311 = 765467) B765467
theorem B7523239 : Blo 507795 7523239 := bstep (se 1 (by rfl) ⟨5642429, by rfl⟩ : syracuseStep 7523239 = 11284859) B11284859
theorem B510959 : Blo 507795 510959 := bstep (se 1 (by rfl) ⟨383219, by rfl⟩ : syracuseStep 510959 = 766439) B766439
theorem B1725407 : Blo 507795 1725407 := bstep (se 1 (by rfl) ⟨1294055, by rfl⟩ : syracuseStep 1725407 = 2588111) B2588111
theorem B2321569 : Blo 507795 2321569 := bstep (se 2 (by rfl) ⟨870588, by rfl⟩ : syracuseStep 2321569 = 1741177) B1741177
theorem B3765295 : Blo 507795 3765295 := bstep (se 1 (by rfl) ⟨2823971, by rfl⟩ : syracuseStep 3765295 = 5647943) B5647943
theorem B1833287 : Blo 507795 1833287 := bstep (se 1 (by rfl) ⟨1374965, by rfl⟩ : syracuseStep 1833287 = 2749931) B2749931
theorem B1148399 : Blo 507795 1148399 := bstep (se 1 (by rfl) ⟨861299, by rfl⟩ : syracuseStep 1148399 = 1722599) B1722599
theorem B13960937 : Blo 507795 13960937 := bstep (se 2 (by rfl) ⟨5235351, by rfl⟩ : syracuseStep 13960937 = 10470703) B10470703
theorem B3672863 : Blo 507795 3672863 := bstep (se 1 (by rfl) ⟨2754647, by rfl⟩ : syracuseStep 3672863 = 5509295) B5509295
theorem B1150271 : Blo 507795 1150271 := bstep (se 1 (by rfl) ⟨862703, by rfl⟩ : syracuseStep 1150271 = 1725407) B1725407
theorem B10030985 : Blo 507795 10030985 := bstep (se 2 (by rfl) ⟨3761619, by rfl⟩ : syracuseStep 10030985 = 7523239) B7523239
theorem B4888765 : Blo 507795 4888765 := bstep (se 3 (by rfl) ⟨916643, by rfl⟩ : syracuseStep 4888765 = 1833287) B1833287
theorem B5020393 : Blo 507795 5020393 := bstep (se 2 (by rfl) ⟨1882647, by rfl⟩ : syracuseStep 5020393 = 3765295) B3765295
theorem B5512319 : Blo 507795 5512319 := bstep (se 1 (by rfl) ⟨4134239, by rfl⟩ : syracuseStep 5512319 = 8268479) B8268479
theorem B860719 : Blo 507795 860719 := bstep (se 1 (by rfl) ⟨645539, by rfl⟩ : syracuseStep 860719 = 1291079) B1291079
theorem B861671 : Blo 507795 861671 := bstep (se 1 (by rfl) ⟨646253, by rfl⟩ : syracuseStep 861671 = 1292507) B1292507
theorem B10432127 : Blo 507795 10432127 := bstep (se 1 (by rfl) ⟨7824095, by rfl⟩ : syracuseStep 10432127 = 15648191) B15648191
theorem B3485531 : Blo 507795 3485531 := bstep (se 1 (by rfl) ⟨2614148, by rfl⟩ : syracuseStep 3485531 = 5228297) B5228297
theorem B1291241 : Blo 507795 1291241 := bstep (se 2 (by rfl) ⟨484215, by rfl⟩ : syracuseStep 1291241 = 968431) B968431
theorem B3095425 : Blo 507795 3095425 := bstep (se 2 (by rfl) ⟨1160784, by rfl⟩ : syracuseStep 3095425 = 2321569) B2321569
theorem B575023 : Blo 507795 575023 := bstep (se 1 (by rfl) ⟨431267, by rfl⟩ : syracuseStep 575023 = 862535) B862535
theorem B510655 : Blo 507795 510655 := bstep (se 1 (by rfl) ⟨382991, by rfl⟩ : syracuseStep 510655 = 765983) B765983
theorem B1142945 : Blo 507795 1142945 := bstep (se 2 (by rfl) ⟨428604, by rfl⟩ : syracuseStep 1142945 = 857209) B857209
theorem B1147625 : Blo 507795 1147625 := bstep (se 2 (by rfl) ⟨430359, by rfl⟩ : syracuseStep 1147625 = 860719) B860719
theorem B6687323 : Blo 507795 6687323 := bstep (se 1 (by rfl) ⟨5015492, by rfl⟩ : syracuseStep 6687323 = 10030985) B10030985
theorem B37229165 : Blo 507795 37229165 := bstep (se 3 (by rfl) ⟨6980468, by rfl⟩ : syracuseStep 37229165 = 13960937) B13960937
theorem B3674879 : Blo 507795 3674879 := bstep (se 1 (by rfl) ⟨2756159, by rfl⟩ : syracuseStep 3674879 = 5512319) B5512319
theorem B6954751 : Blo 507795 6954751 := bstep (se 1 (by rfl) ⟨5216063, by rfl⟩ : syracuseStep 6954751 = 10432127) B10432127
theorem B761963 : Blo 507795 761963 := bstep (se 1 (by rfl) ⟨571472, by rfl⟩ : syracuseStep 761963 = 1142945) B1142945
theorem B860827 : Blo 507795 860827 := bstep (se 1 (by rfl) ⟨645620, by rfl⟩ : syracuseStep 860827 = 1291241) B1291241
theorem B6693857 : Blo 507795 6693857 := bstep (se 2 (by rfl) ⟨2510196, by rfl⟩ : syracuseStep 6693857 = 5020393) B5020393
theorem B765599 : Blo 507795 765599 := bstep (se 1 (by rfl) ⟨574199, by rfl⟩ : syracuseStep 765599 = 1148399) B1148399
theorem B766697 : Blo 507795 766697 := bstep (se 2 (by rfl) ⟨287511, by rfl⟩ : syracuseStep 766697 = 575023) B575023
theorem B766847 : Blo 507795 766847 := bstep (se 1 (by rfl) ⟨575135, by rfl⟩ : syracuseStep 766847 = 1150271) B1150271
theorem B574447 : Blo 507795 574447 := bstep (se 1 (by rfl) ⟨430835, by rfl⟩ : syracuseStep 574447 = 861671) B861671
theorem B9294749 : Blo 507795 9294749 := bstep (se 3 (by rfl) ⟨1742765, by rfl⟩ : syracuseStep 9294749 = 3485531) B3485531
theorem B2448575 : Blo 507795 2448575 := bstep (se 1 (by rfl) ⟨1836431, by rfl⟩ : syracuseStep 2448575 = 3672863) B3672863
theorem B16508933 : Blo 507795 16508933 := bstep (se 4 (by rfl) ⟨1547712, by rfl⟩ : syracuseStep 16508933 = 3095425) B3095425
theorem B6518353 : Blo 507795 6518353 := bstep (se 2 (by rfl) ⟨2444382, by rfl⟩ : syracuseStep 6518353 = 4888765) B4888765
theorem B1147769 : Blo 507795 1147769 := bstep (se 2 (by rfl) ⟨430413, by rfl⟩ : syracuseStep 1147769 = 860827) B860827
theorem B4458215 : Blo 507795 4458215 := bstep (se 1 (by rfl) ⟨3343661, by rfl⟩ : syracuseStep 4458215 = 6687323) B6687323
theorem B6196499 : Blo 507795 6196499 := bstep (se 1 (by rfl) ⟨4647374, by rfl⟩ : syracuseStep 6196499 = 9294749) B9294749
theorem B4462571 : Blo 507795 4462571 := bstep (se 1 (by rfl) ⟨3346928, by rfl⟩ : syracuseStep 4462571 = 6693857) B6693857
theorem B8691137 : Blo 507795 8691137 := bstep (se 2 (by rfl) ⟨3259176, by rfl⟩ : syracuseStep 8691137 = 6518353) B6518353
theorem B765083 : Blo 507795 765083 := bstep (se 1 (by rfl) ⟨573812, by rfl⟩ : syracuseStep 765083 = 1147625) B1147625
theorem B765929 : Blo 507795 765929 := bstep (se 2 (by rfl) ⟨287223, by rfl⟩ : syracuseStep 765929 = 574447) B574447
theorem B24819443 : Blo 507795 24819443 := bstep (se 1 (by rfl) ⟨18614582, by rfl⟩ : syracuseStep 24819443 = 37229165) B37229165
theorem B507975 : Blo 507795 507975 := bstep (se 1 (by rfl) ⟨380981, by rfl⟩ : syracuseStep 507975 = 761963) B761963
theorem B510399 : Blo 507795 510399 := bstep (se 1 (by rfl) ⟨382799, by rfl⟩ : syracuseStep 510399 = 765599) B765599
theorem B511131 : Blo 507795 511131 := bstep (se 1 (by rfl) ⟨383348, by rfl⟩ : syracuseStep 511131 = 766697) B766697
theorem B511231 : Blo 507795 511231 := bstep (se 1 (by rfl) ⟨383423, by rfl⟩ : syracuseStep 511231 = 766847) B766847
theorem B2449919 : Blo 507795 2449919 := bstep (se 1 (by rfl) ⟨1837439, by rfl⟩ : syracuseStep 2449919 = 3674879) B3674879
theorem B1632383 : Blo 507795 1632383 := bstep (se 1 (by rfl) ⟨1224287, by rfl⟩ : syracuseStep 1632383 = 2448575) B2448575
theorem B11005955 : Blo 507795 11005955 := bstep (se 1 (by rfl) ⟨8254466, by rfl⟩ : syracuseStep 11005955 = 16508933) B16508933
theorem B9273001 : Blo 507795 9273001 := bstep (se 2 (by rfl) ⟨3477375, by rfl⟩ : syracuseStep 9273001 = 6954751) B6954751
theorem B4130999 : Blo 507795 4130999 := bstep (se 1 (by rfl) ⟨3098249, by rfl⟩ : syracuseStep 4130999 = 6196499) B6196499
theorem B11900189 : Blo 507795 11900189 := bstep (se 3 (by rfl) ⟨2231285, by rfl⟩ : syracuseStep 11900189 = 4462571) B4462571
theorem B1088255 : Blo 507795 1088255 := bstep (se 1 (by rfl) ⟨816191, by rfl⟩ : syracuseStep 1088255 = 1632383) B1632383
theorem B12364001 : Blo 507795 12364001 := bstep (se 2 (by rfl) ⟨4636500, by rfl⟩ : syracuseStep 12364001 = 9273001) B9273001
theorem B765179 : Blo 507795 765179 := bstep (se 1 (by rfl) ⟨573884, by rfl⟩ : syracuseStep 765179 = 1147769) B1147769
theorem B510055 : Blo 507795 510055 := bstep (se 1 (by rfl) ⟨382541, by rfl⟩ : syracuseStep 510055 = 765083) B765083
theorem B510619 : Blo 507795 510619 := bstep (se 1 (by rfl) ⟨382964, by rfl⟩ : syracuseStep 510619 = 765929) B765929
theorem B2972143 : Blo 507795 2972143 := bstep (se 1 (by rfl) ⟨2229107, by rfl⟩ : syracuseStep 2972143 = 4458215) B4458215
theorem B5794091 : Blo 507795 5794091 := bstep (se 1 (by rfl) ⟨4345568, by rfl⟩ : syracuseStep 5794091 = 8691137) B8691137
theorem B1633279 : Blo 507795 1633279 := bstep (se 1 (by rfl) ⟨1224959, by rfl⟩ : syracuseStep 1633279 = 2449919) B2449919
theorem B7337303 : Blo 507795 7337303 := bstep (se 1 (by rfl) ⟨5502977, by rfl⟩ : syracuseStep 7337303 = 11005955) B11005955
theorem B16546295 : Blo 507795 16546295 := bstep (se 1 (by rfl) ⟨12409721, by rfl⟩ : syracuseStep 16546295 = 24819443) B24819443
theorem B2753999 : Blo 507795 2753999 := bstep (se 1 (by rfl) ⟨2065499, by rfl⟩ : syracuseStep 2753999 = 4130999) B4130999
theorem B7933459 : Blo 507795 7933459 := bstep (se 1 (by rfl) ⟨5950094, by rfl⟩ : syracuseStep 7933459 = 11900189) B11900189
theorem B4891535 : Blo 507795 4891535 := bstep (se 1 (by rfl) ⟨3668651, by rfl⟩ : syracuseStep 4891535 = 7337303) B7337303
theorem B2177705 : Blo 507795 2177705 := bstep (se 2 (by rfl) ⟨816639, by rfl⟩ : syracuseStep 2177705 = 1633279) B1633279
theorem B8242667 : Blo 507795 8242667 := bstep (se 1 (by rfl) ⟨6182000, by rfl⟩ : syracuseStep 8242667 = 12364001) B12364001
theorem B2902013 : Blo 507795 2902013 := bstep (se 3 (by rfl) ⟨544127, by rfl⟩ : syracuseStep 2902013 = 1088255) B1088255
theorem B510119 : Blo 507795 510119 := bstep (se 1 (by rfl) ⟨382589, by rfl⟩ : syracuseStep 510119 = 765179) B765179
theorem B11030863 : Blo 507795 11030863 := bstep (se 1 (by rfl) ⟨8273147, by rfl⟩ : syracuseStep 11030863 = 16546295) B16546295
theorem B3862727 : Blo 507795 3862727 := bstep (se 1 (by rfl) ⟨2897045, by rfl⟩ : syracuseStep 3862727 = 5794091) B5794091
theorem B3962857 : Blo 507795 3962857 := bstep (se 2 (by rfl) ⟨1486071, by rfl⟩ : syracuseStep 3962857 = 2972143) B2972143
theorem B1835999 : Blo 507795 1835999 := bstep (se 1 (by rfl) ⟨1376999, by rfl⟩ : syracuseStep 1835999 = 2753999) B2753999
theorem B1934675 : Blo 507795 1934675 := bstep (se 1 (by rfl) ⟨1451006, by rfl⟩ : syracuseStep 1934675 = 2902013) B2902013
theorem B5807213 : Blo 507795 5807213 := bstep (se 3 (by rfl) ⟨1088852, by rfl⟩ : syracuseStep 5807213 = 2177705) B2177705
theorem B5283809 : Blo 507795 5283809 := bstep (se 2 (by rfl) ⟨1981428, by rfl⟩ : syracuseStep 5283809 = 3962857) B3962857
theorem B3261023 : Blo 507795 3261023 := bstep (se 1 (by rfl) ⟨2445767, by rfl⟩ : syracuseStep 3261023 = 4891535) B4891535
theorem B2575151 : Blo 507795 2575151 := bstep (se 1 (by rfl) ⟨1931363, by rfl⟩ : syracuseStep 2575151 = 3862727) B3862727
theorem B5495111 : Blo 507795 5495111 := bstep (se 1 (by rfl) ⟨4121333, by rfl⟩ : syracuseStep 5495111 = 8242667) B8242667
theorem B10577945 : Blo 507795 10577945 := bstep (se 2 (by rfl) ⟨3966729, by rfl⟩ : syracuseStep 10577945 = 7933459) B7933459
theorem B14707817 : Blo 507795 14707817 := bstep (se 2 (by rfl) ⟨5515431, by rfl⟩ : syracuseStep 14707817 = 11030863) B11030863
theorem B3871475 : Blo 507795 3871475 := bstep (se 1 (by rfl) ⟨2903606, by rfl⟩ : syracuseStep 3871475 = 5807213) B5807213
theorem B7051963 : Blo 507795 7051963 := bstep (se 1 (by rfl) ⟨5288972, by rfl⟩ : syracuseStep 7051963 = 10577945) B10577945
theorem B9805211 : Blo 507795 9805211 := bstep (se 1 (by rfl) ⟨7353908, by rfl⟩ : syracuseStep 9805211 = 14707817) B14707817
theorem B2174015 : Blo 507795 2174015 := bstep (se 1 (by rfl) ⟨1630511, by rfl⟩ : syracuseStep 2174015 = 3261023) B3261023
theorem B1223999 : Blo 507795 1223999 := bstep (se 1 (by rfl) ⟨917999, by rfl⟩ : syracuseStep 1223999 = 1835999) B1835999
theorem B1289783 : Blo 507795 1289783 := bstep (se 1 (by rfl) ⟨967337, by rfl⟩ : syracuseStep 1289783 = 1934675) B1934675
theorem B1716767 : Blo 507795 1716767 := bstep (se 1 (by rfl) ⟨1287575, by rfl⟩ : syracuseStep 1716767 = 2575151) B2575151
theorem B3522539 : Blo 507795 3522539 := bstep (se 1 (by rfl) ⟨2641904, by rfl⟩ : syracuseStep 3522539 = 5283809) B5283809
theorem B3663407 : Blo 507795 3663407 := bstep (se 1 (by rfl) ⟨2747555, by rfl⟩ : syracuseStep 3663407 = 5495111) B5495111
theorem B1449343 : Blo 507795 1449343 := bstep (se 1 (by rfl) ⟨1087007, by rfl⟩ : syracuseStep 1449343 = 2174015) B2174015
theorem B859855 : Blo 507795 859855 := bstep (se 1 (by rfl) ⟨644891, by rfl⟩ : syracuseStep 859855 = 1289783) B1289783
theorem B6536807 : Blo 507795 6536807 := bstep (se 1 (by rfl) ⟨4902605, by rfl⟩ : syracuseStep 6536807 = 9805211) B9805211
theorem B2442271 : Blo 507795 2442271 := bstep (se 1 (by rfl) ⟨1831703, by rfl⟩ : syracuseStep 2442271 = 3663407) B3663407
theorem B2348359 : Blo 507795 2348359 := bstep (se 1 (by rfl) ⟨1761269, by rfl⟩ : syracuseStep 2348359 = 3522539) B3522539
theorem B2580983 : Blo 507795 2580983 := bstep (se 1 (by rfl) ⟨1935737, by rfl⟩ : syracuseStep 2580983 = 3871475) B3871475
theorem B815999 : Blo 507795 815999 := bstep (se 1 (by rfl) ⟨611999, by rfl⟩ : syracuseStep 815999 = 1223999) B1223999
theorem B1144511 : Blo 507795 1144511 := bstep (se 1 (by rfl) ⟨858383, by rfl⟩ : syracuseStep 1144511 = 1716767) B1716767
theorem B9402617 : Blo 507795 9402617 := bstep (se 2 (by rfl) ⟨3525981, by rfl⟩ : syracuseStep 9402617 = 7051963) B7051963
theorem B12524581 : Blo 507795 12524581 := bstep (se 4 (by rfl) ⟨1174179, by rfl⟩ : syracuseStep 12524581 = 2348359) B2348359
theorem B763007 : Blo 507795 763007 := bstep (se 1 (by rfl) ⟨572255, by rfl⟩ : syracuseStep 763007 = 1144511) B1144511
theorem B6268411 : Blo 507795 6268411 := bstep (se 1 (by rfl) ⟨4701308, by rfl⟩ : syracuseStep 6268411 = 9402617) B9402617
theorem B3256361 : Blo 507795 3256361 := bstep (se 2 (by rfl) ⟨1221135, by rfl⟩ : syracuseStep 3256361 = 2442271) B2442271
theorem B2175997 : Blo 507795 2175997 := bstep (se 3 (by rfl) ⟨407999, by rfl⟩ : syracuseStep 2175997 = 815999) B815999
theorem B1720655 : Blo 507795 1720655 := bstep (se 1 (by rfl) ⟨1290491, by rfl⟩ : syracuseStep 1720655 = 2580983) B2580983
theorem B1932457 : Blo 507795 1932457 := bstep (se 2 (by rfl) ⟨724671, by rfl⟩ : syracuseStep 1932457 = 1449343) B1449343
theorem B1146473 : Blo 507795 1146473 := bstep (se 2 (by rfl) ⟨429927, by rfl⟩ : syracuseStep 1146473 = 859855) B859855
theorem B4357871 : Blo 507795 4357871 := bstep (se 1 (by rfl) ⟨3268403, by rfl⟩ : syracuseStep 4357871 = 6536807) B6536807
theorem B1147103 : Blo 507795 1147103 := bstep (se 1 (by rfl) ⟨860327, by rfl⟩ : syracuseStep 1147103 = 1720655) B1720655
theorem B33431525 : Blo 507795 33431525 := bstep (se 4 (by rfl) ⟨3134205, by rfl⟩ : syracuseStep 33431525 = 6268411) B6268411
theorem B2170907 : Blo 507795 2170907 := bstep (se 1 (by rfl) ⟨1628180, by rfl⟩ : syracuseStep 2170907 = 3256361) B3256361
theorem B764315 : Blo 507795 764315 := bstep (se 1 (by rfl) ⟨573236, by rfl⟩ : syracuseStep 764315 = 1146473) B1146473
theorem B508671 : Blo 507795 508671 := bstep (se 1 (by rfl) ⟨381503, by rfl⟩ : syracuseStep 508671 = 763007) B763007
theorem B2901329 : Blo 507795 2901329 := bstep (se 2 (by rfl) ⟨1087998, by rfl⟩ : syracuseStep 2901329 = 2175997) B2175997
theorem B16699441 : Blo 507795 16699441 := bstep (se 2 (by rfl) ⟨6262290, by rfl⟩ : syracuseStep 16699441 = 12524581) B12524581
theorem B2576609 : Blo 507795 2576609 := bstep (se 2 (by rfl) ⟨966228, by rfl⟩ : syracuseStep 2576609 = 1932457) B1932457
theorem B2905247 : Blo 507795 2905247 := bstep (se 1 (by rfl) ⟨2178935, by rfl⟩ : syracuseStep 2905247 = 4357871) B4357871
theorem B1934219 : Blo 507795 1934219 := bstep (se 1 (by rfl) ⟨1450664, by rfl⟩ : syracuseStep 1934219 = 2901329) B2901329
theorem B1936831 : Blo 507795 1936831 := bstep (se 1 (by rfl) ⟨1452623, by rfl⟩ : syracuseStep 1936831 = 2905247) B2905247
theorem B22287683 : Blo 507795 22287683 := bstep (se 1 (by rfl) ⟨16715762, by rfl⟩ : syracuseStep 22287683 = 33431525) B33431525
theorem B1447271 : Blo 507795 1447271 := bstep (se 1 (by rfl) ⟨1085453, by rfl⟩ : syracuseStep 1447271 = 2170907) B2170907
theorem B764735 : Blo 507795 764735 := bstep (se 1 (by rfl) ⟨573551, by rfl⟩ : syracuseStep 764735 = 1147103) B1147103
theorem B1717739 : Blo 507795 1717739 := bstep (se 1 (by rfl) ⟨1288304, by rfl⟩ : syracuseStep 1717739 = 2576609) B2576609
theorem B22265921 : Blo 507795 22265921 := bstep (se 2 (by rfl) ⟨8349720, by rfl⟩ : syracuseStep 22265921 = 16699441) B16699441
theorem B509543 : Blo 507795 509543 := bstep (se 1 (by rfl) ⟨382157, by rfl⟩ : syracuseStep 509543 = 764315) B764315
theorem B14843947 : Blo 507795 14843947 := bstep (se 1 (by rfl) ⟨11132960, by rfl⟩ : syracuseStep 14843947 = 22265921) B22265921
theorem B1289479 : Blo 507795 1289479 := bstep (se 1 (by rfl) ⟨967109, by rfl⟩ : syracuseStep 1289479 = 1934219) B1934219
theorem B964847 : Blo 507795 964847 := bstep (se 1 (by rfl) ⟨723635, by rfl⟩ : syracuseStep 964847 = 1447271) B1447271
theorem B509823 : Blo 507795 509823 := bstep (se 1 (by rfl) ⟨382367, by rfl⟩ : syracuseStep 509823 = 764735) B764735
theorem B59433821 : Blo 507795 59433821 := bstep (se 3 (by rfl) ⟨11143841, by rfl⟩ : syracuseStep 59433821 = 22287683) B22287683
theorem B2582441 : Blo 507795 2582441 := bstep (se 2 (by rfl) ⟨968415, by rfl⟩ : syracuseStep 2582441 = 1936831) B1936831
theorem B1145159 : Blo 507795 1145159 := bstep (se 1 (by rfl) ⟨858869, by rfl⟩ : syracuseStep 1145159 = 1717739) B1717739
theorem B19791929 : Blo 507795 19791929 := bstep (se 2 (by rfl) ⟨7421973, by rfl⟩ : syracuseStep 19791929 = 14843947) B14843947
theorem B39622547 : Blo 507795 39622547 := bstep (se 1 (by rfl) ⟨29716910, by rfl⟩ : syracuseStep 39622547 = 59433821) B59433821
theorem B763439 : Blo 507795 763439 := bstep (se 1 (by rfl) ⟨572579, by rfl⟩ : syracuseStep 763439 = 1145159) B1145159
theorem B1719305 : Blo 507795 1719305 := bstep (se 2 (by rfl) ⟨644739, by rfl⟩ : syracuseStep 1719305 = 1289479) B1289479
theorem B1721627 : Blo 507795 1721627 := bstep (se 1 (by rfl) ⟨1291220, by rfl⟩ : syracuseStep 1721627 = 2582441) B2582441
theorem B643231 : Blo 507795 643231 := bstep (se 1 (by rfl) ⟨482423, by rfl⟩ : syracuseStep 643231 = 964847) B964847
theorem B1147751 : Blo 507795 1147751 := bstep (se 1 (by rfl) ⟨860813, by rfl⟩ : syracuseStep 1147751 = 1721627) B1721627
theorem B26415031 : Blo 507795 26415031 := bstep (se 1 (by rfl) ⟨19811273, by rfl⟩ : syracuseStep 26415031 = 39622547) B39622547
theorem B857641 : Blo 507795 857641 := bstep (se 2 (by rfl) ⟨321615, by rfl⟩ : syracuseStep 857641 = 643231) B643231
theorem B508959 : Blo 507795 508959 := bstep (se 1 (by rfl) ⟨381719, by rfl⟩ : syracuseStep 508959 = 763439) B763439
theorem B13194619 : Blo 507795 13194619 := bstep (se 1 (by rfl) ⟨9895964, by rfl⟩ : syracuseStep 13194619 = 19791929) B19791929
theorem B1146203 : Blo 507795 1146203 := bstep (se 1 (by rfl) ⟨859652, by rfl⟩ : syracuseStep 1146203 = 1719305) B1719305
theorem B764135 : Blo 507795 764135 := bstep (se 1 (by rfl) ⟨573101, by rfl⟩ : syracuseStep 764135 = 1146203) B1146203
theorem B765167 : Blo 507795 765167 := bstep (se 1 (by rfl) ⟨573875, by rfl⟩ : syracuseStep 765167 = 1147751) B1147751
theorem B70371301 : Blo 507795 70371301 := bstep (se 4 (by rfl) ⟨6597309, by rfl⟩ : syracuseStep 70371301 = 13194619) B13194619
theorem B35220041 : Blo 507795 35220041 := bstep (se 2 (by rfl) ⟨13207515, by rfl⟩ : syracuseStep 35220041 = 26415031) B26415031
theorem B1143521 : Blo 507795 1143521 := bstep (se 2 (by rfl) ⟨428820, by rfl⟩ : syracuseStep 1143521 = 857641) B857641
theorem B762347 : Blo 507795 762347 := bstep (se 1 (by rfl) ⟨571760, by rfl⟩ : syracuseStep 762347 = 1143521) B1143521
theorem B93828401 : Blo 507795 93828401 := bstep (se 2 (by rfl) ⟨35185650, by rfl⟩ : syracuseStep 93828401 = 70371301) B70371301
theorem B509423 : Blo 507795 509423 := bstep (se 1 (by rfl) ⟨382067, by rfl⟩ : syracuseStep 509423 = 764135) B764135
theorem B23480027 : Blo 507795 23480027 := bstep (se 1 (by rfl) ⟨17610020, by rfl⟩ : syracuseStep 23480027 = 35220041) B35220041
theorem B510111 : Blo 507795 510111 := bstep (se 1 (by rfl) ⟨382583, by rfl⟩ : syracuseStep 510111 = 765167) B765167
theorem B508231 : Blo 507795 508231 := bstep (se 1 (by rfl) ⟨381173, by rfl⟩ : syracuseStep 508231 = 762347) B762347
theorem B15653351 : Blo 507795 15653351 := bstep (se 1 (by rfl) ⟨11740013, by rfl⟩ : syracuseStep 15653351 = 23480027) B23480027
theorem B62552267 : Blo 507795 62552267 := bstep (se 1 (by rfl) ⟨46914200, by rfl⟩ : syracuseStep 62552267 = 93828401) B93828401
theorem B10435567 : Blo 507795 10435567 := bstep (se 1 (by rfl) ⟨7826675, by rfl⟩ : syracuseStep 10435567 = 15653351) B15653351
theorem B41701511 : Blo 507795 41701511 := bstep (se 1 (by rfl) ⟨31276133, by rfl⟩ : syracuseStep 41701511 = 62552267) B62552267
theorem B13914089 : Blo 507795 13914089 := bstep (se 2 (by rfl) ⟨5217783, by rfl⟩ : syracuseStep 13914089 = 10435567) B10435567
theorem B111204029 : Blo 507795 111204029 := bstep (se 3 (by rfl) ⟨20850755, by rfl⟩ : syracuseStep 111204029 = 41701511) B41701511
theorem B9276059 : Blo 507795 9276059 := bstep (se 1 (by rfl) ⟨6957044, by rfl⟩ : syracuseStep 9276059 = 13914089) B13914089
theorem B74136019 : Blo 507795 74136019 := bstep (se 1 (by rfl) ⟨55602014, by rfl⟩ : syracuseStep 74136019 = 111204029) B111204029
theorem B98848025 : Blo 507795 98848025 := bstep (se 2 (by rfl) ⟨37068009, by rfl⟩ : syracuseStep 98848025 = 74136019) B74136019
theorem B6184039 : Blo 507795 6184039 := bstep (se 1 (by rfl) ⟨4638029, by rfl⟩ : syracuseStep 6184039 = 9276059) B9276059
theorem B65898683 : Blo 507795 65898683 := bstep (se 1 (by rfl) ⟨49424012, by rfl⟩ : syracuseStep 65898683 = 98848025) B98848025
theorem B8245385 : Blo 507795 8245385 := bstep (se 2 (by rfl) ⟨3092019, by rfl⟩ : syracuseStep 8245385 = 6184039) B6184039
theorem B43932455 : Blo 507795 43932455 := bstep (se 1 (by rfl) ⟨32949341, by rfl⟩ : syracuseStep 43932455 = 65898683) B65898683
theorem B5496923 : Blo 507795 5496923 := bstep (se 1 (by rfl) ⟨4122692, by rfl⟩ : syracuseStep 5496923 = 8245385) B8245385
theorem B29288303 : Blo 507795 29288303 := bstep (se 1 (by rfl) ⟨21966227, by rfl⟩ : syracuseStep 29288303 = 43932455) B43932455
theorem B3664615 : Blo 507795 3664615 := bstep (se 1 (by rfl) ⟨2748461, by rfl⟩ : syracuseStep 3664615 = 5496923) B5496923
theorem B4886153 : Blo 507795 4886153 := bstep (se 2 (by rfl) ⟨1832307, by rfl⟩ : syracuseStep 4886153 = 3664615) B3664615
theorem B19525535 : Blo 507795 19525535 := bstep (se 1 (by rfl) ⟨14644151, by rfl⟩ : syracuseStep 19525535 = 29288303) B29288303
theorem B13017023 : Blo 507795 13017023 := bstep (se 1 (by rfl) ⟨9762767, by rfl⟩ : syracuseStep 13017023 = 19525535) B19525535
theorem B3257435 : Blo 507795 3257435 := bstep (se 1 (by rfl) ⟨2443076, by rfl⟩ : syracuseStep 3257435 = 4886153) B4886153
theorem B2171623 : Blo 507795 2171623 := bstep (se 1 (by rfl) ⟨1628717, by rfl⟩ : syracuseStep 2171623 = 3257435) B3257435
theorem B8678015 : Blo 507795 8678015 := bstep (se 1 (by rfl) ⟨6508511, by rfl⟩ : syracuseStep 8678015 = 13017023) B13017023
theorem B2895497 : Blo 507795 2895497 := bstep (se 2 (by rfl) ⟨1085811, by rfl⟩ : syracuseStep 2895497 = 2171623) B2171623
theorem B5785343 : Blo 507795 5785343 := bstep (se 1 (by rfl) ⟨4339007, by rfl⟩ : syracuseStep 5785343 = 8678015) B8678015
theorem B3856895 : Blo 507795 3856895 := bstep (se 1 (by rfl) ⟨2892671, by rfl⟩ : syracuseStep 3856895 = 5785343) B5785343
theorem B1930331 : Blo 507795 1930331 := bstep (se 1 (by rfl) ⟨1447748, by rfl⟩ : syracuseStep 1930331 = 2895497) B2895497
theorem B1286887 : Blo 507795 1286887 := bstep (se 1 (by rfl) ⟨965165, by rfl⟩ : syracuseStep 1286887 = 1930331) B1930331
theorem B2571263 : Blo 507795 2571263 := bstep (se 1 (by rfl) ⟨1928447, by rfl⟩ : syracuseStep 2571263 = 3856895) B3856895
theorem B1714175 : Blo 507795 1714175 := bstep (se 1 (by rfl) ⟨1285631, by rfl⟩ : syracuseStep 1714175 = 2571263) B2571263
theorem B1715849 : Blo 507795 1715849 := bstep (se 2 (by rfl) ⟨643443, by rfl⟩ : syracuseStep 1715849 = 1286887) B1286887
theorem B1142783 : Blo 507795 1142783 := bstep (se 1 (by rfl) ⟨857087, by rfl⟩ : syracuseStep 1142783 = 1714175) B1714175
theorem B1143899 : Blo 507795 1143899 := bstep (se 1 (by rfl) ⟨857924, by rfl⟩ : syracuseStep 1143899 = 1715849) B1715849
theorem B761855 : Blo 507795 761855 := bstep (se 1 (by rfl) ⟨571391, by rfl⟩ : syracuseStep 761855 = 1142783) B1142783
theorem B762599 : Blo 507795 762599 := bstep (se 1 (by rfl) ⟨571949, by rfl⟩ : syracuseStep 762599 = 1143899) B1143899
theorem B507903 : Blo 507795 507903 := bstep (se 1 (by rfl) ⟨380927, by rfl⟩ : syracuseStep 507903 = 761855) B761855
theorem B508399 : Blo 507795 508399 := bstep (se 1 (by rfl) ⟨381299, by rfl⟩ : syracuseStep 508399 = 762599) B762599

theorem C0 (j : ℕ) (h1 : 126948 ≤ j) (h2 : j ≤ 127647) : Blo 507795 (4 * j + 3) := by
  interval_cases j
  · exact B507795
  · exact B507799
  · exact B507803
  · exact B507807
  · exact B507811
  · exact B507815
  · exact B507819
  · exact B507823
  · exact B507827
  · exact B507831
  · exact B507835
  · exact B507839
  · exact B507843
  · exact B507847
  · exact B507851
  · exact B507855
  · exact B507859
  · exact B507863
  · exact B507867
  · exact B507871
  · exact B507875
  · exact B507879
  · exact B507883
  · exact B507887
  · exact B507891
  · exact B507895
  · exact B507899
  · exact B507903
  · exact B507907
  · exact B507911
  · exact B507915
  · exact B507919
  · exact B507923
  · exact B507927
  · exact B507931
  · exact B507935
  · exact B507939
  · exact B507943
  · exact B507947
  · exact B507951
  · exact B507955
  · exact B507959
  · exact B507963
  · exact B507967
  · exact B507971
  · exact B507975
  · exact B507979
  · exact B507983
  · exact B507987
  · exact B507991
  · exact B507995
  · exact B507999
  · exact B508003
  · exact B508007
  · exact B508011
  · exact B508015
  · exact B508019
  · exact B508023
  · exact B508027
  · exact B508031
  · exact B508035
  · exact B508039
  · exact B508043
  · exact B508047
  · exact B508051
  · exact B508055
  · exact B508059
  · exact B508063
  · exact B508067
  · exact B508071
  · exact B508075
  · exact B508079
  · exact B508083
  · exact B508087
  · exact B508091
  · exact B508095
  · exact B508099
  · exact B508103
  · exact B508107
  · exact B508111
  · exact B508115
  · exact B508119
  · exact B508123
  · exact B508127
  · exact B508131
  · exact B508135
  · exact B508139
  · exact B508143
  · exact B508147
  · exact B508151
  · exact B508155
  · exact B508159
  · exact B508163
  · exact B508167
  · exact B508171
  · exact B508175
  · exact B508179
  · exact B508183
  · exact B508187
  · exact B508191
  · exact B508195
  · exact B508199
  · exact B508203
  · exact B508207
  · exact B508211
  · exact B508215
  · exact B508219
  · exact B508223
  · exact B508227
  · exact B508231
  · exact B508235
  · exact B508239
  · exact B508243
  · exact B508247
  · exact B508251
  · exact B508255
  · exact B508259
  · exact B508263
  · exact B508267
  · exact B508271
  · exact B508275
  · exact B508279
  · exact B508283
  · exact B508287
  · exact B508291
  · exact B508295
  · exact B508299
  · exact B508303
  · exact B508307
  · exact B508311
  · exact B508315
  · exact B508319
  · exact B508323
  · exact B508327
  · exact B508331
  · exact B508335
  · exact B508339
  · exact B508343
  · exact B508347
  · exact B508351
  · exact B508355
  · exact B508359
  · exact B508363
  · exact B508367
  · exact B508371
  · exact B508375
  · exact B508379
  · exact B508383
  · exact B508387
  · exact B508391
  · exact B508395
  · exact B508399
  · exact B508403
  · exact B508407
  · exact B508411
  · exact B508415
  · exact B508419
  · exact B508423
  · exact B508427
  · exact B508431
  · exact B508435
  · exact B508439
  · exact B508443
  · exact B508447
  · exact B508451
  · exact B508455
  · exact B508459
  · exact B508463
  · exact B508467
  · exact B508471
  · exact B508475
  · exact B508479
  · exact B508483
  · exact B508487
  · exact B508491
  · exact B508495
  · exact B508499
  · exact B508503
  · exact B508507
  · exact B508511
  · exact B508515
  · exact B508519
  · exact B508523
  · exact B508527
  · exact B508531
  · exact B508535
  · exact B508539
  · exact B508543
  · exact B508547
  · exact B508551
  · exact B508555
  · exact B508559
  · exact B508563
  · exact B508567
  · exact B508571
  · exact B508575
  · exact B508579
  · exact B508583
  · exact B508587
  · exact B508591
  · exact B508595
  · exact B508599
  · exact B508603
  · exact B508607
  · exact B508611
  · exact B508615
  · exact B508619
  · exact B508623
  · exact B508627
  · exact B508631
  · exact B508635
  · exact B508639
  · exact B508643
  · exact B508647
  · exact B508651
  · exact B508655
  · exact B508659
  · exact B508663
  · exact B508667
  · exact B508671
  · exact B508675
  · exact B508679
  · exact B508683
  · exact B508687
  · exact B508691
  · exact B508695
  · exact B508699
  · exact B508703
  · exact B508707
  · exact B508711
  · exact B508715
  · exact B508719
  · exact B508723
  · exact B508727
  · exact B508731
  · exact B508735
  · exact B508739
  · exact B508743
  · exact B508747
  · exact B508751
  · exact B508755
  · exact B508759
  · exact B508763
  · exact B508767
  · exact B508771
  · exact B508775
  · exact B508779
  · exact B508783
  · exact B508787
  · exact B508791
  · exact B508795
  · exact B508799
  · exact B508803
  · exact B508807
  · exact B508811
  · exact B508815
  · exact B508819
  · exact B508823
  · exact B508827
  · exact B508831
  · exact B508835
  · exact B508839
  · exact B508843
  · exact B508847
  · exact B508851
  · exact B508855
  · exact B508859
  · exact B508863
  · exact B508867
  · exact B508871
  · exact B508875
  · exact B508879
  · exact B508883
  · exact B508887
  · exact B508891
  · exact B508895
  · exact B508899
  · exact B508903
  · exact B508907
  · exact B508911
  · exact B508915
  · exact B508919
  · exact B508923
  · exact B508927
  · exact B508931
  · exact B508935
  · exact B508939
  · exact B508943
  · exact B508947
  · exact B508951
  · exact B508955
  · exact B508959
  · exact B508963
  · exact B508967
  · exact B508971
  · exact B508975
  · exact B508979
  · exact B508983
  · exact B508987
  · exact B508991
  · exact B508995
  · exact B508999
  · exact B509003
  · exact B509007
  · exact B509011
  · exact B509015
  · exact B509019
  · exact B509023
  · exact B509027
  · exact B509031
  · exact B509035
  · exact B509039
  · exact B509043
  · exact B509047
  · exact B509051
  · exact B509055
  · exact B509059
  · exact B509063
  · exact B509067
  · exact B509071
  · exact B509075
  · exact B509079
  · exact B509083
  · exact B509087
  · exact B509091
  · exact B509095
  · exact B509099
  · exact B509103
  · exact B509107
  · exact B509111
  · exact B509115
  · exact B509119
  · exact B509123
  · exact B509127
  · exact B509131
  · exact B509135
  · exact B509139
  · exact B509143
  · exact B509147
  · exact B509151
  · exact B509155
  · exact B509159
  · exact B509163
  · exact B509167
  · exact B509171
  · exact B509175
  · exact B509179
  · exact B509183
  · exact B509187
  · exact B509191
  · exact B509195
  · exact B509199
  · exact B509203
  · exact B509207
  · exact B509211
  · exact B509215
  · exact B509219
  · exact B509223
  · exact B509227
  · exact B509231
  · exact B509235
  · exact B509239
  · exact B509243
  · exact B509247
  · exact B509251
  · exact B509255
  · exact B509259
  · exact B509263
  · exact B509267
  · exact B509271
  · exact B509275
  · exact B509279
  · exact B509283
  · exact B509287
  · exact B509291
  · exact B509295
  · exact B509299
  · exact B509303
  · exact B509307
  · exact B509311
  · exact B509315
  · exact B509319
  · exact B509323
  · exact B509327
  · exact B509331
  · exact B509335
  · exact B509339
  · exact B509343
  · exact B509347
  · exact B509351
  · exact B509355
  · exact B509359
  · exact B509363
  · exact B509367
  · exact B509371
  · exact B509375
  · exact B509379
  · exact B509383
  · exact B509387
  · exact B509391
  · exact B509395
  · exact B509399
  · exact B509403
  · exact B509407
  · exact B509411
  · exact B509415
  · exact B509419
  · exact B509423
  · exact B509427
  · exact B509431
  · exact B509435
  · exact B509439
  · exact B509443
  · exact B509447
  · exact B509451
  · exact B509455
  · exact B509459
  · exact B509463
  · exact B509467
  · exact B509471
  · exact B509475
  · exact B509479
  · exact B509483
  · exact B509487
  · exact B509491
  · exact B509495
  · exact B509499
  · exact B509503
  · exact B509507
  · exact B509511
  · exact B509515
  · exact B509519
  · exact B509523
  · exact B509527
  · exact B509531
  · exact B509535
  · exact B509539
  · exact B509543
  · exact B509547
  · exact B509551
  · exact B509555
  · exact B509559
  · exact B509563
  · exact B509567
  · exact B509571
  · exact B509575
  · exact B509579
  · exact B509583
  · exact B509587
  · exact B509591
  · exact B509595
  · exact B509599
  · exact B509603
  · exact B509607
  · exact B509611
  · exact B509615
  · exact B509619
  · exact B509623
  · exact B509627
  · exact B509631
  · exact B509635
  · exact B509639
  · exact B509643
  · exact B509647
  · exact B509651
  · exact B509655
  · exact B509659
  · exact B509663
  · exact B509667
  · exact B509671
  · exact B509675
  · exact B509679
  · exact B509683
  · exact B509687
  · exact B509691
  · exact B509695
  · exact B509699
  · exact B509703
  · exact B509707
  · exact B509711
  · exact B509715
  · exact B509719
  · exact B509723
  · exact B509727
  · exact B509731
  · exact B509735
  · exact B509739
  · exact B509743
  · exact B509747
  · exact B509751
  · exact B509755
  · exact B509759
  · exact B509763
  · exact B509767
  · exact B509771
  · exact B509775
  · exact B509779
  · exact B509783
  · exact B509787
  · exact B509791
  · exact B509795
  · exact B509799
  · exact B509803
  · exact B509807
  · exact B509811
  · exact B509815
  · exact B509819
  · exact B509823
  · exact B509827
  · exact B509831
  · exact B509835
  · exact B509839
  · exact B509843
  · exact B509847
  · exact B509851
  · exact B509855
  · exact B509859
  · exact B509863
  · exact B509867
  · exact B509871
  · exact B509875
  · exact B509879
  · exact B509883
  · exact B509887
  · exact B509891
  · exact B509895
  · exact B509899
  · exact B509903
  · exact B509907
  · exact B509911
  · exact B509915
  · exact B509919
  · exact B509923
  · exact B509927
  · exact B509931
  · exact B509935
  · exact B509939
  · exact B509943
  · exact B509947
  · exact B509951
  · exact B509955
  · exact B509959
  · exact B509963
  · exact B509967
  · exact B509971
  · exact B509975
  · exact B509979
  · exact B509983
  · exact B509987
  · exact B509991
  · exact B509995
  · exact B509999
  · exact B510003
  · exact B510007
  · exact B510011
  · exact B510015
  · exact B510019
  · exact B510023
  · exact B510027
  · exact B510031
  · exact B510035
  · exact B510039
  · exact B510043
  · exact B510047
  · exact B510051
  · exact B510055
  · exact B510059
  · exact B510063
  · exact B510067
  · exact B510071
  · exact B510075
  · exact B510079
  · exact B510083
  · exact B510087
  · exact B510091
  · exact B510095
  · exact B510099
  · exact B510103
  · exact B510107
  · exact B510111
  · exact B510115
  · exact B510119
  · exact B510123
  · exact B510127
  · exact B510131
  · exact B510135
  · exact B510139
  · exact B510143
  · exact B510147
  · exact B510151
  · exact B510155
  · exact B510159
  · exact B510163
  · exact B510167
  · exact B510171
  · exact B510175
  · exact B510179
  · exact B510183
  · exact B510187
  · exact B510191
  · exact B510195
  · exact B510199
  · exact B510203
  · exact B510207
  · exact B510211
  · exact B510215
  · exact B510219
  · exact B510223
  · exact B510227
  · exact B510231
  · exact B510235
  · exact B510239
  · exact B510243
  · exact B510247
  · exact B510251
  · exact B510255
  · exact B510259
  · exact B510263
  · exact B510267
  · exact B510271
  · exact B510275
  · exact B510279
  · exact B510283
  · exact B510287
  · exact B510291
  · exact B510295
  · exact B510299
  · exact B510303
  · exact B510307
  · exact B510311
  · exact B510315
  · exact B510319
  · exact B510323
  · exact B510327
  · exact B510331
  · exact B510335
  · exact B510339
  · exact B510343
  · exact B510347
  · exact B510351
  · exact B510355
  · exact B510359
  · exact B510363
  · exact B510367
  · exact B510371
  · exact B510375
  · exact B510379
  · exact B510383
  · exact B510387
  · exact B510391
  · exact B510395
  · exact B510399
  · exact B510403
  · exact B510407
  · exact B510411
  · exact B510415
  · exact B510419
  · exact B510423
  · exact B510427
  · exact B510431
  · exact B510435
  · exact B510439
  · exact B510443
  · exact B510447
  · exact B510451
  · exact B510455
  · exact B510459
  · exact B510463
  · exact B510467
  · exact B510471
  · exact B510475
  · exact B510479
  · exact B510483
  · exact B510487
  · exact B510491
  · exact B510495
  · exact B510499
  · exact B510503
  · exact B510507
  · exact B510511
  · exact B510515
  · exact B510519
  · exact B510523
  · exact B510527
  · exact B510531
  · exact B510535
  · exact B510539
  · exact B510543
  · exact B510547
  · exact B510551
  · exact B510555
  · exact B510559
  · exact B510563
  · exact B510567
  · exact B510571
  · exact B510575
  · exact B510579
  · exact B510583
  · exact B510587
  · exact B510591

theorem C1 (j : ℕ) (h1 : 127648 ≤ j) (h2 : j ≤ 127948) : Blo 507795 (4 * j + 3) := by
  interval_cases j
  · exact B510595
  · exact B510599
  · exact B510603
  · exact B510607
  · exact B510611
  · exact B510615
  · exact B510619
  · exact B510623
  · exact B510627
  · exact B510631
  · exact B510635
  · exact B510639
  · exact B510643
  · exact B510647
  · exact B510651
  · exact B510655
  · exact B510659
  · exact B510663
  · exact B510667
  · exact B510671
  · exact B510675
  · exact B510679
  · exact B510683
  · exact B510687
  · exact B510691
  · exact B510695
  · exact B510699
  · exact B510703
  · exact B510707
  · exact B510711
  · exact B510715
  · exact B510719
  · exact B510723
  · exact B510727
  · exact B510731
  · exact B510735
  · exact B510739
  · exact B510743
  · exact B510747
  · exact B510751
  · exact B510755
  · exact B510759
  · exact B510763
  · exact B510767
  · exact B510771
  · exact B510775
  · exact B510779
  · exact B510783
  · exact B510787
  · exact B510791
  · exact B510795
  · exact B510799
  · exact B510803
  · exact B510807
  · exact B510811
  · exact B510815
  · exact B510819
  · exact B510823
  · exact B510827
  · exact B510831
  · exact B510835
  · exact B510839
  · exact B510843
  · exact B510847
  · exact B510851
  · exact B510855
  · exact B510859
  · exact B510863
  · exact B510867
  · exact B510871
  · exact B510875
  · exact B510879
  · exact B510883
  · exact B510887
  · exact B510891
  · exact B510895
  · exact B510899
  · exact B510903
  · exact B510907
  · exact B510911
  · exact B510915
  · exact B510919
  · exact B510923
  · exact B510927
  · exact B510931
  · exact B510935
  · exact B510939
  · exact B510943
  · exact B510947
  · exact B510951
  · exact B510955
  · exact B510959
  · exact B510963
  · exact B510967
  · exact B510971
  · exact B510975
  · exact B510979
  · exact B510983
  · exact B510987
  · exact B510991
  · exact B510995
  · exact B510999
  · exact B511003
  · exact B511007
  · exact B511011
  · exact B511015
  · exact B511019
  · exact B511023
  · exact B511027
  · exact B511031
  · exact B511035
  · exact B511039
  · exact B511043
  · exact B511047
  · exact B511051
  · exact B511055
  · exact B511059
  · exact B511063
  · exact B511067
  · exact B511071
  · exact B511075
  · exact B511079
  · exact B511083
  · exact B511087
  · exact B511091
  · exact B511095
  · exact B511099
  · exact B511103
  · exact B511107
  · exact B511111
  · exact B511115
  · exact B511119
  · exact B511123
  · exact B511127
  · exact B511131
  · exact B511135
  · exact B511139
  · exact B511143
  · exact B511147
  · exact B511151
  · exact B511155
  · exact B511159
  · exact B511163
  · exact B511167
  · exact B511171
  · exact B511175
  · exact B511179
  · exact B511183
  · exact B511187
  · exact B511191
  · exact B511195
  · exact B511199
  · exact B511203
  · exact B511207
  · exact B511211
  · exact B511215
  · exact B511219
  · exact B511223
  · exact B511227
  · exact B511231
  · exact B511235
  · exact B511239
  · exact B511243
  · exact B511247
  · exact B511251
  · exact B511255
  · exact B511259
  · exact B511263
  · exact B511267
  · exact B511271
  · exact B511275
  · exact B511279
  · exact B511283
  · exact B511287
  · exact B511291
  · exact B511295
  · exact B511299
  · exact B511303
  · exact B511307
  · exact B511311
  · exact B511315
  · exact B511319
  · exact B511323
  · exact B511327
  · exact B511331
  · exact B511335
  · exact B511339
  · exact B511343
  · exact B511347
  · exact B511351
  · exact B511355
  · exact B511359
  · exact B511363
  · exact B511367
  · exact B511371
  · exact B511375
  · exact B511379
  · exact B511383
  · exact B511387
  · exact B511391
  · exact B511395
  · exact B511399
  · exact B511403
  · exact B511407
  · exact B511411
  · exact B511415
  · exact B511419
  · exact B511423
  · exact B511427
  · exact B511431
  · exact B511435
  · exact B511439
  · exact B511443
  · exact B511447
  · exact B511451
  · exact B511455
  · exact B511459
  · exact B511463
  · exact B511467
  · exact B511471
  · exact B511475
  · exact B511479
  · exact B511483
  · exact B511487
  · exact B511491
  · exact B511495
  · exact B511499
  · exact B511503
  · exact B511507
  · exact B511511
  · exact B511515
  · exact B511519
  · exact B511523
  · exact B511527
  · exact B511531
  · exact B511535
  · exact B511539
  · exact B511543
  · exact B511547
  · exact B511551
  · exact B511555
  · exact B511559
  · exact B511563
  · exact B511567
  · exact B511571
  · exact B511575
  · exact B511579
  · exact B511583
  · exact B511587
  · exact B511591
  · exact B511595
  · exact B511599
  · exact B511603
  · exact B511607
  · exact B511611
  · exact B511615
  · exact B511619
  · exact B511623
  · exact B511627
  · exact B511631
  · exact B511635
  · exact B511639
  · exact B511643
  · exact B511647
  · exact B511651
  · exact B511655
  · exact B511659
  · exact B511663
  · exact B511667
  · exact B511671
  · exact B511675
  · exact B511679
  · exact B511683
  · exact B511687
  · exact B511691
  · exact B511695
  · exact B511699
  · exact B511703
  · exact B511707
  · exact B511711
  · exact B511715
  · exact B511719
  · exact B511723
  · exact B511727
  · exact B511731
  · exact B511735
  · exact B511739
  · exact B511743
  · exact B511747
  · exact B511751
  · exact B511755
  · exact B511759
  · exact B511763
  · exact B511767
  · exact B511771
  · exact B511775
  · exact B511779
  · exact B511783
  · exact B511787
  · exact B511791
  · exact B511795

theorem solution (m : ℕ) (hlo : 507795 ≤ m) (hhi : m ≤ 511795) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 126948 ≤ j := by omega
    have hj2 : j ≤ 127948 := by omega
    have hb : Blo 507795 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 127648 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
