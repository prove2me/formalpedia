-- Prove2me | solution 1 for syracuse_descends_range_1368503_1370503
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:40:10.510291+00:00
-- url     : https://prove2.me/submissions/835a1ed9-5cef-4e65-ac61-874ed42c873a

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


theorem B4620293 : Blo 1368503 4620293 := bbase (se 4 (by rfl) ⟨433152, by rfl⟩ : syracuseStep 4620293 = 866305) (by norm_num)
theorem B3080213 : Blo 1368503 3080213 := bbase (se 6 (by rfl) ⟨72192, by rfl⟩ : syracuseStep 3080213 = 144385) (by norm_num)
theorem B1540129 : Blo 1368503 1540129 := bbase (se 2 (by rfl) ⟨577548, by rfl⟩ : syracuseStep 1540129 = 1155097) (by norm_num)
theorem B2080837 : Blo 1368503 2080837 := bbase (se 4 (by rfl) ⟨195078, by rfl⟩ : syracuseStep 2080837 = 390157) (by norm_num)
theorem B1540165 : Blo 1368503 1540165 := bbase (se 4 (by rfl) ⟨144390, by rfl⟩ : syracuseStep 1540165 = 288781) (by norm_num)
theorem B2744389 : Blo 1368503 2744389 := bbase (se 4 (by rfl) ⟨257286, by rfl⟩ : syracuseStep 2744389 = 514573) (by norm_num)
theorem B2310221 : Blo 1368503 2310221 := bbase (se 3 (by rfl) ⟨433166, by rfl⟩ : syracuseStep 2310221 = 866333) (by norm_num)
theorem B3465301 : Blo 1368503 3465301 := bbase (se 8 (by rfl) ⟨20304, by rfl⟩ : syracuseStep 3465301 = 40609) (by norm_num)
theorem B3080285 : Blo 1368503 3080285 := bbase (se 3 (by rfl) ⟨577553, by rfl⟩ : syracuseStep 3080285 = 1155107) (by norm_num)
theorem B1851493 : Blo 1368503 1851493 := bbase (se 4 (by rfl) ⟨173577, by rfl⟩ : syracuseStep 1851493 = 347155) (by norm_num)
theorem B1540201 : Blo 1368503 1540201 := bbase (se 2 (by rfl) ⟨577575, by rfl⟩ : syracuseStep 1540201 = 1155151) (by norm_num)
theorem B2924669 : Blo 1368503 2924669 := bbase (se 3 (by rfl) ⟨548375, by rfl⟩ : syracuseStep 2924669 = 1096751) (by norm_num)
theorem B5202053 : Blo 1368503 5202053 := bbase (se 4 (by rfl) ⟨487692, by rfl⟩ : syracuseStep 5202053 = 975385) (by norm_num)
theorem B1540237 : Blo 1368503 1540237 := bbase (se 3 (by rfl) ⟨288794, by rfl⟩ : syracuseStep 1540237 = 577589) (by norm_num)
theorem B3080357 : Blo 1368503 3080357 := bbase (se 4 (by rfl) ⟨288783, by rfl⟩ : syracuseStep 3080357 = 577567) (by norm_num)
theorem B1540273 : Blo 1368503 1540273 := bbase (se 2 (by rfl) ⟨577602, by rfl⟩ : syracuseStep 1540273 = 1155205) (by norm_num)
theorem B8331445 : Blo 1368503 8331445 := bbase (se 5 (by rfl) ⟨390536, by rfl⟩ : syracuseStep 8331445 = 781073) (by norm_num)
theorem B3465413 : Blo 1368503 3465413 := bbase (se 4 (by rfl) ⟨324882, by rfl⟩ : syracuseStep 3465413 = 649765) (by norm_num)
theorem B2310349 : Blo 1368503 2310349 := bbase (se 3 (by rfl) ⟨433190, by rfl⟩ : syracuseStep 2310349 = 866381) (by norm_num)
theorem B1540309 : Blo 1368503 1540309 := bbase (se 7 (by rfl) ⟨18050, by rfl⟩ : syracuseStep 1540309 = 36101) (by norm_num)
theorem B3080429 : Blo 1368503 3080429 := bbase (se 3 (by rfl) ⟨577580, by rfl⟩ : syracuseStep 3080429 = 1155161) (by norm_num)
theorem B1949933 : Blo 1368503 1949933 := bbase (se 3 (by rfl) ⟨365612, by rfl⟩ : syracuseStep 1949933 = 731225) (by norm_num)
theorem B1540345 : Blo 1368503 1540345 := bbase (se 2 (by rfl) ⟨577629, by rfl⟩ : syracuseStep 1540345 = 1155259) (by norm_num)
theorem B26665237 : Blo 1368503 26665237 := bbase (se 6 (by rfl) ⟨624966, by rfl⟩ : syracuseStep 26665237 = 1249933) (by norm_num)
theorem B1540381 : Blo 1368503 1540381 := bbase (se 3 (by rfl) ⟨288821, by rfl⟩ : syracuseStep 1540381 = 577643) (by norm_num)
theorem B2310437 : Blo 1368503 2310437 := bbase (se 4 (by rfl) ⟨216603, by rfl⟩ : syracuseStep 2310437 = 433207) (by norm_num)
theorem B3080501 : Blo 1368503 3080501 := bbase (se 5 (by rfl) ⟨144398, by rfl⟩ : syracuseStep 3080501 = 288797) (by norm_num)
theorem B1540417 : Blo 1368503 1540417 := bbase (se 2 (by rfl) ⟨577656, by rfl⟩ : syracuseStep 1540417 = 1155313) (by norm_num)
theorem B1540453 : Blo 1368503 1540453 := bbase (se 4 (by rfl) ⟨144417, by rfl⟩ : syracuseStep 1540453 = 288835) (by norm_num)
theorem B3080573 : Blo 1368503 3080573 := bbase (se 3 (by rfl) ⟨577607, by rfl⟩ : syracuseStep 3080573 = 1155215) (by norm_num)
theorem B3465605 : Blo 1368503 3465605 := bbase (se 4 (by rfl) ⟨324900, by rfl⟩ : syracuseStep 3465605 = 649801) (by norm_num)
theorem B1540489 : Blo 1368503 1540489 := bbase (se 2 (by rfl) ⟨577683, by rfl⟩ : syracuseStep 1540489 = 1155367) (by norm_num)
theorem B2310565 : Blo 1368503 2310565 := bbase (se 4 (by rfl) ⟨216615, by rfl⟩ : syracuseStep 2310565 = 433231) (by norm_num)
theorem B1540525 : Blo 1368503 1540525 := bbase (se 3 (by rfl) ⟨288848, by rfl⟩ : syracuseStep 1540525 = 577697) (by norm_num)
theorem B4620725 : Blo 1368503 4620725 := bbase (se 5 (by rfl) ⟨216596, by rfl⟩ : syracuseStep 4620725 = 433193) (by norm_num)
theorem B3080645 : Blo 1368503 3080645 := bbase (se 4 (by rfl) ⟨288810, by rfl⟩ : syracuseStep 3080645 = 577621) (by norm_num)
theorem B1540561 : Blo 1368503 1540561 := bbase (se 2 (by rfl) ⟨577710, by rfl⟩ : syracuseStep 1540561 = 1155421) (by norm_num)
theorem B1540597 : Blo 1368503 1540597 := bbase (se 5 (by rfl) ⟨72215, by rfl⟩ : syracuseStep 1540597 = 144431) (by norm_num)
theorem B2310653 : Blo 1368503 2310653 := bbase (se 3 (by rfl) ⟨433247, by rfl⟩ : syracuseStep 2310653 = 866495) (by norm_num)
theorem B3080717 : Blo 1368503 3080717 := bbase (se 3 (by rfl) ⟨577634, by rfl⟩ : syracuseStep 3080717 = 1155269) (by norm_num)
theorem B6242837 : Blo 1368503 6242837 := bbase (se 6 (by rfl) ⟨146316, by rfl⟩ : syracuseStep 6242837 = 292633) (by norm_num)
theorem B7029269 : Blo 1368503 7029269 := bbase (se 6 (by rfl) ⟨164748, by rfl⟩ : syracuseStep 7029269 = 329497) (by norm_num)
theorem B1540633 : Blo 1368503 1540633 := bbase (se 2 (by rfl) ⟨577737, by rfl⟩ : syracuseStep 1540633 = 1155475) (by norm_num)
theorem B1540669 : Blo 1368503 1540669 := bbase (se 3 (by rfl) ⟨288875, by rfl⟩ : syracuseStep 1540669 = 577751) (by norm_num)
theorem B3080789 : Blo 1368503 3080789 := bbase (se 8 (by rfl) ⟨18051, by rfl⟩ : syracuseStep 3080789 = 36103) (by norm_num)
theorem B1540705 : Blo 1368503 1540705 := bbase (se 2 (by rfl) ⟨577764, by rfl⟩ : syracuseStep 1540705 = 1155529) (by norm_num)
theorem B2925173 : Blo 1368503 2925173 := bbase (se 5 (by rfl) ⟨137117, by rfl⟩ : syracuseStep 2925173 = 274235) (by norm_num)
theorem B2310781 : Blo 1368503 2310781 := bbase (se 3 (by rfl) ⟨433271, by rfl⟩ : syracuseStep 2310781 = 866543) (by norm_num)
theorem B2925181 : Blo 1368503 2925181 := bbase (se 3 (by rfl) ⟨548471, by rfl⟩ : syracuseStep 2925181 = 1096943) (by norm_num)
theorem B1540741 : Blo 1368503 1540741 := bbase (se 4 (by rfl) ⟨144444, by rfl⟩ : syracuseStep 1540741 = 288889) (by norm_num)
theorem B2777741 : Blo 1368503 2777741 := bbase (se 3 (by rfl) ⟨520826, by rfl⟩ : syracuseStep 2777741 = 1041653) (by norm_num)
theorem B3080861 : Blo 1368503 3080861 := bbase (se 3 (by rfl) ⟨577661, by rfl⟩ : syracuseStep 3080861 = 1155323) (by norm_num)
theorem B1540777 : Blo 1368503 1540777 := bbase (se 2 (by rfl) ⟨577791, by rfl⟩ : syracuseStep 1540777 = 1155583) (by norm_num)
theorem B1540813 : Blo 1368503 1540813 := bbase (se 3 (by rfl) ⟨288902, by rfl⟩ : syracuseStep 1540813 = 577805) (by norm_num)
theorem B2310869 : Blo 1368503 2310869 := bbase (se 7 (by rfl) ⟨27080, by rfl⟩ : syracuseStep 2310869 = 54161) (by norm_num)
theorem B3465949 : Blo 1368503 3465949 := bbase (se 3 (by rfl) ⟨649865, by rfl⟩ : syracuseStep 3465949 = 1299731) (by norm_num)
theorem B3080933 : Blo 1368503 3080933 := bbase (se 4 (by rfl) ⟨288837, by rfl⟩ : syracuseStep 3080933 = 577675) (by norm_num)
theorem B1540849 : Blo 1368503 1540849 := bbase (se 2 (by rfl) ⟨577818, by rfl⟩ : syracuseStep 1540849 = 1155637) (by norm_num)
theorem B1540885 : Blo 1368503 1540885 := bbase (se 6 (by rfl) ⟨36114, by rfl⟩ : syracuseStep 1540885 = 72229) (by norm_num)
theorem B1950485 : Blo 1368503 1950485 := bbase (se 6 (by rfl) ⟨45714, by rfl⟩ : syracuseStep 1950485 = 91429) (by norm_num)
theorem B3081005 : Blo 1368503 3081005 := bbase (se 3 (by rfl) ⟨577688, by rfl⟩ : syracuseStep 3081005 = 1155377) (by norm_num)
theorem B1540921 : Blo 1368503 1540921 := bbase (se 2 (by rfl) ⟨577845, by rfl⟩ : syracuseStep 1540921 = 1155691) (by norm_num)
theorem B3466061 : Blo 1368503 3466061 := bbase (se 3 (by rfl) ⟨649886, by rfl⟩ : syracuseStep 3466061 = 1299773) (by norm_num)
theorem B73089877 : Blo 1368503 73089877 := bbase (se 9 (by rfl) ⟨214130, by rfl⟩ : syracuseStep 73089877 = 428261) (by norm_num)
theorem B2310997 : Blo 1368503 2310997 := bbase (se 9 (by rfl) ⟨6770, by rfl⟩ : syracuseStep 2310997 = 13541) (by norm_num)
theorem B1540957 : Blo 1368503 1540957 := bbase (se 3 (by rfl) ⟨288929, by rfl⟩ : syracuseStep 1540957 = 577859) (by norm_num)
theorem B4621157 : Blo 1368503 4621157 := bbase (se 4 (by rfl) ⟨433233, by rfl⟩ : syracuseStep 4621157 = 866467) (by norm_num)
theorem B3081077 : Blo 1368503 3081077 := bbase (se 5 (by rfl) ⟨144425, by rfl⟩ : syracuseStep 3081077 = 288851) (by norm_num)
theorem B11707253 : Blo 1368503 11707253 := bbase (se 5 (by rfl) ⟨548777, by rfl⟩ : syracuseStep 11707253 = 1097555) (by norm_num)
theorem B1540993 : Blo 1368503 1540993 := bbase (se 2 (by rfl) ⟨577872, by rfl⟩ : syracuseStep 1540993 = 1155745) (by norm_num)
theorem B2343829 : Blo 1368503 2343829 := bbase (se 6 (by rfl) ⟨54933, by rfl⟩ : syracuseStep 2343829 = 109867) (by norm_num)
theorem B1541029 : Blo 1368503 1541029 := bbase (se 4 (by rfl) ⟨144471, by rfl⟩ : syracuseStep 1541029 = 288943) (by norm_num)
theorem B2311085 : Blo 1368503 2311085 := bbase (se 3 (by rfl) ⟨433328, by rfl⟩ : syracuseStep 2311085 = 866657) (by norm_num)
theorem B3081149 : Blo 1368503 3081149 := bbase (se 3 (by rfl) ⟨577715, by rfl⟩ : syracuseStep 3081149 = 1155431) (by norm_num)
theorem B1541065 : Blo 1368503 1541065 := bbase (se 2 (by rfl) ⟨577899, by rfl⟩ : syracuseStep 1541065 = 1155799) (by norm_num)
theorem B1541101 : Blo 1368503 1541101 := bbase (se 3 (by rfl) ⟨288956, by rfl⟩ : syracuseStep 1541101 = 577913) (by norm_num)
theorem B3081221 : Blo 1368503 3081221 := bbase (se 4 (by rfl) ⟨288864, by rfl⟩ : syracuseStep 3081221 = 577729) (by norm_num)
theorem B3466253 : Blo 1368503 3466253 := bbase (se 3 (by rfl) ⟨649922, by rfl⟩ : syracuseStep 3466253 = 1299845) (by norm_num)
theorem B1541137 : Blo 1368503 1541137 := bbase (se 2 (by rfl) ⟨577926, by rfl⟩ : syracuseStep 1541137 = 1155853) (by norm_num)
theorem B6931493 : Blo 1368503 6931493 := bbase (se 4 (by rfl) ⟨649827, by rfl⟩ : syracuseStep 6931493 = 1299655) (by norm_num)
theorem B2311213 : Blo 1368503 2311213 := bbase (se 3 (by rfl) ⟨433352, by rfl⟩ : syracuseStep 2311213 = 866705) (by norm_num)
theorem B3900469 : Blo 1368503 3900469 := bbase (se 5 (by rfl) ⟨182834, by rfl⟩ : syracuseStep 3900469 = 365669) (by norm_num)
theorem B1541173 : Blo 1368503 1541173 := bbase (se 5 (by rfl) ⟨72242, by rfl⟩ : syracuseStep 1541173 = 144485) (by norm_num)
theorem B3081293 : Blo 1368503 3081293 := bbase (se 3 (by rfl) ⟨577742, by rfl⟩ : syracuseStep 3081293 = 1155485) (by norm_num)
theorem B7398485 : Blo 1368503 7398485 := bbase (se 8 (by rfl) ⟨43350, by rfl⟩ : syracuseStep 7398485 = 86701) (by norm_num)
theorem B1541209 : Blo 1368503 1541209 := bbase (se 2 (by rfl) ⟨577953, by rfl⟩ : syracuseStep 1541209 = 1155907) (by norm_num)
theorem B1541245 : Blo 1368503 1541245 := bbase (se 3 (by rfl) ⟨288983, by rfl⟩ : syracuseStep 1541245 = 577967) (by norm_num)
theorem B2311301 : Blo 1368503 2311301 := bbase (se 4 (by rfl) ⟨216684, by rfl⟩ : syracuseStep 2311301 = 433369) (by norm_num)
theorem B3081365 : Blo 1368503 3081365 := bbase (se 6 (by rfl) ⟨72219, by rfl⟩ : syracuseStep 3081365 = 144439) (by norm_num)
theorem B1541281 : Blo 1368503 1541281 := bbase (se 2 (by rfl) ⟨577980, by rfl⟩ : syracuseStep 1541281 = 1155961) (by norm_num)
theorem B6243493 : Blo 1368503 6243493 := bbase (se 4 (by rfl) ⟨585327, by rfl⟩ : syracuseStep 6243493 = 1170655) (by norm_num)
theorem B1541317 : Blo 1368503 1541317 := bbase (se 4 (by rfl) ⟨144498, by rfl⟩ : syracuseStep 1541317 = 288997) (by norm_num)
theorem B3900629 : Blo 1368503 3900629 := bbase (se 7 (by rfl) ⟨45710, by rfl⟩ : syracuseStep 3900629 = 91421) (by norm_num)
theorem B3081437 : Blo 1368503 3081437 := bbase (se 3 (by rfl) ⟨577769, by rfl⟩ : syracuseStep 3081437 = 1155539) (by norm_num)
theorem B2344157 : Blo 1368503 2344157 := bbase (se 3 (by rfl) ⟨439529, by rfl⟩ : syracuseStep 2344157 = 879059) (by norm_num)
theorem B3122405 : Blo 1368503 3122405 := bbase (se 4 (by rfl) ⟨292725, by rfl⟩ : syracuseStep 3122405 = 585451) (by norm_num)
theorem B1541353 : Blo 1368503 1541353 := bbase (se 2 (by rfl) ⟨578007, by rfl⟩ : syracuseStep 1541353 = 1156015) (by norm_num)
theorem B2598149 : Blo 1368503 2598149 := bbase (se 4 (by rfl) ⟨243576, by rfl⟩ : syracuseStep 2598149 = 487153) (by norm_num)
theorem B2311429 : Blo 1368503 2311429 := bbase (se 4 (by rfl) ⟨216696, by rfl⟩ : syracuseStep 2311429 = 433393) (by norm_num)
theorem B1541389 : Blo 1368503 1541389 := bbase (se 3 (by rfl) ⟨289010, by rfl⟩ : syracuseStep 1541389 = 578021) (by norm_num)
theorem B4621589 : Blo 1368503 4621589 := bbase (se 6 (by rfl) ⟨108318, by rfl⟩ : syracuseStep 4621589 = 216637) (by norm_num)
theorem B3081509 : Blo 1368503 3081509 := bbase (se 4 (by rfl) ⟨288891, by rfl⟩ : syracuseStep 3081509 = 577783) (by norm_num)
theorem B5203237 : Blo 1368503 5203237 := bbase (se 4 (by rfl) ⟨487803, by rfl⟩ : syracuseStep 5203237 = 975607) (by norm_num)
theorem B1541425 : Blo 1368503 1541425 := bbase (se 2 (by rfl) ⟨578034, by rfl⟩ : syracuseStep 1541425 = 1156069) (by norm_num)
theorem B2467141 : Blo 1368503 2467141 := bbase (se 4 (by rfl) ⟨231294, by rfl⟩ : syracuseStep 2467141 = 462589) (by norm_num)
theorem B1541461 : Blo 1368503 1541461 := bbase (se 12 (by rfl) ⟨564, by rfl⟩ : syracuseStep 1541461 = 1129) (by norm_num)
theorem B2311517 : Blo 1368503 2311517 := bbase (se 3 (by rfl) ⟨433409, by rfl⟩ : syracuseStep 2311517 = 866819) (by norm_num)
theorem B3466597 : Blo 1368503 3466597 := bbase (se 4 (by rfl) ⟨324993, by rfl⟩ : syracuseStep 3466597 = 649987) (by norm_num)
theorem B3081581 : Blo 1368503 3081581 := bbase (se 3 (by rfl) ⟨577796, by rfl⟩ : syracuseStep 3081581 = 1155593) (by norm_num)
theorem B1541497 : Blo 1368503 1541497 := bbase (se 2 (by rfl) ⟨578061, by rfl⟩ : syracuseStep 1541497 = 1156123) (by norm_num)
theorem B2598293 : Blo 1368503 2598293 := bbase (se 6 (by rfl) ⟨60897, by rfl⟩ : syracuseStep 2598293 = 121795) (by norm_num)
theorem B1541533 : Blo 1368503 1541533 := bbase (se 3 (by rfl) ⟨289037, by rfl⟩ : syracuseStep 1541533 = 578075) (by norm_num)
theorem B3081653 : Blo 1368503 3081653 := bbase (se 5 (by rfl) ⟨144452, by rfl⟩ : syracuseStep 3081653 = 288905) (by norm_num)
theorem B1541569 : Blo 1368503 1541569 := bbase (se 2 (by rfl) ⟨578088, by rfl⟩ : syracuseStep 1541569 = 1156177) (by norm_num)
theorem B3900869 : Blo 1368503 3900869 := bbase (se 4 (by rfl) ⟨365706, by rfl⟩ : syracuseStep 3900869 = 731413) (by norm_num)
theorem B3466709 : Blo 1368503 3466709 := bbase (se 7 (by rfl) ⟨40625, by rfl⟩ : syracuseStep 3466709 = 81251) (by norm_num)
theorem B2311645 : Blo 1368503 2311645 := bbase (se 3 (by rfl) ⟨433433, by rfl⟩ : syracuseStep 2311645 = 866867) (by norm_num)
theorem B1541605 : Blo 1368503 1541605 := bbase (se 4 (by rfl) ⟨144525, by rfl⟩ : syracuseStep 1541605 = 289051) (by norm_num)
theorem B3081725 : Blo 1368503 3081725 := bbase (se 3 (by rfl) ⟨577823, by rfl⟩ : syracuseStep 3081725 = 1155647) (by norm_num)
theorem B1541641 : Blo 1368503 1541641 := bbase (se 2 (by rfl) ⟨578115, by rfl⟩ : syracuseStep 1541641 = 1156231) (by norm_num)
theorem B1951237 : Blo 1368503 1951237 := bbase (se 4 (by rfl) ⟨182928, by rfl⟩ : syracuseStep 1951237 = 365857) (by norm_num)
theorem B1541677 : Blo 1368503 1541677 := bbase (se 3 (by rfl) ⟨289064, by rfl⟩ : syracuseStep 1541677 = 578129) (by norm_num)
theorem B2311733 : Blo 1368503 2311733 := bbase (se 5 (by rfl) ⟨108362, by rfl⟩ : syracuseStep 2311733 = 216725) (by norm_num)
theorem B3081797 : Blo 1368503 3081797 := bbase (se 4 (by rfl) ⟨288918, by rfl⟩ : syracuseStep 3081797 = 577837) (by norm_num)
theorem B1541713 : Blo 1368503 1541713 := bbase (se 2 (by rfl) ⟨578142, by rfl⟩ : syracuseStep 1541713 = 1156285) (by norm_num)
theorem B5203541 : Blo 1368503 5203541 := bbase (se 8 (by rfl) ⟨30489, by rfl⟩ : syracuseStep 5203541 = 60979) (by norm_num)
theorem B2672237 : Blo 1368503 2672237 := bbase (se 3 (by rfl) ⟨501044, by rfl⟩ : syracuseStep 2672237 = 1002089) (by norm_num)
theorem B1541749 : Blo 1368503 1541749 := bbase (se 5 (by rfl) ⟨72269, by rfl⟩ : syracuseStep 1541749 = 144539) (by norm_num)
theorem B3901061 : Blo 1368503 3901061 := bbase (se 4 (by rfl) ⟨365724, by rfl⟩ : syracuseStep 3901061 = 731449) (by norm_num)
theorem B3081869 : Blo 1368503 3081869 := bbase (se 3 (by rfl) ⟨577850, by rfl⟩ : syracuseStep 3081869 = 1155701) (by norm_num)
theorem B3466901 : Blo 1368503 3466901 := bbase (se 6 (by rfl) ⟨81255, by rfl⟩ : syracuseStep 3466901 = 162511) (by norm_num)
theorem B1541785 : Blo 1368503 1541785 := bbase (se 2 (by rfl) ⟨578169, by rfl⟩ : syracuseStep 1541785 = 1156339) (by norm_num)
theorem B2598581 : Blo 1368503 2598581 := bbase (se 5 (by rfl) ⟨121808, by rfl⟩ : syracuseStep 2598581 = 243617) (by norm_num)
theorem B2311861 : Blo 1368503 2311861 := bbase (se 5 (by rfl) ⟨108368, by rfl⟩ : syracuseStep 2311861 = 216737) (by norm_num)
theorem B4622021 : Blo 1368503 4622021 := bbase (se 4 (by rfl) ⟨433314, by rfl⟩ : syracuseStep 4622021 = 866629) (by norm_num)
theorem B3081941 : Blo 1368503 3081941 := bbase (se 7 (by rfl) ⟨36116, by rfl⟩ : syracuseStep 3081941 = 72233) (by norm_num)
theorem B4933349 : Blo 1368503 4933349 := bbase (se 4 (by rfl) ⟨462501, by rfl⟩ : syracuseStep 4933349 = 925003) (by norm_num)
theorem B2926309 : Blo 1368503 2926309 := bbase (se 4 (by rfl) ⟨274341, by rfl⟩ : syracuseStep 2926309 = 548683) (by norm_num)
theorem B2467597 : Blo 1368503 2467597 := bbase (se 3 (by rfl) ⟨462674, by rfl⟩ : syracuseStep 2467597 = 925349) (by norm_num)
theorem B2311949 : Blo 1368503 2311949 := bbase (se 3 (by rfl) ⟨433490, by rfl⟩ : syracuseStep 2311949 = 866981) (by norm_num)
theorem B3082013 : Blo 1368503 3082013 := bbase (se 3 (by rfl) ⟨577877, by rfl⟩ : syracuseStep 3082013 = 1155755) (by norm_num)
theorem B2598733 : Blo 1368503 2598733 := bbase (se 3 (by rfl) ⟨487262, by rfl⟩ : syracuseStep 2598733 = 974525) (by norm_num)
theorem B8898389 : Blo 1368503 8898389 := bbase (se 9 (by rfl) ⟨26069, by rfl⟩ : syracuseStep 8898389 = 52139) (by norm_num)
theorem B3082085 : Blo 1368503 3082085 := bbase (se 4 (by rfl) ⟨288945, by rfl⟩ : syracuseStep 3082085 = 577891) (by norm_num)
theorem B2312077 : Blo 1368503 2312077 := bbase (se 3 (by rfl) ⟨433514, by rfl⟩ : syracuseStep 2312077 = 867029) (by norm_num)
theorem B5851045 : Blo 1368503 5851045 := bbase (se 4 (by rfl) ⟨548535, by rfl⟩ : syracuseStep 5851045 = 1097071) (by norm_num)
theorem B3082157 : Blo 1368503 3082157 := bbase (se 3 (by rfl) ⟨577904, by rfl⟩ : syracuseStep 3082157 = 1155809) (by norm_num)
theorem B3123125 : Blo 1368503 3123125 := bbase (se 5 (by rfl) ⟨146396, by rfl⟩ : syracuseStep 3123125 = 292793) (by norm_num)
theorem B4163525 : Blo 1368503 4163525 := bbase (se 4 (by rfl) ⟨390330, by rfl⟩ : syracuseStep 4163525 = 780661) (by norm_num)
theorem B2312165 : Blo 1368503 2312165 := bbase (se 4 (by rfl) ⟨216765, by rfl⟩ : syracuseStep 2312165 = 433531) (by norm_num)
theorem B3467245 : Blo 1368503 3467245 := bbase (se 3 (by rfl) ⟨650108, by rfl⟩ : syracuseStep 3467245 = 1300217) (by norm_num)
theorem B3082229 : Blo 1368503 3082229 := bbase (se 5 (by rfl) ⟨144479, by rfl⟩ : syracuseStep 3082229 = 288959) (by norm_num)
theorem B3082301 : Blo 1368503 3082301 := bbase (se 3 (by rfl) ⟨577931, by rfl⟩ : syracuseStep 3082301 = 1155863) (by norm_num)
theorem B2500685 : Blo 1368503 2500685 := bbase (se 3 (by rfl) ⟨468878, by rfl⟩ : syracuseStep 2500685 = 937757) (by norm_num)
theorem B3467357 : Blo 1368503 3467357 := bbase (se 3 (by rfl) ⟨650129, by rfl⟩ : syracuseStep 3467357 = 1300259) (by norm_num)
theorem B2926685 : Blo 1368503 2926685 := bbase (se 3 (by rfl) ⟨548753, by rfl⟩ : syracuseStep 2926685 = 1097507) (by norm_num)
theorem B2312293 : Blo 1368503 2312293 := bbase (se 4 (by rfl) ⟨216777, by rfl⟩ : syracuseStep 2312293 = 433555) (by norm_num)
theorem B4622453 : Blo 1368503 4622453 := bbase (se 5 (by rfl) ⟨216677, by rfl⟩ : syracuseStep 4622453 = 433355) (by norm_num)
theorem B2599037 : Blo 1368503 2599037 := bbase (se 3 (by rfl) ⟨487319, by rfl⟩ : syracuseStep 2599037 = 974639) (by norm_num)
theorem B4384901 : Blo 1368503 4384901 := bbase (se 4 (by rfl) ⟨411084, by rfl⟩ : syracuseStep 4384901 = 822169) (by norm_num)
theorem B3082373 : Blo 1368503 3082373 := bbase (se 4 (by rfl) ⟨288972, by rfl⟩ : syracuseStep 3082373 = 577945) (by norm_num)
theorem B2312381 : Blo 1368503 2312381 := bbase (se 3 (by rfl) ⟨433571, by rfl⟩ : syracuseStep 2312381 = 867143) (by norm_num)
theorem B3082445 : Blo 1368503 3082445 := bbase (se 3 (by rfl) ⟨577958, by rfl⟩ : syracuseStep 3082445 = 1155917) (by norm_num)
theorem B1583317 : Blo 1368503 1583317 := bbase (se 7 (by rfl) ⟨18554, by rfl⟩ : syracuseStep 1583317 = 37109) (by norm_num)
theorem B3082517 : Blo 1368503 3082517 := bbase (se 6 (by rfl) ⟨72246, by rfl⟩ : syracuseStep 3082517 = 144493) (by norm_num)
theorem B3467549 : Blo 1368503 3467549 := bbase (se 3 (by rfl) ⟨650165, by rfl⟩ : syracuseStep 3467549 = 1300331) (by norm_num)
theorem B6932789 : Blo 1368503 6932789 := bbase (se 5 (by rfl) ⟨324974, by rfl⟩ : syracuseStep 6932789 = 649949) (by norm_num)
theorem B2312509 : Blo 1368503 2312509 := bbase (se 3 (by rfl) ⟨433595, by rfl⟩ : syracuseStep 2312509 = 867191) (by norm_num)
theorem B3082589 : Blo 1368503 3082589 := bbase (se 3 (by rfl) ⟨577985, by rfl⟩ : syracuseStep 3082589 = 1155971) (by norm_num)
theorem B2312597 : Blo 1368503 2312597 := bbase (se 6 (by rfl) ⟨54201, by rfl⟩ : syracuseStep 2312597 = 108403) (by norm_num)
theorem B3082661 : Blo 1368503 3082661 := bbase (se 4 (by rfl) ⟨288999, by rfl⟩ : syracuseStep 3082661 = 577999) (by norm_num)
theorem B3082733 : Blo 1368503 3082733 := bbase (se 3 (by rfl) ⟨578012, by rfl⟩ : syracuseStep 3082733 = 1156025) (by norm_num)
theorem B2083349 : Blo 1368503 2083349 := bbase (se 6 (by rfl) ⟨48828, by rfl⟩ : syracuseStep 2083349 = 97657) (by norm_num)
theorem B2312725 : Blo 1368503 2312725 := bbase (se 6 (by rfl) ⟨54204, by rfl⟩ : syracuseStep 2312725 = 108409) (by norm_num)
theorem B4622885 : Blo 1368503 4622885 := bbase (se 4 (by rfl) ⟨433395, by rfl⟩ : syracuseStep 4622885 = 866791) (by norm_num)
theorem B3082805 : Blo 1368503 3082805 := bbase (se 5 (by rfl) ⟨144506, by rfl⟩ : syracuseStep 3082805 = 289013) (by norm_num)
theorem B3902053 : Blo 1368503 3902053 := bbase (se 4 (by rfl) ⟨365817, by rfl⟩ : syracuseStep 3902053 = 731635) (by norm_num)
theorem B3467893 : Blo 1368503 3467893 := bbase (se 5 (by rfl) ⟨162557, by rfl⟩ : syracuseStep 3467893 = 325115) (by norm_num)
theorem B3082877 : Blo 1368503 3082877 := bbase (se 3 (by rfl) ⟨578039, by rfl⟩ : syracuseStep 3082877 = 1156079) (by norm_num)
theorem B2468525 : Blo 1368503 2468525 := bbase (se 3 (by rfl) ⟨462848, by rfl⟩ : syracuseStep 2468525 = 925697) (by norm_num)
theorem B3082949 : Blo 1368503 3082949 := bbase (se 4 (by rfl) ⟨289026, by rfl⟩ : syracuseStep 3082949 = 578053) (by norm_num)
theorem B3468005 : Blo 1368503 3468005 := bbase (se 4 (by rfl) ⟨325125, by rfl⟩ : syracuseStep 3468005 = 650251) (by norm_num)
theorem B3083021 : Blo 1368503 3083021 := bbase (se 3 (by rfl) ⟨578066, by rfl⟩ : syracuseStep 3083021 = 1156133) (by norm_num)
theorem B1755937 : Blo 1368503 1755937 := bbase (se 2 (by rfl) ⟨658476, by rfl⟩ : syracuseStep 1755937 = 1316953) (by norm_num)
theorem B2468693 : Blo 1368503 2468693 := bbase (se 9 (by rfl) ⟨7232, by rfl⟩ : syracuseStep 2468693 = 14465) (by norm_num)
theorem B3083093 : Blo 1368503 3083093 := bbase (se 9 (by rfl) ⟨9032, by rfl⟩ : syracuseStep 3083093 = 18065) (by norm_num)
theorem B2599789 : Blo 1368503 2599789 := bbase (se 3 (by rfl) ⟨487460, by rfl⟩ : syracuseStep 2599789 = 974921) (by norm_num)
theorem B3083165 : Blo 1368503 3083165 := bbase (se 3 (by rfl) ⟨578093, by rfl⟩ : syracuseStep 3083165 = 1156187) (by norm_num)
theorem B3468197 : Blo 1368503 3468197 := bbase (se 4 (by rfl) ⟨325143, by rfl⟩ : syracuseStep 3468197 = 650287) (by norm_num)
theorem B2812877 : Blo 1368503 2812877 := bbase (se 3 (by rfl) ⟨527414, by rfl⟩ : syracuseStep 2812877 = 1054829) (by norm_num)
theorem B4623317 : Blo 1368503 4623317 := bbase (se 7 (by rfl) ⟨54179, by rfl⟩ : syracuseStep 4623317 = 108359) (by norm_num)
theorem B3083237 : Blo 1368503 3083237 := bbase (se 4 (by rfl) ⟨289053, by rfl⟩ : syracuseStep 3083237 = 578107) (by norm_num)
theorem B2501621 : Blo 1368503 2501621 := bbase (se 5 (by rfl) ⟨117263, by rfl⟩ : syracuseStep 2501621 = 234527) (by norm_num)
theorem B2599933 : Blo 1368503 2599933 := bbase (se 3 (by rfl) ⟨487487, by rfl⟩ : syracuseStep 2599933 = 974975) (by norm_num)
theorem B3083309 : Blo 1368503 3083309 := bbase (se 3 (by rfl) ⟨578120, by rfl⟩ : syracuseStep 3083309 = 1156241) (by norm_num)
theorem B2468981 : Blo 1368503 2468981 := bbase (se 5 (by rfl) ⟨115733, by rfl⟩ : syracuseStep 2468981 = 231467) (by norm_num)
theorem B3083381 : Blo 1368503 3083381 := bbase (se 5 (by rfl) ⟨144533, by rfl⟩ : syracuseStep 3083381 = 289067) (by norm_num)
theorem B2600093 : Blo 1368503 2600093 := bbase (se 3 (by rfl) ⟨487517, by rfl⟩ : syracuseStep 2600093 = 975035) (by norm_num)
theorem B3083453 : Blo 1368503 3083453 := bbase (se 3 (by rfl) ⟨578147, by rfl⟩ : syracuseStep 3083453 = 1156295) (by norm_num)
theorem B1461493 : Blo 1368503 1461493 := bbase (se 5 (by rfl) ⟨68507, by rfl⟩ : syracuseStep 1461493 = 137015) (by norm_num)
theorem B1461497 : Blo 1368503 1461497 := bbase (se 2 (by rfl) ⟨548061, by rfl⟩ : syracuseStep 1461497 = 1096123) (by norm_num)
theorem B3468541 : Blo 1368503 3468541 := bbase (se 3 (by rfl) ⟨650351, by rfl⟩ : syracuseStep 3468541 = 1300703) (by norm_num)
theorem B3083525 : Blo 1368503 3083525 := bbase (se 4 (by rfl) ⟨289080, by rfl⟩ : syracuseStep 3083525 = 578161) (by norm_num)
theorem B2600237 : Blo 1368503 2600237 := bbase (se 3 (by rfl) ⟨487544, by rfl⟩ : syracuseStep 2600237 = 975089) (by norm_num)
theorem B9866549 : Blo 1368503 9866549 := bbase (se 5 (by rfl) ⟨462494, by rfl⟩ : syracuseStep 9866549 = 924989) (by norm_num)
theorem B3083597 : Blo 1368503 3083597 := bbase (se 3 (by rfl) ⟨578174, by rfl⟩ : syracuseStep 3083597 = 1156349) (by norm_num)
theorem B3468653 : Blo 1368503 3468653 := bbase (se 3 (by rfl) ⟨650372, by rfl⟩ : syracuseStep 3468653 = 1300745) (by norm_num)
theorem B5852533 : Blo 1368503 5852533 := bbase (se 5 (by rfl) ⟨274337, by rfl⟩ : syracuseStep 5852533 = 548675) (by norm_num)
theorem B4623749 : Blo 1368503 4623749 := bbase (se 4 (by rfl) ⟨433476, by rfl⟩ : syracuseStep 4623749 = 866953) (by norm_num)
theorem B5852549 : Blo 1368503 5852549 := bbase (se 4 (by rfl) ⟨548676, by rfl⟩ : syracuseStep 5852549 = 1097353) (by norm_num)
theorem B1732033 : Blo 1368503 1732033 := bbase (se 2 (by rfl) ⟨649512, by rfl⟩ : syracuseStep 1732033 = 1299025) (by norm_num)
theorem B4386325 : Blo 1368503 4386325 := bbase (se 6 (by rfl) ⟨102804, by rfl⟩ : syracuseStep 4386325 = 205609) (by norm_num)
theorem B4935205 : Blo 1368503 4935205 := bbase (se 4 (by rfl) ⟨462675, by rfl⟩ : syracuseStep 4935205 = 925351) (by norm_num)
theorem B3468845 : Blo 1368503 3468845 := bbase (se 3 (by rfl) ⟨650408, by rfl⟩ : syracuseStep 3468845 = 1300817) (by norm_num)
theorem B6934085 : Blo 1368503 6934085 := bbase (se 4 (by rfl) ⟨650070, by rfl⟩ : syracuseStep 6934085 = 1300141) (by norm_num)
theorem B2600525 : Blo 1368503 2600525 := bbase (se 3 (by rfl) ⟨487598, by rfl⟩ : syracuseStep 2600525 = 975197) (by norm_num)
theorem B1732205 : Blo 1368503 1732205 := bbase (se 3 (by rfl) ⟨324788, by rfl⟩ : syracuseStep 1732205 = 649577) (by norm_num)
theorem B1388189 : Blo 1368503 1388189 := bbase (se 3 (by rfl) ⟨260285, by rfl⟩ : syracuseStep 1388189 = 520571) (by norm_num)
theorem B1732261 : Blo 1368503 1732261 := bbase (se 4 (by rfl) ⟨162399, by rfl⟩ : syracuseStep 1732261 = 324799) (by norm_num)
theorem B2600677 : Blo 1368503 2600677 := bbase (se 4 (by rfl) ⟨243813, by rfl⟩ : syracuseStep 2600677 = 487627) (by norm_num)
theorem B6582005 : Blo 1368503 6582005 := bbase (se 5 (by rfl) ⟨308531, by rfl⟩ : syracuseStep 6582005 = 617063) (by norm_num)
theorem B1732357 : Blo 1368503 1732357 := bbase (se 4 (by rfl) ⟨162408, by rfl⟩ : syracuseStep 1732357 = 324817) (by norm_num)
theorem B1462061 : Blo 1368503 1462061 := bbase (se 3 (by rfl) ⟨274136, by rfl⟩ : syracuseStep 1462061 = 548273) (by norm_num)
theorem B4624181 : Blo 1368503 4624181 := bbase (se 5 (by rfl) ⟨216758, by rfl⟩ : syracuseStep 4624181 = 433517) (by norm_num)
theorem B1732529 : Blo 1368503 1732529 := bbase (se 2 (by rfl) ⟨649698, by rfl⟩ : syracuseStep 1732529 = 1299397) (by norm_num)
theorem B4386773 : Blo 1368503 4386773 := bbase (se 7 (by rfl) ⟨51407, by rfl⟩ : syracuseStep 4386773 = 102815) (by norm_num)
theorem B3289061 : Blo 1368503 3289061 := bbase (se 4 (by rfl) ⟨308349, by rfl⟩ : syracuseStep 3289061 = 616699) (by norm_num)
theorem B1732585 : Blo 1368503 1732585 := bbase (se 2 (by rfl) ⟨649719, by rfl⟩ : syracuseStep 1732585 = 1299439) (by norm_num)
theorem B1462249 : Blo 1368503 1462249 := bbase (se 2 (by rfl) ⟨548343, by rfl⟩ : syracuseStep 1462249 = 1096687) (by norm_num)
theorem B2600981 : Blo 1368503 2600981 := bbase (se 6 (by rfl) ⟨60960, by rfl⟩ : syracuseStep 2600981 = 121921) (by norm_num)
theorem B3379229 : Blo 1368503 3379229 := bbase (se 3 (by rfl) ⟨633605, by rfl⟩ : syracuseStep 3379229 = 1267211) (by norm_num)
theorem B5197877 : Blo 1368503 5197877 := bbase (se 5 (by rfl) ⟨243650, by rfl⟩ : syracuseStep 5197877 = 487301) (by norm_num)
theorem B1732681 : Blo 1368503 1732681 := bbase (se 2 (by rfl) ⟨649755, by rfl⟩ : syracuseStep 1732681 = 1299511) (by norm_num)
theorem B4624613 : Blo 1368503 4624613 := bbase (se 4 (by rfl) ⟨433557, by rfl⟩ : syracuseStep 4624613 = 867115) (by norm_num)
theorem B1732853 : Blo 1368503 1732853 := bbase (se 5 (by rfl) ⟨81227, by rfl⟩ : syracuseStep 1732853 = 162455) (by norm_num)
theorem B7803125 : Blo 1368503 7803125 := bbase (se 5 (by rfl) ⟨365771, by rfl⟩ : syracuseStep 7803125 = 731543) (by norm_num)
theorem B1732909 : Blo 1368503 1732909 := bbase (se 3 (by rfl) ⟨324920, by rfl⟩ : syracuseStep 1732909 = 649841) (by norm_num)
theorem B2502965 : Blo 1368503 2502965 := bbase (se 5 (by rfl) ⟨117326, by rfl⟩ : syracuseStep 2502965 = 234653) (by norm_num)
theorem B5198165 : Blo 1368503 5198165 := bbase (se 10 (by rfl) ⟨7614, by rfl⟩ : syracuseStep 5198165 = 15229) (by norm_num)
theorem B7795061 : Blo 1368503 7795061 := bbase (se 5 (by rfl) ⟨365393, by rfl⟩ : syracuseStep 7795061 = 730787) (by norm_num)
theorem B1733005 : Blo 1368503 1733005 := bbase (se 3 (by rfl) ⟨324938, by rfl⟩ : syracuseStep 1733005 = 649877) (by norm_num)
theorem B1733177 : Blo 1368503 1733177 := bbase (se 2 (by rfl) ⟨649941, by rfl⟩ : syracuseStep 1733177 = 1299883) (by norm_num)
theorem B1733233 : Blo 1368503 1733233 := bbase (se 2 (by rfl) ⟨649962, by rfl⟩ : syracuseStep 1733233 = 1299925) (by norm_num)
theorem B4625045 : Blo 1368503 4625045 := bbase (se 6 (by rfl) ⟨108399, by rfl⟩ : syracuseStep 4625045 = 216799) (by norm_num)
theorem B2052773 : Blo 1368503 2052773 := bbase (se 4 (by rfl) ⟨192447, by rfl⟩ : syracuseStep 2052773 = 384895) (by norm_num)
theorem B2052797 : Blo 1368503 2052797 := bbase (se 3 (by rfl) ⟨384899, by rfl⟩ : syracuseStep 2052797 = 769799) (by norm_num)
theorem B1733329 : Blo 1368503 1733329 := bbase (se 2 (by rfl) ⟨649998, by rfl⟩ : syracuseStep 1733329 = 1299997) (by norm_num)
theorem B2052821 : Blo 1368503 2052821 := bbase (se 7 (by rfl) ⟨24056, by rfl⟩ : syracuseStep 2052821 = 48113) (by norm_num)
theorem B3289829 : Blo 1368503 3289829 := bbase (se 4 (by rfl) ⟨308421, by rfl⟩ : syracuseStep 3289829 = 616843) (by norm_num)
theorem B2052845 : Blo 1368503 2052845 := bbase (se 3 (by rfl) ⟨384908, by rfl⟩ : syracuseStep 2052845 = 769817) (by norm_num)
theorem B13153013 : Blo 1368503 13153013 := bbase (se 5 (by rfl) ⟨616547, by rfl⟩ : syracuseStep 13153013 = 1233095) (by norm_num)
theorem B2052869 : Blo 1368503 2052869 := bbase (se 4 (by rfl) ⟨192456, by rfl⟩ : syracuseStep 2052869 = 384913) (by norm_num)
theorem B2601733 : Blo 1368503 2601733 := bbase (se 4 (by rfl) ⟨243912, by rfl⟩ : syracuseStep 2601733 = 487825) (by norm_num)
theorem B2052893 : Blo 1368503 2052893 := bbase (se 3 (by rfl) ⟨384917, by rfl⟩ : syracuseStep 2052893 = 769835) (by norm_num)
theorem B1463069 : Blo 1368503 1463069 := bbase (se 3 (by rfl) ⟨274325, by rfl⟩ : syracuseStep 1463069 = 548651) (by norm_num)
theorem B2052917 : Blo 1368503 2052917 := bbase (se 5 (by rfl) ⟨96230, by rfl⟩ : syracuseStep 2052917 = 192461) (by norm_num)
theorem B2052941 : Blo 1368503 2052941 := bbase (se 3 (by rfl) ⟨384926, by rfl⟩ : syracuseStep 2052941 = 769853) (by norm_num)
theorem B6935381 : Blo 1368503 6935381 := bbase (se 9 (by rfl) ⟨20318, by rfl⟩ : syracuseStep 6935381 = 40637) (by norm_num)
theorem B2052965 : Blo 1368503 2052965 := bbase (se 4 (by rfl) ⟨192465, by rfl⟩ : syracuseStep 2052965 = 384931) (by norm_num)
theorem B2052989 : Blo 1368503 2052989 := bbase (se 3 (by rfl) ⟨384935, by rfl⟩ : syracuseStep 2052989 = 769871) (by norm_num)
theorem B1733501 : Blo 1368503 1733501 := bbase (se 3 (by rfl) ⟨325031, by rfl⟩ : syracuseStep 1733501 = 650063) (by norm_num)
theorem B2003837 : Blo 1368503 2003837 := bbase (se 3 (by rfl) ⟨375719, by rfl⟩ : syracuseStep 2003837 = 751439) (by norm_num)
theorem B2053013 : Blo 1368503 2053013 := bbase (se 6 (by rfl) ⟨48117, by rfl⟩ : syracuseStep 2053013 = 96235) (by norm_num)
theorem B2053037 : Blo 1368503 2053037 := bbase (se 3 (by rfl) ⟨384944, by rfl⟩ : syracuseStep 2053037 = 769889) (by norm_num)
theorem B1733557 : Blo 1368503 1733557 := bbase (se 5 (by rfl) ⟨81260, by rfl⟩ : syracuseStep 1733557 = 162521) (by norm_num)
theorem B2053061 : Blo 1368503 2053061 := bbase (se 4 (by rfl) ⟨192474, by rfl⟩ : syracuseStep 2053061 = 384949) (by norm_num)
theorem B1758169 : Blo 1368503 1758169 := bbase (se 2 (by rfl) ⟨659313, by rfl⟩ : syracuseStep 1758169 = 1318627) (by norm_num)
theorem B2053085 : Blo 1368503 2053085 := bbase (se 3 (by rfl) ⟨384953, by rfl⟩ : syracuseStep 2053085 = 769907) (by norm_num)
theorem B2053109 : Blo 1368503 2053109 := bbase (se 5 (by rfl) ⟨96239, by rfl⟩ : syracuseStep 2053109 = 192479) (by norm_num)
theorem B3511309 : Blo 1368503 3511309 := bbase (se 3 (by rfl) ⟨658370, by rfl⟩ : syracuseStep 3511309 = 1316741) (by norm_num)
theorem B2053133 : Blo 1368503 2053133 := bbase (se 3 (by rfl) ⟨384962, by rfl⟩ : syracuseStep 2053133 = 769925) (by norm_num)
theorem B1561613 : Blo 1368503 1561613 := bbase (se 3 (by rfl) ⟨292802, by rfl⟩ : syracuseStep 1561613 = 585605) (by norm_num)
theorem B1733653 : Blo 1368503 1733653 := bbase (se 6 (by rfl) ⟨40632, by rfl⟩ : syracuseStep 1733653 = 81265) (by norm_num)
theorem B2053157 : Blo 1368503 2053157 := bbase (se 4 (by rfl) ⟨192483, by rfl⟩ : syracuseStep 2053157 = 384967) (by norm_num)
theorem B7025717 : Blo 1368503 7025717 := bbase (se 5 (by rfl) ⟨329330, by rfl⟩ : syracuseStep 7025717 = 658661) (by norm_num)
theorem B6583349 : Blo 1368503 6583349 := bbase (se 5 (by rfl) ⟨308594, by rfl⟩ : syracuseStep 6583349 = 617189) (by norm_num)
theorem B2053181 : Blo 1368503 2053181 := bbase (se 3 (by rfl) ⟨384971, by rfl⟩ : syracuseStep 2053181 = 769943) (by norm_num)
theorem B2053205 : Blo 1368503 2053205 := bbase (se 8 (by rfl) ⟨12030, by rfl⟩ : syracuseStep 2053205 = 24061) (by norm_num)
theorem B2053229 : Blo 1368503 2053229 := bbase (se 3 (by rfl) ⟨384980, by rfl⟩ : syracuseStep 2053229 = 769961) (by norm_num)
theorem B10400885 : Blo 1368503 10400885 := bbase (se 5 (by rfl) ⟨487541, by rfl⟩ : syracuseStep 10400885 = 975083) (by norm_num)
theorem B2053253 : Blo 1368503 2053253 := bbase (se 4 (by rfl) ⟨192492, by rfl⟩ : syracuseStep 2053253 = 384985) (by norm_num)
theorem B2053277 : Blo 1368503 2053277 := bbase (se 3 (by rfl) ⟨384989, by rfl⟩ : syracuseStep 2053277 = 769979) (by norm_num)
theorem B2053301 : Blo 1368503 2053301 := bbase (se 5 (by rfl) ⟨96248, by rfl⟩ : syracuseStep 2053301 = 192497) (by norm_num)
theorem B1733825 : Blo 1368503 1733825 := bbase (se 2 (by rfl) ⟨650184, by rfl⟩ : syracuseStep 1733825 = 1300369) (by norm_num)
theorem B2053325 : Blo 1368503 2053325 := bbase (se 3 (by rfl) ⟨384998, by rfl⟩ : syracuseStep 2053325 = 769997) (by norm_num)
theorem B14062805 : Blo 1368503 14062805 := bbase (se 7 (by rfl) ⟨164798, by rfl⟩ : syracuseStep 14062805 = 329597) (by norm_num)
theorem B1463513 : Blo 1368503 1463513 := bbase (se 2 (by rfl) ⟨548817, by rfl⟩ : syracuseStep 1463513 = 1097635) (by norm_num)
theorem B2053349 : Blo 1368503 2053349 := bbase (se 4 (by rfl) ⟨192501, by rfl⟩ : syracuseStep 2053349 = 385003) (by norm_num)
theorem B6329573 : Blo 1368503 6329573 := bbase (se 4 (by rfl) ⟨593397, by rfl⟩ : syracuseStep 6329573 = 1186795) (by norm_num)
theorem B1733881 : Blo 1368503 1733881 := bbase (se 2 (by rfl) ⟨650205, by rfl⟩ : syracuseStep 1733881 = 1300411) (by norm_num)
theorem B2053373 : Blo 1368503 2053373 := bbase (se 3 (by rfl) ⟨385007, by rfl⟩ : syracuseStep 2053373 = 770015) (by norm_num)
theorem B2053397 : Blo 1368503 2053397 := bbase (se 6 (by rfl) ⟨48126, by rfl⟩ : syracuseStep 2053397 = 96253) (by norm_num)
theorem B2053421 : Blo 1368503 2053421 := bbase (se 3 (by rfl) ⟨385016, by rfl⟩ : syracuseStep 2053421 = 770033) (by norm_num)
theorem B2053445 : Blo 1368503 2053445 := bbase (se 4 (by rfl) ⟨192510, by rfl⟩ : syracuseStep 2053445 = 385021) (by norm_num)
theorem B1733977 : Blo 1368503 1733977 := bbase (se 2 (by rfl) ⟨650241, by rfl⟩ : syracuseStep 1733977 = 1300483) (by norm_num)
theorem B2053469 : Blo 1368503 2053469 := bbase (se 3 (by rfl) ⟨385025, by rfl⟩ : syracuseStep 2053469 = 770051) (by norm_num)
theorem B2053493 : Blo 1368503 2053493 := bbase (se 5 (by rfl) ⟨96257, by rfl⟩ : syracuseStep 2053493 = 192515) (by norm_num)
theorem B2053517 : Blo 1368503 2053517 := bbase (se 3 (by rfl) ⟨385034, by rfl⟩ : syracuseStep 2053517 = 770069) (by norm_num)
theorem B7804309 : Blo 1368503 7804309 := bbase (se 6 (by rfl) ⟨182913, by rfl⟩ : syracuseStep 7804309 = 365827) (by norm_num)
theorem B2053541 : Blo 1368503 2053541 := bbase (se 4 (by rfl) ⟨192519, by rfl⟩ : syracuseStep 2053541 = 385039) (by norm_num)
theorem B2053565 : Blo 1368503 2053565 := bbase (se 3 (by rfl) ⟨385043, by rfl⟩ : syracuseStep 2053565 = 770087) (by norm_num)
theorem B2053589 : Blo 1368503 2053589 := bbase (se 7 (by rfl) ⟨24065, by rfl⟩ : syracuseStep 2053589 = 48131) (by norm_num)
theorem B2192861 : Blo 1368503 2192861 := bbase (se 3 (by rfl) ⟨411161, by rfl⟩ : syracuseStep 2192861 = 822323) (by norm_num)
theorem B2053613 : Blo 1368503 2053613 := bbase (se 3 (by rfl) ⟨385052, by rfl⟩ : syracuseStep 2053613 = 770105) (by norm_num)
theorem B5199349 : Blo 1368503 5199349 := bbase (se 5 (by rfl) ⟨243719, by rfl⟩ : syracuseStep 5199349 = 487439) (by norm_num)
theorem B2053637 : Blo 1368503 2053637 := bbase (se 4 (by rfl) ⟨192528, by rfl⟩ : syracuseStep 2053637 = 385057) (by norm_num)
theorem B1734149 : Blo 1368503 1734149 := bbase (se 4 (by rfl) ⟨162576, by rfl⟩ : syracuseStep 1734149 = 325153) (by norm_num)
theorem B10393109 : Blo 1368503 10393109 := bbase (se 6 (by rfl) ⟨243588, by rfl⟩ : syracuseStep 10393109 = 487177) (by norm_num)
theorem B2053661 : Blo 1368503 2053661 := bbase (se 3 (by rfl) ⟨385061, by rfl⟩ : syracuseStep 2053661 = 770123) (by norm_num)
theorem B2053685 : Blo 1368503 2053685 := bbase (se 5 (by rfl) ⟨96266, by rfl⟩ : syracuseStep 2053685 = 192533) (by norm_num)
theorem B1734205 : Blo 1368503 1734205 := bbase (se 3 (by rfl) ⟨325163, by rfl⟩ : syracuseStep 1734205 = 650327) (by norm_num)
theorem B2053709 : Blo 1368503 2053709 := bbase (se 3 (by rfl) ⟨385070, by rfl⟩ : syracuseStep 2053709 = 770141) (by norm_num)
theorem B2192989 : Blo 1368503 2192989 := bbase (se 3 (by rfl) ⟨411185, by rfl⟩ : syracuseStep 2192989 = 822371) (by norm_num)
theorem B2053733 : Blo 1368503 2053733 := bbase (se 4 (by rfl) ⟨192537, by rfl⟩ : syracuseStep 2053733 = 385075) (by norm_num)
theorem B2053757 : Blo 1368503 2053757 := bbase (se 3 (by rfl) ⟨385079, by rfl⟩ : syracuseStep 2053757 = 770159) (by norm_num)
theorem B2053781 : Blo 1368503 2053781 := bbase (se 6 (by rfl) ⟨48135, by rfl⟩ : syracuseStep 2053781 = 96271) (by norm_num)
theorem B1734301 : Blo 1368503 1734301 := bbase (se 3 (by rfl) ⟨325181, by rfl⟩ : syracuseStep 1734301 = 650363) (by norm_num)
theorem B2053805 : Blo 1368503 2053805 := bbase (se 3 (by rfl) ⟨385088, by rfl⟩ : syracuseStep 2053805 = 770177) (by norm_num)
theorem B2053829 : Blo 1368503 2053829 := bbase (se 4 (by rfl) ⟨192546, by rfl⟩ : syracuseStep 2053829 = 385093) (by norm_num)
theorem B5846741 : Blo 1368503 5846741 := bbase (se 7 (by rfl) ⟨68516, by rfl⟩ : syracuseStep 5846741 = 137033) (by norm_num)
theorem B2053853 : Blo 1368503 2053853 := bbase (se 3 (by rfl) ⟨385097, by rfl⟩ : syracuseStep 2053853 = 770195) (by norm_num)
theorem B1644257 : Blo 1368503 1644257 := bbase (se 2 (by rfl) ⟨616596, by rfl⟩ : syracuseStep 1644257 = 1233193) (by norm_num)
theorem B7706357 : Blo 1368503 7706357 := bbase (se 5 (by rfl) ⟨361235, by rfl⟩ : syracuseStep 7706357 = 722471) (by norm_num)
theorem B2053877 : Blo 1368503 2053877 := bbase (se 5 (by rfl) ⟨96275, by rfl⟩ : syracuseStep 2053877 = 192551) (by norm_num)
theorem B2053901 : Blo 1368503 2053901 := bbase (se 3 (by rfl) ⟨385106, by rfl⟩ : syracuseStep 2053901 = 770213) (by norm_num)
theorem B2053925 : Blo 1368503 2053925 := bbase (se 4 (by rfl) ⟨192555, by rfl⟩ : syracuseStep 2053925 = 385111) (by norm_num)
theorem B5199653 : Blo 1368503 5199653 := bbase (se 4 (by rfl) ⟨487467, by rfl⟩ : syracuseStep 5199653 = 974935) (by norm_num)
theorem B2053949 : Blo 1368503 2053949 := bbase (se 3 (by rfl) ⟨385115, by rfl⟩ : syracuseStep 2053949 = 770231) (by norm_num)
theorem B1734473 : Blo 1368503 1734473 := bbase (se 2 (by rfl) ⟨650427, by rfl⟩ : syracuseStep 1734473 = 1300855) (by norm_num)
theorem B2053973 : Blo 1368503 2053973 := bbase (se 9 (by rfl) ⟨6017, by rfl⟩ : syracuseStep 2053973 = 12035) (by norm_num)
theorem B2053997 : Blo 1368503 2053997 := bbase (se 3 (by rfl) ⟨385124, by rfl⟩ : syracuseStep 2053997 = 770249) (by norm_num)
theorem B1734529 : Blo 1368503 1734529 := bbase (se 2 (by rfl) ⟨650448, by rfl⟩ : syracuseStep 1734529 = 1300897) (by norm_num)
theorem B2054021 : Blo 1368503 2054021 := bbase (se 4 (by rfl) ⟨192564, by rfl⟩ : syracuseStep 2054021 = 385129) (by norm_num)
theorem B2054045 : Blo 1368503 2054045 := bbase (se 3 (by rfl) ⟨385133, by rfl⟩ : syracuseStep 2054045 = 770267) (by norm_num)
theorem B2054069 : Blo 1368503 2054069 := bbase (se 5 (by rfl) ⟨96284, by rfl⟩ : syracuseStep 2054069 = 192569) (by norm_num)
theorem B5273525 : Blo 1368503 5273525 := bbase (se 5 (by rfl) ⟨247196, by rfl⟩ : syracuseStep 5273525 = 494393) (by norm_num)
theorem B2054093 : Blo 1368503 2054093 := bbase (se 3 (by rfl) ⟨385142, by rfl⟩ : syracuseStep 2054093 = 770285) (by norm_num)
theorem B11704277 : Blo 1368503 11704277 := bbase (se 7 (by rfl) ⟨137159, by rfl⟩ : syracuseStep 11704277 = 274319) (by norm_num)
theorem B2054117 : Blo 1368503 2054117 := bbase (se 4 (by rfl) ⟨192573, by rfl⟩ : syracuseStep 2054117 = 385147) (by norm_num)
theorem B3512317 : Blo 1368503 3512317 := bbase (se 3 (by rfl) ⟨658559, by rfl⟩ : syracuseStep 3512317 = 1317119) (by norm_num)
theorem B2054141 : Blo 1368503 2054141 := bbase (se 3 (by rfl) ⟨385151, by rfl⟩ : syracuseStep 2054141 = 770303) (by norm_num)
theorem B1644565 : Blo 1368503 1644565 := bbase (se 6 (by rfl) ⟨38544, by rfl⟩ : syracuseStep 1644565 = 77089) (by norm_num)
theorem B2054165 : Blo 1368503 2054165 := bbase (se 6 (by rfl) ⟨48144, by rfl⟩ : syracuseStep 2054165 = 96289) (by norm_num)
theorem B2054189 : Blo 1368503 2054189 := bbase (se 3 (by rfl) ⟨385160, by rfl⟩ : syracuseStep 2054189 = 770321) (by norm_num)
theorem B2054213 : Blo 1368503 2054213 := bbase (se 4 (by rfl) ⟨192582, by rfl⟩ : syracuseStep 2054213 = 385165) (by norm_num)
theorem B16660565 : Blo 1368503 16660565 := bbase (se 8 (by rfl) ⟨97620, by rfl⟩ : syracuseStep 16660565 = 195241) (by norm_num)
theorem B2054237 : Blo 1368503 2054237 := bbase (se 3 (by rfl) ⟨385169, by rfl⟩ : syracuseStep 2054237 = 770339) (by norm_num)
theorem B6936677 : Blo 1368503 6936677 := bbase (se 4 (by rfl) ⟨650313, by rfl⟩ : syracuseStep 6936677 = 1300627) (by norm_num)
theorem B2054261 : Blo 1368503 2054261 := bbase (se 5 (by rfl) ⟨96293, by rfl⟩ : syracuseStep 2054261 = 192587) (by norm_num)
theorem B2054285 : Blo 1368503 2054285 := bbase (se 3 (by rfl) ⟨385178, by rfl⟩ : syracuseStep 2054285 = 770357) (by norm_num)
theorem B2054309 : Blo 1368503 2054309 := bbase (se 4 (by rfl) ⟨192591, by rfl⟩ : syracuseStep 2054309 = 385183) (by norm_num)
theorem B4389029 : Blo 1368503 4389029 := bbase (se 4 (by rfl) ⟨411471, by rfl⟩ : syracuseStep 4389029 = 822943) (by norm_num)
theorem B2054333 : Blo 1368503 2054333 := bbase (se 3 (by rfl) ⟨385187, by rfl⟩ : syracuseStep 2054333 = 770375) (by norm_num)
theorem B2054357 : Blo 1368503 2054357 := bbase (se 7 (by rfl) ⟨24074, by rfl⟩ : syracuseStep 2054357 = 48149) (by norm_num)
theorem B2054381 : Blo 1368503 2054381 := bbase (se 3 (by rfl) ⟨385196, by rfl⟩ : syracuseStep 2054381 = 770393) (by norm_num)
theorem B2054405 : Blo 1368503 2054405 := bbase (se 4 (by rfl) ⟨192600, by rfl⟩ : syracuseStep 2054405 = 385201) (by norm_num)
theorem B2054429 : Blo 1368503 2054429 := bbase (se 3 (by rfl) ⟨385205, by rfl⟩ : syracuseStep 2054429 = 770411) (by norm_num)
theorem B1407277 : Blo 1368503 1407277 := bbase (se 3 (by rfl) ⟨263864, by rfl⟩ : syracuseStep 1407277 = 527729) (by norm_num)
theorem B2054453 : Blo 1368503 2054453 := bbase (se 5 (by rfl) ⟨96302, by rfl⟩ : syracuseStep 2054453 = 192605) (by norm_num)
theorem B5626181 : Blo 1368503 5626181 := bbase (se 4 (by rfl) ⟨527454, by rfl⟩ : syracuseStep 5626181 = 1054909) (by norm_num)
theorem B2054477 : Blo 1368503 2054477 := bbase (se 3 (by rfl) ⟨385214, by rfl⟩ : syracuseStep 2054477 = 770429) (by norm_num)
theorem B2054501 : Blo 1368503 2054501 := bbase (se 4 (by rfl) ⟨192609, by rfl⟩ : syracuseStep 2054501 = 385219) (by norm_num)
theorem B2054525 : Blo 1368503 2054525 := bbase (se 3 (by rfl) ⟨385223, by rfl⟩ : syracuseStep 2054525 = 770447) (by norm_num)
theorem B2193797 : Blo 1368503 2193797 := bbase (se 4 (by rfl) ⟨205668, by rfl⟩ : syracuseStep 2193797 = 411337) (by norm_num)
theorem B1644949 : Blo 1368503 1644949 := bbase (se 6 (by rfl) ⟨38553, by rfl⟩ : syracuseStep 1644949 = 77107) (by norm_num)
theorem B2054549 : Blo 1368503 2054549 := bbase (se 6 (by rfl) ⟨48153, by rfl⟩ : syracuseStep 2054549 = 96307) (by norm_num)
theorem B1644953 : Blo 1368503 1644953 := bbase (se 2 (by rfl) ⟨616857, by rfl⟩ : syracuseStep 1644953 = 1233715) (by norm_num)
theorem B2054573 : Blo 1368503 2054573 := bbase (se 3 (by rfl) ⟨385232, by rfl⟩ : syracuseStep 2054573 = 770465) (by norm_num)
theorem B2054597 : Blo 1368503 2054597 := bbase (se 4 (by rfl) ⟨192618, by rfl⟩ : syracuseStep 2054597 = 385237) (by norm_num)
theorem B6584773 : Blo 1368503 6584773 := bbase (se 4 (by rfl) ⟨617322, by rfl⟩ : syracuseStep 6584773 = 1234645) (by norm_num)
theorem B2054621 : Blo 1368503 2054621 := bbase (se 3 (by rfl) ⟨385241, by rfl⟩ : syracuseStep 2054621 = 770483) (by norm_num)
theorem B2054645 : Blo 1368503 2054645 := bbase (se 5 (by rfl) ⟨96311, by rfl⟩ : syracuseStep 2054645 = 192623) (by norm_num)
theorem B3291637 : Blo 1368503 3291637 := bbase (se 5 (by rfl) ⟨154295, by rfl⟩ : syracuseStep 3291637 = 308591) (by norm_num)
theorem B6928901 : Blo 1368503 6928901 := bbase (se 4 (by rfl) ⟨649584, by rfl⟩ : syracuseStep 6928901 = 1299169) (by norm_num)
theorem B2054669 : Blo 1368503 2054669 := bbase (se 3 (by rfl) ⟨385250, by rfl⟩ : syracuseStep 2054669 = 770501) (by norm_num)
theorem B2054693 : Blo 1368503 2054693 := bbase (se 4 (by rfl) ⟨192627, by rfl⟩ : syracuseStep 2054693 = 385255) (by norm_num)
theorem B2054717 : Blo 1368503 2054717 := bbase (se 3 (by rfl) ⟨385259, by rfl⟩ : syracuseStep 2054717 = 770519) (by norm_num)
theorem B2054741 : Blo 1368503 2054741 := bbase (se 8 (by rfl) ⟨12039, by rfl⟩ : syracuseStep 2054741 = 24079) (by norm_num)
theorem B2341469 : Blo 1368503 2341469 := bbase (se 3 (by rfl) ⟨439025, by rfl⟩ : syracuseStep 2341469 = 878051) (by norm_num)
theorem B2054765 : Blo 1368503 2054765 := bbase (se 3 (by rfl) ⟨385268, by rfl⟩ : syracuseStep 2054765 = 770537) (by norm_num)
theorem B2054789 : Blo 1368503 2054789 := bbase (se 4 (by rfl) ⟨192636, by rfl⟩ : syracuseStep 2054789 = 385273) (by norm_num)
theorem B2923165 : Blo 1368503 2923165 := bbase (se 3 (by rfl) ⟨548093, by rfl⟩ : syracuseStep 2923165 = 1096187) (by norm_num)
theorem B2054813 : Blo 1368503 2054813 := bbase (se 3 (by rfl) ⟨385277, by rfl⟩ : syracuseStep 2054813 = 770555) (by norm_num)
theorem B2194085 : Blo 1368503 2194085 := bbase (se 4 (by rfl) ⟨205695, by rfl⟩ : syracuseStep 2194085 = 411391) (by norm_num)
theorem B2054837 : Blo 1368503 2054837 := bbase (se 5 (by rfl) ⟨96320, by rfl⟩ : syracuseStep 2054837 = 192641) (by norm_num)
theorem B2054861 : Blo 1368503 2054861 := bbase (se 3 (by rfl) ⟨385286, by rfl⟩ : syracuseStep 2054861 = 770573) (by norm_num)
theorem B2054885 : Blo 1368503 2054885 := bbase (se 4 (by rfl) ⟨192645, by rfl⟩ : syracuseStep 2054885 = 385291) (by norm_num)
theorem B4618997 : Blo 1368503 4618997 := bbase (se 5 (by rfl) ⟨216515, by rfl⟩ : syracuseStep 4618997 = 433031) (by norm_num)
theorem B2054909 : Blo 1368503 2054909 := bbase (se 3 (by rfl) ⟨385295, by rfl⟩ : syracuseStep 2054909 = 770591) (by norm_num)
theorem B2923285 : Blo 1368503 2923285 := bbase (se 6 (by rfl) ⟨68514, by rfl⟩ : syracuseStep 2923285 = 137029) (by norm_num)
theorem B2054933 : Blo 1368503 2054933 := bbase (se 6 (by rfl) ⟨48162, by rfl⟩ : syracuseStep 2054933 = 96325) (by norm_num)
theorem B1645357 : Blo 1368503 1645357 := bbase (se 3 (by rfl) ⟨308504, by rfl⟩ : syracuseStep 1645357 = 617009) (by norm_num)
theorem B2054957 : Blo 1368503 2054957 := bbase (se 3 (by rfl) ⟨385304, by rfl⟩ : syracuseStep 2054957 = 770609) (by norm_num)
theorem B2054981 : Blo 1368503 2054981 := bbase (se 4 (by rfl) ⟨192654, by rfl⟩ : syracuseStep 2054981 = 385309) (by norm_num)
theorem B2055005 : Blo 1368503 2055005 := bbase (se 3 (by rfl) ⟨385313, by rfl⟩ : syracuseStep 2055005 = 770627) (by norm_num)
theorem B2055029 : Blo 1368503 2055029 := bbase (se 5 (by rfl) ⟨96329, by rfl⟩ : syracuseStep 2055029 = 192659) (by norm_num)
theorem B1948549 : Blo 1368503 1948549 := bbase (se 4 (by rfl) ⟨182676, by rfl⟩ : syracuseStep 1948549 = 365353) (by norm_num)
theorem B2055053 : Blo 1368503 2055053 := bbase (se 3 (by rfl) ⟨385322, by rfl⟩ : syracuseStep 2055053 = 770645) (by norm_num)
theorem B2055077 : Blo 1368503 2055077 := bbase (se 4 (by rfl) ⟨192663, by rfl⟩ : syracuseStep 2055077 = 385327) (by norm_num)
theorem B3464117 : Blo 1368503 3464117 := bbase (se 5 (by rfl) ⟨162380, by rfl⟩ : syracuseStep 3464117 = 324761) (by norm_num)
theorem B2055101 : Blo 1368503 2055101 := bbase (se 3 (by rfl) ⟨385331, by rfl⟩ : syracuseStep 2055101 = 770663) (by norm_num)
theorem B2055125 : Blo 1368503 2055125 := bbase (se 7 (by rfl) ⟨24083, by rfl⟩ : syracuseStep 2055125 = 48167) (by norm_num)
theorem B3079133 : Blo 1368503 3079133 := bbase (se 3 (by rfl) ⟨577337, by rfl⟩ : syracuseStep 3079133 = 1154675) (by norm_num)
theorem B4938725 : Blo 1368503 4938725 := bbase (se 4 (by rfl) ⟨463005, by rfl⟩ : syracuseStep 4938725 = 926011) (by norm_num)
theorem B2055149 : Blo 1368503 2055149 := bbase (se 3 (by rfl) ⟨385340, by rfl⟩ : syracuseStep 2055149 = 770681) (by norm_num)
theorem B3292157 : Blo 1368503 3292157 := bbase (se 3 (by rfl) ⟨617279, by rfl⟩ : syracuseStep 3292157 = 1234559) (by norm_num)
theorem B2055173 : Blo 1368503 2055173 := bbase (se 4 (by rfl) ⟨192672, by rfl⟩ : syracuseStep 2055173 = 385345) (by norm_num)
theorem B2923541 : Blo 1368503 2923541 := bbase (se 6 (by rfl) ⟨68520, by rfl⟩ : syracuseStep 2923541 = 137041) (by norm_num)
theorem B2055197 : Blo 1368503 2055197 := bbase (se 3 (by rfl) ⟨385349, by rfl⟩ : syracuseStep 2055197 = 770699) (by norm_num)
theorem B3079205 : Blo 1368503 3079205 := bbase (se 4 (by rfl) ⟨288675, by rfl⟩ : syracuseStep 3079205 = 577351) (by norm_num)
theorem B2055221 : Blo 1368503 2055221 := bbase (se 5 (by rfl) ⟨96338, by rfl⟩ : syracuseStep 2055221 = 192677) (by norm_num)
theorem B2194501 : Blo 1368503 2194501 := bbase (se 4 (by rfl) ⟨205734, by rfl⟩ : syracuseStep 2194501 = 411469) (by norm_num)
theorem B2055245 : Blo 1368503 2055245 := bbase (se 3 (by rfl) ⟨385358, by rfl⟩ : syracuseStep 2055245 = 770717) (by norm_num)
theorem B2055269 : Blo 1368503 2055269 := bbase (se 4 (by rfl) ⟨192681, by rfl⟩ : syracuseStep 2055269 = 385363) (by norm_num)
theorem B3079277 : Blo 1368503 3079277 := bbase (se 3 (by rfl) ⟨577364, by rfl⟩ : syracuseStep 3079277 = 1154729) (by norm_num)
theorem B3464309 : Blo 1368503 3464309 := bbase (se 5 (by rfl) ⟨162389, by rfl⟩ : syracuseStep 3464309 = 324779) (by norm_num)
theorem B8772725 : Blo 1368503 8772725 := bbase (se 5 (by rfl) ⟨411221, by rfl⟩ : syracuseStep 8772725 = 822443) (by norm_num)
theorem B2055293 : Blo 1368503 2055293 := bbase (se 3 (by rfl) ⟨385367, by rfl⟩ : syracuseStep 2055293 = 770735) (by norm_num)
theorem B4684949 : Blo 1368503 4684949 := bbase (se 6 (by rfl) ⟨109803, by rfl⟩ : syracuseStep 4684949 = 219607) (by norm_num)
theorem B2055317 : Blo 1368503 2055317 := bbase (se 6 (by rfl) ⟨48171, by rfl⟩ : syracuseStep 2055317 = 96343) (by norm_num)
theorem B4619429 : Blo 1368503 4619429 := bbase (se 4 (by rfl) ⟨433071, by rfl⟩ : syracuseStep 4619429 = 866143) (by norm_num)
theorem B2055341 : Blo 1368503 2055341 := bbase (se 3 (by rfl) ⟨385376, by rfl⟩ : syracuseStep 2055341 = 770753) (by norm_num)
theorem B3079349 : Blo 1368503 3079349 := bbase (se 5 (by rfl) ⟨144344, by rfl⟩ : syracuseStep 3079349 = 288689) (by norm_num)
theorem B4447429 : Blo 1368503 4447429 := bbase (se 4 (by rfl) ⟨416946, by rfl⟩ : syracuseStep 4447429 = 833893) (by norm_num)
theorem B2055365 : Blo 1368503 2055365 := bbase (se 4 (by rfl) ⟨192690, by rfl⟩ : syracuseStep 2055365 = 385381) (by norm_num)
theorem B2055389 : Blo 1368503 2055389 := bbase (se 3 (by rfl) ⟨385385, by rfl⟩ : syracuseStep 2055389 = 770771) (by norm_num)
theorem B2309357 : Blo 1368503 2309357 := bbase (se 3 (by rfl) ⟨433004, by rfl⟩ : syracuseStep 2309357 = 866009) (by norm_num)
theorem B2055413 : Blo 1368503 2055413 := bbase (se 5 (by rfl) ⟨96347, by rfl⟩ : syracuseStep 2055413 = 192695) (by norm_num)
theorem B3079421 : Blo 1368503 3079421 := bbase (se 3 (by rfl) ⟨577391, by rfl⟩ : syracuseStep 3079421 = 1154783) (by norm_num)
theorem B2055437 : Blo 1368503 2055437 := bbase (se 3 (by rfl) ⟨385394, by rfl⟩ : syracuseStep 2055437 = 770789) (by norm_num)
theorem B2055461 : Blo 1368503 2055461 := bbase (se 4 (by rfl) ⟨192699, by rfl⟩ : syracuseStep 2055461 = 385399) (by norm_num)
theorem B2055485 : Blo 1368503 2055485 := bbase (se 3 (by rfl) ⟨385403, by rfl⟩ : syracuseStep 2055485 = 770807) (by norm_num)
theorem B3079493 : Blo 1368503 3079493 := bbase (se 4 (by rfl) ⟨288702, by rfl⟩ : syracuseStep 3079493 = 577405) (by norm_num)
theorem B2055509 : Blo 1368503 2055509 := bbase (se 11 (by rfl) ⟨1505, by rfl⟩ : syracuseStep 2055509 = 3011) (by norm_num)
theorem B2309485 : Blo 1368503 2309485 := bbase (se 3 (by rfl) ⟨433028, by rfl⟩ : syracuseStep 2309485 = 866057) (by norm_num)
theorem B2055533 : Blo 1368503 2055533 := bbase (se 3 (by rfl) ⟨385412, by rfl⟩ : syracuseStep 2055533 = 770825) (by norm_num)
theorem B6937973 : Blo 1368503 6937973 := bbase (se 5 (by rfl) ⟨325217, by rfl⟩ : syracuseStep 6937973 = 650435) (by norm_num)
theorem B3292541 : Blo 1368503 3292541 := bbase (se 3 (by rfl) ⟨617351, by rfl⟩ : syracuseStep 3292541 = 1234703) (by norm_num)
theorem B2055557 : Blo 1368503 2055557 := bbase (se 4 (by rfl) ⟨192708, by rfl⟩ : syracuseStep 2055557 = 385417) (by norm_num)
theorem B3079565 : Blo 1368503 3079565 := bbase (se 3 (by rfl) ⟨577418, by rfl⟩ : syracuseStep 3079565 = 1154837) (by norm_num)
theorem B4939157 : Blo 1368503 4939157 := bbase (se 6 (by rfl) ⟨115761, by rfl⟩ : syracuseStep 4939157 = 231523) (by norm_num)
theorem B2776477 : Blo 1368503 2776477 := bbase (se 3 (by rfl) ⟨520589, by rfl⟩ : syracuseStep 2776477 = 1041179) (by norm_num)
theorem B2055581 : Blo 1368503 2055581 := bbase (se 3 (by rfl) ⟨385421, by rfl⟩ : syracuseStep 2055581 = 770843) (by norm_num)
theorem B1850789 : Blo 1368503 1850789 := bbase (se 4 (by rfl) ⟨173511, by rfl⟩ : syracuseStep 1850789 = 347023) (by norm_num)
theorem B3513773 : Blo 1368503 3513773 := bbase (se 3 (by rfl) ⟨658832, by rfl⟩ : syracuseStep 3513773 = 1317665) (by norm_num)
theorem B3292589 : Blo 1368503 3292589 := bbase (se 3 (by rfl) ⟨617360, by rfl⟩ : syracuseStep 3292589 = 1234721) (by norm_num)
theorem B3292597 : Blo 1368503 3292597 := bbase (se 5 (by rfl) ⟨154340, by rfl⟩ : syracuseStep 3292597 = 308681) (by norm_num)
theorem B2055605 : Blo 1368503 2055605 := bbase (se 5 (by rfl) ⟨96356, by rfl⟩ : syracuseStep 2055605 = 192713) (by norm_num)
theorem B2309573 : Blo 1368503 2309573 := bbase (se 4 (by rfl) ⟨216522, by rfl⟩ : syracuseStep 2309573 = 433045) (by norm_num)
theorem B5848517 : Blo 1368503 5848517 := bbase (se 4 (by rfl) ⟨548298, by rfl⟩ : syracuseStep 5848517 = 1096597) (by norm_num)
theorem B3464653 : Blo 1368503 3464653 := bbase (se 3 (by rfl) ⟨649622, by rfl⟩ : syracuseStep 3464653 = 1299245) (by norm_num)
theorem B2055629 : Blo 1368503 2055629 := bbase (se 3 (by rfl) ⟨385430, by rfl⟩ : syracuseStep 2055629 = 770861) (by norm_num)
theorem B3079637 : Blo 1368503 3079637 := bbase (se 7 (by rfl) ⟨36089, by rfl⟩ : syracuseStep 3079637 = 72179) (by norm_num)
theorem B1949141 : Blo 1368503 1949141 := bbase (se 7 (by rfl) ⟨22841, by rfl⟩ : syracuseStep 1949141 = 45683) (by norm_num)
theorem B6766037 : Blo 1368503 6766037 := bbase (se 7 (by rfl) ⟨79289, by rfl⟩ : syracuseStep 6766037 = 158579) (by norm_num)
theorem B2055653 : Blo 1368503 2055653 := bbase (se 4 (by rfl) ⟨192717, by rfl⟩ : syracuseStep 2055653 = 385435) (by norm_num)
theorem B2055677 : Blo 1368503 2055677 := bbase (se 3 (by rfl) ⟨385439, by rfl⟩ : syracuseStep 2055677 = 770879) (by norm_num)
theorem B1539589 : Blo 1368503 1539589 := bbase (se 4 (by rfl) ⟨144336, by rfl⟩ : syracuseStep 1539589 = 288673) (by norm_num)
theorem B2055701 : Blo 1368503 2055701 := bbase (se 6 (by rfl) ⟨48180, by rfl⟩ : syracuseStep 2055701 = 96361) (by norm_num)
theorem B3079709 : Blo 1368503 3079709 := bbase (se 3 (by rfl) ⟨577445, by rfl⟩ : syracuseStep 3079709 = 1154891) (by norm_num)
theorem B2965021 : Blo 1368503 2965021 := bbase (se 3 (by rfl) ⟨555941, by rfl⟩ : syracuseStep 2965021 = 1111883) (by norm_num)
theorem B1949221 : Blo 1368503 1949221 := bbase (se 4 (by rfl) ⟨182739, by rfl⟩ : syracuseStep 1949221 = 365479) (by norm_num)
theorem B1539625 : Blo 1368503 1539625 := bbase (se 2 (by rfl) ⟨577359, by rfl⟩ : syracuseStep 1539625 = 1154719) (by norm_num)
theorem B2055725 : Blo 1368503 2055725 := bbase (se 3 (by rfl) ⟨385448, by rfl⟩ : syracuseStep 2055725 = 770897) (by norm_num)
theorem B3464765 : Blo 1368503 3464765 := bbase (se 3 (by rfl) ⟨649643, by rfl⟩ : syracuseStep 3464765 = 1299287) (by norm_num)
theorem B2309701 : Blo 1368503 2309701 := bbase (se 4 (by rfl) ⟨216534, by rfl⟩ : syracuseStep 2309701 = 433069) (by norm_num)
theorem B2055749 : Blo 1368503 2055749 := bbase (se 4 (by rfl) ⟨192726, by rfl⟩ : syracuseStep 2055749 = 385453) (by norm_num)
theorem B1539661 : Blo 1368503 1539661 := bbase (se 3 (by rfl) ⟨288686, by rfl⟩ : syracuseStep 1539661 = 577373) (by norm_num)
theorem B4619861 : Blo 1368503 4619861 := bbase (se 8 (by rfl) ⟨27069, by rfl⟩ : syracuseStep 4619861 = 54139) (by norm_num)
theorem B3079781 : Blo 1368503 3079781 := bbase (se 4 (by rfl) ⟨288729, by rfl⟩ : syracuseStep 3079781 = 577459) (by norm_num)
theorem B1539697 : Blo 1368503 1539697 := bbase (se 2 (by rfl) ⟨577386, by rfl⟩ : syracuseStep 1539697 = 1154773) (by norm_num)
theorem B1539733 : Blo 1368503 1539733 := bbase (se 6 (by rfl) ⟨36087, by rfl⟩ : syracuseStep 1539733 = 72175) (by norm_num)
theorem B2309789 : Blo 1368503 2309789 := bbase (se 3 (by rfl) ⟨433085, by rfl⟩ : syracuseStep 2309789 = 866171) (by norm_num)
theorem B1949341 : Blo 1368503 1949341 := bbase (se 3 (by rfl) ⟨365501, by rfl⟩ : syracuseStep 1949341 = 731003) (by norm_num)
theorem B3079853 : Blo 1368503 3079853 := bbase (se 3 (by rfl) ⟨577472, by rfl⟩ : syracuseStep 3079853 = 1154945) (by norm_num)
theorem B5848757 : Blo 1368503 5848757 := bbase (se 5 (by rfl) ⟨274160, by rfl⟩ : syracuseStep 5848757 = 548321) (by norm_num)
theorem B1539769 : Blo 1368503 1539769 := bbase (se 2 (by rfl) ⟨577413, by rfl⟩ : syracuseStep 1539769 = 1154827) (by norm_num)
theorem B1539805 : Blo 1368503 1539805 := bbase (se 3 (by rfl) ⟨288713, by rfl⟩ : syracuseStep 1539805 = 577427) (by norm_num)
theorem B3079925 : Blo 1368503 3079925 := bbase (se 5 (by rfl) ⟨144371, by rfl⟩ : syracuseStep 3079925 = 288743) (by norm_num)
theorem B3464957 : Blo 1368503 3464957 := bbase (se 3 (by rfl) ⟨649679, by rfl⟩ : syracuseStep 3464957 = 1299359) (by norm_num)
theorem B1949437 : Blo 1368503 1949437 := bbase (se 3 (by rfl) ⟨365519, by rfl⟩ : syracuseStep 1949437 = 731039) (by norm_num)
theorem B1539841 : Blo 1368503 1539841 := bbase (se 2 (by rfl) ⟨577440, by rfl⟩ : syracuseStep 1539841 = 1154881) (by norm_num)
theorem B6930197 : Blo 1368503 6930197 := bbase (se 6 (by rfl) ⟨162426, by rfl⟩ : syracuseStep 6930197 = 324853) (by norm_num)
theorem B2309917 : Blo 1368503 2309917 := bbase (se 3 (by rfl) ⟨433109, by rfl⟩ : syracuseStep 2309917 = 866219) (by norm_num)
theorem B1539877 : Blo 1368503 1539877 := bbase (se 4 (by rfl) ⟨144363, by rfl⟩ : syracuseStep 1539877 = 288727) (by norm_num)
theorem B3079997 : Blo 1368503 3079997 := bbase (se 3 (by rfl) ⟨577499, by rfl⟩ : syracuseStep 3079997 = 1154999) (by norm_num)
theorem B1539913 : Blo 1368503 1539913 := bbase (se 2 (by rfl) ⟨577467, by rfl⟩ : syracuseStep 1539913 = 1154935) (by norm_num)
theorem B5201765 : Blo 1368503 5201765 := bbase (se 4 (by rfl) ⟨487665, by rfl⟩ : syracuseStep 5201765 = 975331) (by norm_num)
theorem B1539949 : Blo 1368503 1539949 := bbase (se 3 (by rfl) ⟨288740, by rfl⟩ : syracuseStep 1539949 = 577481) (by norm_num)
theorem B2310005 : Blo 1368503 2310005 := bbase (se 5 (by rfl) ⟨108281, by rfl⟩ : syracuseStep 2310005 = 216563) (by norm_num)
theorem B3080069 : Blo 1368503 3080069 := bbase (se 4 (by rfl) ⟨288756, by rfl⟩ : syracuseStep 3080069 = 577513) (by norm_num)
theorem B2924429 : Blo 1368503 2924429 := bbase (se 3 (by rfl) ⟨548330, by rfl⟩ : syracuseStep 2924429 = 1096661) (by norm_num)
theorem B1539985 : Blo 1368503 1539985 := bbase (se 2 (by rfl) ⟨577494, by rfl⟩ : syracuseStep 1539985 = 1154989) (by norm_num)
theorem B3899285 : Blo 1368503 3899285 := bbase (se 6 (by rfl) ⟨91389, by rfl⟩ : syracuseStep 3899285 = 182779) (by norm_num)
theorem B1540021 : Blo 1368503 1540021 := bbase (se 5 (by rfl) ⟨72188, by rfl⟩ : syracuseStep 1540021 = 144377) (by norm_num)
theorem B3702725 : Blo 1368503 3702725 := bbase (se 4 (by rfl) ⟨347130, by rfl⟩ : syracuseStep 3702725 = 694261) (by norm_num)
theorem B3080141 : Blo 1368503 3080141 := bbase (se 3 (by rfl) ⟨577526, by rfl⟩ : syracuseStep 3080141 = 1155053) (by norm_num)
theorem B1540057 : Blo 1368503 1540057 := bbase (se 2 (by rfl) ⟨577521, by rfl⟩ : syracuseStep 1540057 = 1155043) (by norm_num)
theorem B1851373 : Blo 1368503 1851373 := bbase (se 3 (by rfl) ⟨347132, by rfl⟩ : syracuseStep 1851373 = 694265) (by norm_num)
theorem B2310133 : Blo 1368503 2310133 := bbase (se 5 (by rfl) ⟨108287, by rfl⟩ : syracuseStep 2310133 = 216575) (by norm_num)
theorem B1540093 : Blo 1368503 1540093 := bbase (se 3 (by rfl) ⟨288767, by rfl⟩ : syracuseStep 1540093 = 577535) (by norm_num)
theorem B3080195 : Blo 1368503 3080195 := bstep (se 1 (by rfl) ⟨2310146, by rfl⟩ : syracuseStep 3080195 = 4620293) B4620293
theorem B2252819 : Blo 1368503 2252819 := bstep (se 1 (by rfl) ⟨1689614, by rfl⟩ : syracuseStep 2252819 = 3379229) B3379229
theorem B3465251 : Blo 1368503 3465251 := bstep (se 1 (by rfl) ⟨2598938, by rfl⟩ : syracuseStep 3465251 = 5197877) B5197877
theorem B1540147 : Blo 1368503 1540147 := bstep (se 1 (by rfl) ⟨1155110, by rfl⟩ : syracuseStep 1540147 = 2310221) B2310221
theorem B1949779 : Blo 1368503 1949779 := bstep (se 1 (by rfl) ⟨1462334, by rfl⟩ : syracuseStep 1949779 = 2924669) B2924669
theorem B2310241 : Blo 1368503 2310241 := bstep (se 2 (by rfl) ⟨866340, by rfl⟩ : syracuseStep 2310241 = 1732681) B1732681
theorem B4620401 : Blo 1368503 4620401 := bstep (se 2 (by rfl) ⟨1732650, by rfl⟩ : syracuseStep 4620401 = 3465301) B3465301
theorem B2310275 : Blo 1368503 2310275 := bstep (se 1 (by rfl) ⟨1732706, by rfl⟩ : syracuseStep 2310275 = 3465413) B3465413
theorem B18735245 : Blo 1368503 18735245 := bstep (se 3 (by rfl) ⟨3512858, by rfl⟩ : syracuseStep 18735245 = 7025717) B7025717
theorem B5202083 : Blo 1368503 5202083 := bstep (se 1 (by rfl) ⟨3901562, by rfl⟩ : syracuseStep 5202083 = 7803125) B7803125
theorem B1540291 : Blo 1368503 1540291 := bstep (se 1 (by rfl) ⟨1155218, by rfl⟩ : syracuseStep 1540291 = 2310437) B2310437
theorem B3465443 : Blo 1368503 3465443 := bstep (se 1 (by rfl) ⟨2599082, by rfl⟩ : syracuseStep 3465443 = 5198165) B5198165
theorem B11108593 : Blo 1368503 11108593 := bstep (se 2 (by rfl) ⟨4165722, by rfl⟩ : syracuseStep 11108593 = 8331445) B8331445
theorem B2310403 : Blo 1368503 2310403 := bstep (se 1 (by rfl) ⟨1732802, by rfl⟩ : syracuseStep 2310403 = 3465605) B3465605
theorem B3080465 : Blo 1368503 3080465 := bstep (se 2 (by rfl) ⟨1155174, by rfl⟩ : syracuseStep 3080465 = 2310349) B2310349
theorem B3080483 : Blo 1368503 3080483 := bstep (se 1 (by rfl) ⟨2310362, by rfl⟩ : syracuseStep 3080483 = 4620725) B4620725
theorem B1540435 : Blo 1368503 1540435 := bstep (se 1 (by rfl) ⟨1155326, by rfl⟩ : syracuseStep 1540435 = 2310653) B2310653
theorem B4686179 : Blo 1368503 4686179 := bstep (se 1 (by rfl) ⟨3514634, by rfl⟩ : syracuseStep 4686179 = 7029269) B7029269
theorem B35553649 : Blo 1368503 35553649 := bstep (se 2 (by rfl) ⟨13332618, by rfl⟩ : syracuseStep 35553649 = 26665237) B26665237
theorem B2310545 : Blo 1368503 2310545 := bstep (se 2 (by rfl) ⟨866454, by rfl⟩ : syracuseStep 2310545 = 1732909) B1732909
theorem B1851827 : Blo 1368503 1851827 := bstep (se 1 (by rfl) ⟨1388870, by rfl⟩ : syracuseStep 1851827 = 2777741) B2777741
theorem B1368515 : Blo 1368503 1368515 := bstep (se 1 (by rfl) ⟨1026386, by rfl⟩ : syracuseStep 1368515 = 2052773) B2052773
theorem B1368531 : Blo 1368503 1368531 := bstep (se 1 (by rfl) ⟨1026398, by rfl⟩ : syracuseStep 1368531 = 2052797) B2052797
theorem B1368547 : Blo 1368503 1368547 := bstep (se 1 (by rfl) ⟨1026410, by rfl⟩ : syracuseStep 1368547 = 2052821) B2052821
theorem B1540579 : Blo 1368503 1540579 := bstep (se 1 (by rfl) ⟨1155434, by rfl⟩ : syracuseStep 1540579 = 2310869) B2310869
theorem B1368563 : Blo 1368503 1368563 := bstep (se 1 (by rfl) ⟨1026422, by rfl⟩ : syracuseStep 1368563 = 2052845) B2052845
theorem B1368579 : Blo 1368503 1368579 := bstep (se 1 (by rfl) ⟨1026434, by rfl⟩ : syracuseStep 1368579 = 2052869) B2052869
theorem B2310673 : Blo 1368503 2310673 := bstep (se 2 (by rfl) ⟨866502, by rfl⟩ : syracuseStep 2310673 = 1733005) B1733005
theorem B1368595 : Blo 1368503 1368595 := bstep (se 1 (by rfl) ⟨1026446, by rfl⟩ : syracuseStep 1368595 = 2052893) B2052893
theorem B1368611 : Blo 1368503 1368611 := bstep (se 1 (by rfl) ⟨1026458, by rfl⟩ : syracuseStep 1368611 = 2052917) B2052917
theorem B3080753 : Blo 1368503 3080753 := bstep (se 2 (by rfl) ⟨1155282, by rfl⟩ : syracuseStep 3080753 = 2310565) B2310565
theorem B1368627 : Blo 1368503 1368627 := bstep (se 1 (by rfl) ⟨1026470, by rfl⟩ : syracuseStep 1368627 = 2052941) B2052941
theorem B2310707 : Blo 1368503 2310707 := bstep (se 1 (by rfl) ⟨1733030, by rfl⟩ : syracuseStep 2310707 = 3466061) B3466061
theorem B1368643 : Blo 1368503 1368643 := bstep (se 1 (by rfl) ⟨1026482, by rfl⟩ : syracuseStep 1368643 = 2052965) B2052965
theorem B3080771 : Blo 1368503 3080771 := bstep (se 1 (by rfl) ⟨2310578, by rfl⟩ : syracuseStep 3080771 = 4621157) B4621157
theorem B1368659 : Blo 1368503 1368659 := bstep (se 1 (by rfl) ⟨1026494, by rfl⟩ : syracuseStep 1368659 = 2052989) B2052989
theorem B1368675 : Blo 1368503 1368675 := bstep (se 1 (by rfl) ⟨1026506, by rfl⟩ : syracuseStep 1368675 = 2053013) B2053013
theorem B1368691 : Blo 1368503 1368691 := bstep (se 1 (by rfl) ⟨1026518, by rfl⟩ : syracuseStep 1368691 = 2053037) B2053037
theorem B1540723 : Blo 1368503 1540723 := bstep (se 1 (by rfl) ⟨1155542, by rfl⟩ : syracuseStep 1540723 = 2311085) B2311085
theorem B1368707 : Blo 1368503 1368707 := bstep (se 1 (by rfl) ⟨1026530, by rfl⟩ : syracuseStep 1368707 = 2053061) B2053061
theorem B4620941 : Blo 1368503 4620941 := bstep (se 3 (by rfl) ⟨866426, by rfl⟩ : syracuseStep 4620941 = 1732853) B1732853
theorem B1368723 : Blo 1368503 1368723 := bstep (se 1 (by rfl) ⟨1026542, by rfl⟩ : syracuseStep 1368723 = 2053085) B2053085
theorem B1368739 : Blo 1368503 1368739 := bstep (se 1 (by rfl) ⟨1026554, by rfl⟩ : syracuseStep 1368739 = 2053109) B2053109
theorem B1368755 : Blo 1368503 1368755 := bstep (se 1 (by rfl) ⟨1026566, by rfl⟩ : syracuseStep 1368755 = 2053133) B2053133
theorem B2310835 : Blo 1368503 2310835 := bstep (se 1 (by rfl) ⟨1733126, by rfl⟩ : syracuseStep 2310835 = 3466253) B3466253
theorem B1368771 : Blo 1368503 1368771 := bstep (se 1 (by rfl) ⟨1026578, by rfl⟩ : syracuseStep 1368771 = 2053157) B2053157
theorem B4620995 : Blo 1368503 4620995 := bstep (se 1 (by rfl) ⟨3465746, by rfl⟩ : syracuseStep 4620995 = 6931493) B6931493
theorem B1368787 : Blo 1368503 1368787 := bstep (se 1 (by rfl) ⟨1026590, by rfl⟩ : syracuseStep 1368787 = 2053181) B2053181
theorem B4932323 : Blo 1368503 4932323 := bstep (se 1 (by rfl) ⟨3699242, by rfl⟩ : syracuseStep 4932323 = 7398485) B7398485
theorem B1368803 : Blo 1368503 1368803 := bstep (se 1 (by rfl) ⟨1026602, by rfl⟩ : syracuseStep 1368803 = 2053205) B2053205
theorem B1368819 : Blo 1368503 1368819 := bstep (se 1 (by rfl) ⟨1026614, by rfl⟩ : syracuseStep 1368819 = 2053229) B2053229
theorem B1368835 : Blo 1368503 1368835 := bstep (se 1 (by rfl) ⟨1026626, by rfl⟩ : syracuseStep 1368835 = 2053253) B2053253
theorem B1540867 : Blo 1368503 1540867 := bstep (se 1 (by rfl) ⟨1155650, by rfl⟩ : syracuseStep 1540867 = 2311301) B2311301
theorem B1368851 : Blo 1368503 1368851 := bstep (se 1 (by rfl) ⟨1026638, by rfl⟩ : syracuseStep 1368851 = 2053277) B2053277
theorem B1368867 : Blo 1368503 1368867 := bstep (se 1 (by rfl) ⟨1026650, by rfl⟩ : syracuseStep 1368867 = 2053301) B2053301
theorem B5202737 : Blo 1368503 5202737 := bstep (se 2 (by rfl) ⟨1951026, by rfl⟩ : syracuseStep 5202737 = 3902053) B3902053
theorem B1368883 : Blo 1368503 1368883 := bstep (se 1 (by rfl) ⟨1026662, by rfl⟩ : syracuseStep 1368883 = 2053325) B2053325
theorem B2310977 : Blo 1368503 2310977 := bstep (se 2 (by rfl) ⟨866616, by rfl⟩ : syracuseStep 2310977 = 1733233) B1733233
theorem B1368899 : Blo 1368503 1368899 := bstep (se 1 (by rfl) ⟨1026674, by rfl⟩ : syracuseStep 1368899 = 2053349) B2053349
theorem B4219715 : Blo 1368503 4219715 := bstep (se 1 (by rfl) ⟨3164786, by rfl⟩ : syracuseStep 4219715 = 6329573) B6329573
theorem B2081603 : Blo 1368503 2081603 := bstep (se 1 (by rfl) ⟨1561202, by rfl⟩ : syracuseStep 2081603 = 3122405) B3122405
theorem B3081041 : Blo 1368503 3081041 := bstep (se 2 (by rfl) ⟨1155390, by rfl⟩ : syracuseStep 3081041 = 2310781) B2310781
theorem B3900241 : Blo 1368503 3900241 := bstep (se 2 (by rfl) ⟨1462590, by rfl⟩ : syracuseStep 3900241 = 2925181) B2925181
theorem B1368915 : Blo 1368503 1368915 := bstep (se 1 (by rfl) ⟨1026686, by rfl⟩ : syracuseStep 1368915 = 2053373) B2053373
theorem B1368931 : Blo 1368503 1368931 := bstep (se 1 (by rfl) ⟨1026698, by rfl⟩ : syracuseStep 1368931 = 2053397) B2053397
theorem B3081059 : Blo 1368503 3081059 := bstep (se 1 (by rfl) ⟨2310794, by rfl⟩ : syracuseStep 3081059 = 4621589) B4621589
theorem B1368947 : Blo 1368503 1368947 := bstep (se 1 (by rfl) ⟨1026710, by rfl⟩ : syracuseStep 1368947 = 2053421) B2053421
theorem B1368963 : Blo 1368503 1368963 := bstep (se 1 (by rfl) ⟨1026722, by rfl⟩ : syracuseStep 1368963 = 2053445) B2053445
theorem B1368979 : Blo 1368503 1368979 := bstep (se 1 (by rfl) ⟨1026734, by rfl⟩ : syracuseStep 1368979 = 2053469) B2053469
theorem B1541011 : Blo 1368503 1541011 := bstep (se 1 (by rfl) ⟨1155758, by rfl⟩ : syracuseStep 1541011 = 2311517) B2311517
theorem B1368995 : Blo 1368503 1368995 := bstep (se 1 (by rfl) ⟨1026746, by rfl⟩ : syracuseStep 1368995 = 2053493) B2053493
theorem B1369011 : Blo 1368503 1369011 := bstep (se 1 (by rfl) ⟨1026758, by rfl⟩ : syracuseStep 1369011 = 2053517) B2053517
theorem B2311105 : Blo 1368503 2311105 := bstep (se 2 (by rfl) ⟨866664, by rfl⟩ : syracuseStep 2311105 = 1733329) B1733329
theorem B1369027 : Blo 1368503 1369027 := bstep (se 1 (by rfl) ⟨1026770, by rfl⟩ : syracuseStep 1369027 = 2053541) B2053541
theorem B4621265 : Blo 1368503 4621265 := bstep (se 2 (by rfl) ⟨1732974, by rfl⟩ : syracuseStep 4621265 = 3465949) B3465949
theorem B1369043 : Blo 1368503 1369043 := bstep (se 1 (by rfl) ⟨1026782, by rfl⟩ : syracuseStep 1369043 = 2053565) B2053565
theorem B1369059 : Blo 1368503 1369059 := bstep (se 1 (by rfl) ⟨1026794, by rfl⟩ : syracuseStep 1369059 = 2053589) B2053589
theorem B2311139 : Blo 1368503 2311139 := bstep (se 1 (by rfl) ⟨1733354, by rfl⟩ : syracuseStep 2311139 = 3466709) B3466709
theorem B1369075 : Blo 1368503 1369075 := bstep (se 1 (by rfl) ⟨1026806, by rfl⟩ : syracuseStep 1369075 = 2053613) B2053613
theorem B1369091 : Blo 1368503 1369091 := bstep (se 1 (by rfl) ⟨1026818, by rfl⟩ : syracuseStep 1369091 = 2053637) B2053637
theorem B1369107 : Blo 1368503 1369107 := bstep (se 1 (by rfl) ⟨1026830, by rfl⟩ : syracuseStep 1369107 = 2053661) B2053661
theorem B1369123 : Blo 1368503 1369123 := bstep (se 1 (by rfl) ⟨1026842, by rfl⟩ : syracuseStep 1369123 = 2053685) B2053685
theorem B1541155 : Blo 1368503 1541155 := bstep (se 1 (by rfl) ⟨1155866, by rfl⟩ : syracuseStep 1541155 = 2311733) B2311733
theorem B1369139 : Blo 1368503 1369139 := bstep (se 1 (by rfl) ⟨1026854, by rfl⟩ : syracuseStep 1369139 = 2053709) B2053709
theorem B1369155 : Blo 1368503 1369155 := bstep (se 1 (by rfl) ⟨1026866, by rfl⟩ : syracuseStep 1369155 = 2053733) B2053733
theorem B1369171 : Blo 1368503 1369171 := bstep (se 1 (by rfl) ⟨1026878, by rfl⟩ : syracuseStep 1369171 = 2053757) B2053757
theorem B1369187 : Blo 1368503 1369187 := bstep (se 1 (by rfl) ⟨1026890, by rfl⟩ : syracuseStep 1369187 = 2053781) B2053781
theorem B2311267 : Blo 1368503 2311267 := bstep (se 1 (by rfl) ⟨1733450, by rfl⟩ : syracuseStep 2311267 = 3466901) B3466901
theorem B97453169 : Blo 1368503 97453169 := bstep (se 2 (by rfl) ⟨36544938, by rfl⟩ : syracuseStep 97453169 = 73089877) B73089877
theorem B3081329 : Blo 1368503 3081329 := bstep (se 2 (by rfl) ⟨1155498, by rfl⟩ : syracuseStep 3081329 = 2310997) B2310997
theorem B1369203 : Blo 1368503 1369203 := bstep (se 1 (by rfl) ⟨1026902, by rfl⟩ : syracuseStep 1369203 = 2053805) B2053805
theorem B1369219 : Blo 1368503 1369219 := bstep (se 1 (by rfl) ⟨1026914, by rfl⟩ : syracuseStep 1369219 = 2053829) B2053829
theorem B3081347 : Blo 1368503 3081347 := bstep (se 1 (by rfl) ⟨2311010, by rfl⟩ : syracuseStep 3081347 = 4622021) B4622021
theorem B3466385 : Blo 1368503 3466385 := bstep (se 2 (by rfl) ⟨1299894, by rfl⟩ : syracuseStep 3466385 = 2599789) B2599789
theorem B1369235 : Blo 1368503 1369235 := bstep (se 1 (by rfl) ⟨1026926, by rfl⟩ : syracuseStep 1369235 = 2053853) B2053853
theorem B5137571 : Blo 1368503 5137571 := bstep (se 1 (by rfl) ⟨3853178, by rfl⟩ : syracuseStep 5137571 = 7706357) B7706357
theorem B1369251 : Blo 1368503 1369251 := bstep (se 1 (by rfl) ⟨1026938, by rfl⟩ : syracuseStep 1369251 = 2053877) B2053877
theorem B2598065 : Blo 1368503 2598065 := bstep (se 2 (by rfl) ⟨974274, by rfl⟩ : syracuseStep 2598065 = 1948549) B1948549
theorem B1369267 : Blo 1368503 1369267 := bstep (se 1 (by rfl) ⟨1026950, by rfl⟩ : syracuseStep 1369267 = 2053901) B2053901
theorem B1541299 : Blo 1368503 1541299 := bstep (se 1 (by rfl) ⟨1155974, by rfl⟩ : syracuseStep 1541299 = 2311949) B2311949
theorem B1369283 : Blo 1368503 1369283 := bstep (se 1 (by rfl) ⟨1026962, by rfl⟩ : syracuseStep 1369283 = 2053925) B2053925
theorem B3466435 : Blo 1368503 3466435 := bstep (se 1 (by rfl) ⟨2599826, by rfl⟩ : syracuseStep 3466435 = 5199653) B5199653
theorem B1369299 : Blo 1368503 1369299 := bstep (se 1 (by rfl) ⟨1026974, by rfl⟩ : syracuseStep 1369299 = 2053949) B2053949
theorem B1369315 : Blo 1368503 1369315 := bstep (se 1 (by rfl) ⟨1026986, by rfl⟩ : syracuseStep 1369315 = 2053973) B2053973
theorem B5932259 : Blo 1368503 5932259 := bstep (se 1 (by rfl) ⟨4449194, by rfl⟩ : syracuseStep 5932259 = 8898389) B8898389
theorem B2311409 : Blo 1368503 2311409 := bstep (se 2 (by rfl) ⟨866778, by rfl⟩ : syracuseStep 2311409 = 1733557) B1733557
theorem B1369331 : Blo 1368503 1369331 := bstep (se 1 (by rfl) ⟨1026998, by rfl⟩ : syracuseStep 1369331 = 2053997) B2053997
theorem B1369347 : Blo 1368503 1369347 := bstep (se 1 (by rfl) ⟨1027010, by rfl⟩ : syracuseStep 1369347 = 2054021) B2054021
theorem B1369363 : Blo 1368503 1369363 := bstep (se 1 (by rfl) ⟨1027022, by rfl⟩ : syracuseStep 1369363 = 2054045) B2054045
theorem B2344225 : Blo 1368503 2344225 := bstep (se 2 (by rfl) ⟨879084, by rfl⟩ : syracuseStep 2344225 = 1758169) B1758169
theorem B2082083 : Blo 1368503 2082083 := bstep (se 1 (by rfl) ⟨1561562, by rfl⟩ : syracuseStep 2082083 = 3123125) B3123125
theorem B1369379 : Blo 1368503 1369379 := bstep (se 1 (by rfl) ⟨1027034, by rfl⟩ : syracuseStep 1369379 = 2054069) B2054069
theorem B3515683 : Blo 1368503 3515683 := bstep (se 1 (by rfl) ⟨2636762, by rfl⟩ : syracuseStep 3515683 = 5273525) B5273525
theorem B1369395 : Blo 1368503 1369395 := bstep (se 1 (by rfl) ⟨1027046, by rfl⟩ : syracuseStep 1369395 = 2054093) B2054093
theorem B1369411 : Blo 1368503 1369411 := bstep (se 1 (by rfl) ⟨1027058, by rfl⟩ : syracuseStep 1369411 = 2054117) B2054117
theorem B1541443 : Blo 1368503 1541443 := bstep (se 1 (by rfl) ⟨1156082, by rfl⟩ : syracuseStep 1541443 = 2312165) B2312165
theorem B10396997 : Blo 1368503 10396997 := bstep (se 4 (by rfl) ⟨974718, by rfl⟩ : syracuseStep 10396997 = 1949437) B1949437
theorem B3466577 : Blo 1368503 3466577 := bstep (se 2 (by rfl) ⟨1299966, by rfl⟩ : syracuseStep 3466577 = 2599933) B2599933
theorem B1369427 : Blo 1368503 1369427 := bstep (se 1 (by rfl) ⟨1027070, by rfl⟩ : syracuseStep 1369427 = 2054141) B2054141
theorem B1369443 : Blo 1368503 1369443 := bstep (se 1 (by rfl) ⟨1027082, by rfl⟩ : syracuseStep 1369443 = 2054165) B2054165
theorem B2311537 : Blo 1368503 2311537 := bstep (se 2 (by rfl) ⟨866826, by rfl⟩ : syracuseStep 2311537 = 1733653) B1733653
theorem B1369459 : Blo 1368503 1369459 := bstep (se 1 (by rfl) ⟨1027094, by rfl⟩ : syracuseStep 1369459 = 2054189) B2054189
theorem B1369475 : Blo 1368503 1369475 := bstep (se 1 (by rfl) ⟨1027106, by rfl⟩ : syracuseStep 1369475 = 2054213) B2054213
theorem B16647565 : Blo 1368503 16647565 := bstep (se 3 (by rfl) ⟨3121418, by rfl⟩ : syracuseStep 16647565 = 6242837) B6242837
theorem B3081617 : Blo 1368503 3081617 := bstep (se 2 (by rfl) ⟨1155606, by rfl⟩ : syracuseStep 3081617 = 2311213) B2311213
theorem B1369491 : Blo 1368503 1369491 := bstep (se 1 (by rfl) ⟨1027118, by rfl⟩ : syracuseStep 1369491 = 2054237) B2054237
theorem B2311571 : Blo 1368503 2311571 := bstep (se 1 (by rfl) ⟨1733678, by rfl⟩ : syracuseStep 2311571 = 3467357) B3467357
theorem B1951123 : Blo 1368503 1951123 := bstep (se 1 (by rfl) ⟨1463342, by rfl⟩ : syracuseStep 1951123 = 2926685) B2926685
theorem B1369507 : Blo 1368503 1369507 := bstep (se 1 (by rfl) ⟨1027130, by rfl⟩ : syracuseStep 1369507 = 2054261) B2054261
theorem B3081635 : Blo 1368503 3081635 := bstep (se 1 (by rfl) ⟨2311226, by rfl⟩ : syracuseStep 3081635 = 4622453) B4622453
theorem B2926001 : Blo 1368503 2926001 := bstep (se 2 (by rfl) ⟨1097250, by rfl⟩ : syracuseStep 2926001 = 2194501) B2194501
theorem B1369523 : Blo 1368503 1369523 := bstep (se 1 (by rfl) ⟨1027142, by rfl⟩ : syracuseStep 1369523 = 2054285) B2054285
theorem B1369539 : Blo 1368503 1369539 := bstep (se 1 (by rfl) ⟨1027154, by rfl⟩ : syracuseStep 1369539 = 2054309) B2054309
theorem B2926019 : Blo 1368503 2926019 := bstep (se 1 (by rfl) ⟨2194514, by rfl⟩ : syracuseStep 2926019 = 4389029) B4389029
theorem B1369555 : Blo 1368503 1369555 := bstep (se 1 (by rfl) ⟨1027166, by rfl⟩ : syracuseStep 1369555 = 2054333) B2054333
theorem B1541587 : Blo 1368503 1541587 := bstep (se 1 (by rfl) ⟨1156190, by rfl⟩ : syracuseStep 1541587 = 2312381) B2312381
theorem B1369571 : Blo 1368503 1369571 := bstep (se 1 (by rfl) ⟨1027178, by rfl⟩ : syracuseStep 1369571 = 2054357) B2054357
theorem B4621805 : Blo 1368503 4621805 := bstep (se 3 (by rfl) ⟨866588, by rfl⟩ : syracuseStep 4621805 = 1733177) B1733177
theorem B1369587 : Blo 1368503 1369587 := bstep (se 1 (by rfl) ⟨1027190, by rfl⟩ : syracuseStep 1369587 = 2054381) B2054381
theorem B1369603 : Blo 1368503 1369603 := bstep (se 1 (by rfl) ⟨1027202, by rfl⟩ : syracuseStep 1369603 = 2054405) B2054405
theorem B9364997 : Blo 1368503 9364997 := bstep (se 4 (by rfl) ⟨877968, by rfl⟩ : syracuseStep 9364997 = 1755937) B1755937
theorem B1369619 : Blo 1368503 1369619 := bstep (se 1 (by rfl) ⟨1027214, by rfl⟩ : syracuseStep 1369619 = 2054429) B2054429
theorem B2311699 : Blo 1368503 2311699 := bstep (se 1 (by rfl) ⟨1733774, by rfl⟩ : syracuseStep 2311699 = 3467549) B3467549
theorem B4621859 : Blo 1368503 4621859 := bstep (se 1 (by rfl) ⟨3466394, by rfl⟩ : syracuseStep 4621859 = 6932789) B6932789
theorem B1369635 : Blo 1368503 1369635 := bstep (se 1 (by rfl) ⟨1027226, by rfl⟩ : syracuseStep 1369635 = 2054453) B2054453
theorem B8324657 : Blo 1368503 8324657 := bstep (se 2 (by rfl) ⟨3121746, by rfl⟩ : syracuseStep 8324657 = 6243493) B6243493
theorem B1369651 : Blo 1368503 1369651 := bstep (se 1 (by rfl) ⟨1027238, by rfl⟩ : syracuseStep 1369651 = 2054477) B2054477
theorem B1369667 : Blo 1368503 1369667 := bstep (se 1 (by rfl) ⟨1027250, by rfl⟩ : syracuseStep 1369667 = 2054501) B2054501
theorem B7505477 : Blo 1368503 7505477 := bstep (se 4 (by rfl) ⟨703638, by rfl⟩ : syracuseStep 7505477 = 1407277) B1407277
theorem B1369683 : Blo 1368503 1369683 := bstep (se 1 (by rfl) ⟨1027262, by rfl⟩ : syracuseStep 1369683 = 2054525) B2054525
theorem B1369699 : Blo 1368503 1369699 := bstep (se 1 (by rfl) ⟨1027274, by rfl⟩ : syracuseStep 1369699 = 2054549) B2054549
theorem B1541731 : Blo 1368503 1541731 := bstep (se 1 (by rfl) ⟨1156298, by rfl⟩ : syracuseStep 1541731 = 2312597) B2312597
theorem B1369715 : Blo 1368503 1369715 := bstep (se 1 (by rfl) ⟨1027286, by rfl⟩ : syracuseStep 1369715 = 2054573) B2054573
theorem B1369731 : Blo 1368503 1369731 := bstep (se 1 (by rfl) ⟨1027298, by rfl⟩ : syracuseStep 1369731 = 2054597) B2054597
theorem B7800461 : Blo 1368503 7800461 := bstep (se 3 (by rfl) ⟨1462586, by rfl⟩ : syracuseStep 7800461 = 2925173) B2925173
theorem B1369747 : Blo 1368503 1369747 := bstep (se 1 (by rfl) ⟨1027310, by rfl⟩ : syracuseStep 1369747 = 2054621) B2054621
theorem B2311841 : Blo 1368503 2311841 := bstep (se 2 (by rfl) ⟨866940, by rfl⟩ : syracuseStep 2311841 = 1733881) B1733881
theorem B1369763 : Blo 1368503 1369763 := bstep (se 1 (by rfl) ⟨1027322, by rfl⟩ : syracuseStep 1369763 = 2054645) B2054645
theorem B3081905 : Blo 1368503 3081905 := bstep (se 2 (by rfl) ⟨1155714, by rfl⟩ : syracuseStep 3081905 = 2311429) B2311429
theorem B1369779 : Blo 1368503 1369779 := bstep (se 1 (by rfl) ⟨1027334, by rfl⟩ : syracuseStep 1369779 = 2054669) B2054669
theorem B3081923 : Blo 1368503 3081923 := bstep (se 1 (by rfl) ⟨2311442, by rfl⟩ : syracuseStep 3081923 = 4622885) B4622885
theorem B1369795 : Blo 1368503 1369795 := bstep (se 1 (by rfl) ⟨1027346, by rfl⟩ : syracuseStep 1369795 = 2054693) B2054693
theorem B1369811 : Blo 1368503 1369811 := bstep (se 1 (by rfl) ⟨1027358, by rfl⟩ : syracuseStep 1369811 = 2054717) B2054717
theorem B1369827 : Blo 1368503 1369827 := bstep (se 1 (by rfl) ⟨1027370, by rfl⟩ : syracuseStep 1369827 = 2054741) B2054741
theorem B1369843 : Blo 1368503 1369843 := bstep (se 1 (by rfl) ⟨1027382, by rfl⟩ : syracuseStep 1369843 = 2054765) B2054765
theorem B1369859 : Blo 1368503 1369859 := bstep (se 1 (by rfl) ⟨1027394, by rfl⟩ : syracuseStep 1369859 = 2054789) B2054789
theorem B5850893 : Blo 1368503 5850893 := bstep (se 3 (by rfl) ⟨1097042, by rfl⟩ : syracuseStep 5850893 = 2194085) B2194085
theorem B1369875 : Blo 1368503 1369875 := bstep (se 1 (by rfl) ⟨1027406, by rfl⟩ : syracuseStep 1369875 = 2054813) B2054813
theorem B2311969 : Blo 1368503 2311969 := bstep (se 2 (by rfl) ⟨866988, by rfl⟩ : syracuseStep 2311969 = 1733977) B1733977
theorem B1369891 : Blo 1368503 1369891 := bstep (se 1 (by rfl) ⟨1027418, by rfl⟩ : syracuseStep 1369891 = 2054837) B2054837
theorem B4622129 : Blo 1368503 4622129 := bstep (se 2 (by rfl) ⟨1733298, by rfl⟩ : syracuseStep 4622129 = 3466597) B3466597
theorem B1369907 : Blo 1368503 1369907 := bstep (se 1 (by rfl) ⟨1027430, by rfl⟩ : syracuseStep 1369907 = 2054861) B2054861
theorem B26330933 : Blo 1368503 26330933 := bstep (se 5 (by rfl) ⟨1234262, by rfl⟩ : syracuseStep 26330933 = 2468525) B2468525
theorem B1369923 : Blo 1368503 1369923 := bstep (se 1 (by rfl) ⟨1027442, by rfl⟩ : syracuseStep 1369923 = 2054885) B2054885
theorem B2312003 : Blo 1368503 2312003 := bstep (se 1 (by rfl) ⟨1734002, by rfl⟩ : syracuseStep 2312003 = 3468005) B3468005
theorem B1369939 : Blo 1368503 1369939 := bstep (se 1 (by rfl) ⟨1027454, by rfl⟩ : syracuseStep 1369939 = 2054909) B2054909
theorem B1369955 : Blo 1368503 1369955 := bstep (se 1 (by rfl) ⟨1027466, by rfl⟩ : syracuseStep 1369955 = 2054933) B2054933
theorem B10405745 : Blo 1368503 10405745 := bstep (se 2 (by rfl) ⟨3902154, by rfl⟩ : syracuseStep 10405745 = 7804309) B7804309
theorem B1369971 : Blo 1368503 1369971 := bstep (se 1 (by rfl) ⟨1027478, by rfl⟩ : syracuseStep 1369971 = 2054957) B2054957
theorem B1369987 : Blo 1368503 1369987 := bstep (se 1 (by rfl) ⟨1027490, by rfl⟩ : syracuseStep 1369987 = 2054981) B2054981
theorem B1370003 : Blo 1368503 1370003 := bstep (se 1 (by rfl) ⟨1027502, by rfl⟩ : syracuseStep 1370003 = 2055005) B2055005
theorem B1370019 : Blo 1368503 1370019 := bstep (se 1 (by rfl) ⟨1027514, by rfl⟩ : syracuseStep 1370019 = 2055029) B2055029
theorem B4384685 : Blo 1368503 4384685 := bstep (se 3 (by rfl) ⟨822128, by rfl⟩ : syracuseStep 4384685 = 1644257) B1644257
theorem B1370035 : Blo 1368503 1370035 := bstep (se 1 (by rfl) ⟨1027526, by rfl⟩ : syracuseStep 1370035 = 2055053) B2055053
theorem B1370051 : Blo 1368503 1370051 := bstep (se 1 (by rfl) ⟨1027538, by rfl⟩ : syracuseStep 1370051 = 2055077) B2055077
theorem B2312131 : Blo 1368503 2312131 := bstep (se 1 (by rfl) ⟨1734098, by rfl⟩ : syracuseStep 2312131 = 3468197) B3468197
theorem B3082193 : Blo 1368503 3082193 := bstep (se 2 (by rfl) ⟨1155822, by rfl⟩ : syracuseStep 3082193 = 2311645) B2311645
theorem B1370067 : Blo 1368503 1370067 := bstep (se 1 (by rfl) ⟨1027550, by rfl⟩ : syracuseStep 1370067 = 2055101) B2055101
theorem B3082211 : Blo 1368503 3082211 := bstep (se 1 (by rfl) ⟨2311658, by rfl⟩ : syracuseStep 3082211 = 4623317) B4623317
theorem B1370083 : Blo 1368503 1370083 := bstep (se 1 (by rfl) ⟨1027562, by rfl⟩ : syracuseStep 1370083 = 2055125) B2055125
theorem B6932465 : Blo 1368503 6932465 := bstep (se 2 (by rfl) ⟨2599674, by rfl⟩ : syracuseStep 6932465 = 5199349) B5199349
theorem B1370099 : Blo 1368503 1370099 := bstep (se 1 (by rfl) ⟨1027574, by rfl⟩ : syracuseStep 1370099 = 2055149) B2055149
theorem B1370115 : Blo 1368503 1370115 := bstep (se 1 (by rfl) ⟨1027586, by rfl⟩ : syracuseStep 1370115 = 2055173) B2055173
theorem B1370131 : Blo 1368503 1370131 := bstep (se 1 (by rfl) ⟨1027598, by rfl⟩ : syracuseStep 1370131 = 2055197) B2055197
theorem B1370147 : Blo 1368503 1370147 := bstep (se 1 (by rfl) ⟨1027610, by rfl⟩ : syracuseStep 1370147 = 2055221) B2055221
theorem B2598961 : Blo 1368503 2598961 := bstep (se 2 (by rfl) ⟨974610, by rfl⟩ : syracuseStep 2598961 = 1949221) B1949221
theorem B6580273 : Blo 1368503 6580273 := bstep (se 2 (by rfl) ⟨2467602, by rfl⟩ : syracuseStep 6580273 = 4935205) B4935205
theorem B1370163 : Blo 1368503 1370163 := bstep (se 1 (by rfl) ⟨1027622, by rfl⟩ : syracuseStep 1370163 = 2055245) B2055245
theorem B1370179 : Blo 1368503 1370179 := bstep (se 1 (by rfl) ⟨1027634, by rfl⟩ : syracuseStep 1370179 = 2055269) B2055269
theorem B3901517 : Blo 1368503 3901517 := bstep (se 3 (by rfl) ⟨731534, by rfl⟩ : syracuseStep 3901517 = 1463069) B1463069
theorem B1370195 : Blo 1368503 1370195 := bstep (se 1 (by rfl) ⟨1027646, by rfl⟩ : syracuseStep 1370195 = 2055293) B2055293
theorem B2312273 : Blo 1368503 2312273 := bstep (se 2 (by rfl) ⟨867102, by rfl⟩ : syracuseStep 2312273 = 1734205) B1734205
theorem B3123299 : Blo 1368503 3123299 := bstep (se 1 (by rfl) ⟨2342474, by rfl⟩ : syracuseStep 3123299 = 4684949) B4684949
theorem B1370211 : Blo 1368503 1370211 := bstep (se 1 (by rfl) ⟨1027658, by rfl⟩ : syracuseStep 1370211 = 2055317) B2055317
theorem B1370227 : Blo 1368503 1370227 := bstep (se 1 (by rfl) ⟨1027670, by rfl⟩ : syracuseStep 1370227 = 2055341) B2055341
theorem B1370243 : Blo 1368503 1370243 := bstep (se 1 (by rfl) ⟨1027682, by rfl⟩ : syracuseStep 1370243 = 2055365) B2055365
theorem B1370259 : Blo 1368503 1370259 := bstep (se 1 (by rfl) ⟨1027694, by rfl⟩ : syracuseStep 1370259 = 2055389) B2055389
theorem B1370275 : Blo 1368503 1370275 := bstep (se 1 (by rfl) ⟨1027706, by rfl⟩ : syracuseStep 1370275 = 2055413) B2055413
theorem B1370291 : Blo 1368503 1370291 := bstep (se 1 (by rfl) ⟨1027718, by rfl⟩ : syracuseStep 1370291 = 2055437) B2055437
theorem B1370307 : Blo 1368503 1370307 := bstep (se 1 (by rfl) ⟨1027730, by rfl⟩ : syracuseStep 1370307 = 2055461) B2055461
theorem B2599121 : Blo 1368503 2599121 := bstep (se 2 (by rfl) ⟨974670, by rfl⟩ : syracuseStep 2599121 = 1949341) B1949341
theorem B2312401 : Blo 1368503 2312401 := bstep (se 2 (by rfl) ⟨867150, by rfl⟩ : syracuseStep 2312401 = 1734301) B1734301
theorem B1370323 : Blo 1368503 1370323 := bstep (se 1 (by rfl) ⟨1027742, by rfl⟩ : syracuseStep 1370323 = 2055485) B2055485
theorem B1370339 : Blo 1368503 1370339 := bstep (se 1 (by rfl) ⟨1027754, by rfl⟩ : syracuseStep 1370339 = 2055509) B2055509
theorem B3082481 : Blo 1368503 3082481 := bstep (se 2 (by rfl) ⟨1155930, by rfl⟩ : syracuseStep 3082481 = 2311861) B2311861
theorem B2312435 : Blo 1368503 2312435 := bstep (se 1 (by rfl) ⟨1734326, by rfl⟩ : syracuseStep 2312435 = 3468653) B3468653
theorem B1370355 : Blo 1368503 1370355 := bstep (se 1 (by rfl) ⟨1027766, by rfl⟩ : syracuseStep 1370355 = 2055533) B2055533
theorem B3082499 : Blo 1368503 3082499 := bstep (se 1 (by rfl) ⟨2311874, by rfl⟩ : syracuseStep 3082499 = 4623749) B4623749
theorem B3901699 : Blo 1368503 3901699 := bstep (se 1 (by rfl) ⟨2926274, by rfl⟩ : syracuseStep 3901699 = 5852549) B5852549
theorem B1370371 : Blo 1368503 1370371 := bstep (se 1 (by rfl) ⟨1027778, by rfl⟩ : syracuseStep 1370371 = 2055557) B2055557
theorem B1370387 : Blo 1368503 1370387 := bstep (se 1 (by rfl) ⟨1027790, by rfl⟩ : syracuseStep 1370387 = 2055581) B2055581
theorem B1370403 : Blo 1368503 1370403 := bstep (se 1 (by rfl) ⟨1027802, by rfl⟩ : syracuseStep 1370403 = 2055605) B2055605
theorem B3467569 : Blo 1368503 3467569 := bstep (se 2 (by rfl) ⟨1300338, by rfl⟩ : syracuseStep 3467569 = 2600677) B2600677
theorem B3901745 : Blo 1368503 3901745 := bstep (se 2 (by rfl) ⟨1463154, by rfl⟩ : syracuseStep 3901745 = 2926309) B2926309
theorem B1370419 : Blo 1368503 1370419 := bstep (se 1 (by rfl) ⟨1027814, by rfl⟩ : syracuseStep 1370419 = 2055629) B2055629
theorem B1370435 : Blo 1368503 1370435 := bstep (se 1 (by rfl) ⟨1027826, by rfl⟩ : syracuseStep 1370435 = 2055653) B2055653
theorem B4622669 : Blo 1368503 4622669 := bstep (se 3 (by rfl) ⟨866750, by rfl⟩ : syracuseStep 4622669 = 1733501) B1733501
theorem B5343565 : Blo 1368503 5343565 := bstep (se 3 (by rfl) ⟨1001918, by rfl⟩ : syracuseStep 5343565 = 2003837) B2003837
theorem B1370451 : Blo 1368503 1370451 := bstep (se 1 (by rfl) ⟨1027838, by rfl⟩ : syracuseStep 1370451 = 2055677) B2055677
theorem B1370467 : Blo 1368503 1370467 := bstep (se 1 (by rfl) ⟨1027850, by rfl⟩ : syracuseStep 1370467 = 2055701) B2055701
theorem B2312563 : Blo 1368503 2312563 := bstep (se 1 (by rfl) ⟨1734422, by rfl⟩ : syracuseStep 2312563 = 3468845) B3468845
theorem B1370483 : Blo 1368503 1370483 := bstep (se 1 (by rfl) ⟨1027862, by rfl⟩ : syracuseStep 1370483 = 2055725) B2055725
theorem B4622723 : Blo 1368503 4622723 := bstep (se 1 (by rfl) ⟨3467042, by rfl⟩ : syracuseStep 4622723 = 6934085) B6934085
theorem B1370499 : Blo 1368503 1370499 := bstep (se 1 (by rfl) ⟨1027874, by rfl⟩ : syracuseStep 1370499 = 2055749) B2055749
theorem B2312705 : Blo 1368503 2312705 := bstep (se 2 (by rfl) ⟨867264, by rfl⟩ : syracuseStep 2312705 = 1734529) B1734529
theorem B3082769 : Blo 1368503 3082769 := bstep (se 2 (by rfl) ⟨1156038, by rfl⟩ : syracuseStep 3082769 = 2312077) B2312077
theorem B3082787 : Blo 1368503 3082787 := bstep (se 1 (by rfl) ⟨2312090, by rfl⟩ : syracuseStep 3082787 = 4624181) B4624181
theorem B7801393 : Blo 1368503 7801393 := bstep (se 2 (by rfl) ⟨2925522, by rfl⟩ : syracuseStep 7801393 = 5851045) B5851045
theorem B3467843 : Blo 1368503 3467843 := bstep (se 1 (by rfl) ⟨2600882, by rfl⟩ : syracuseStep 3467843 = 5201765) B5201765
theorem B2599523 : Blo 1368503 2599523 := bstep (se 1 (by rfl) ⟨1949642, by rfl⟩ : syracuseStep 2599523 = 3899285) B3899285
theorem B2468483 : Blo 1368503 2468483 := bstep (se 1 (by rfl) ⟨1851362, by rfl⟩ : syracuseStep 2468483 = 3702725) B3702725
theorem B4622993 : Blo 1368503 4622993 := bstep (se 2 (by rfl) ⟨1733622, by rfl⟩ : syracuseStep 4622993 = 3467245) B3467245
theorem B2468497 : Blo 1368503 2468497 := bstep (se 2 (by rfl) ⟨925686, by rfl⟩ : syracuseStep 2468497 = 1851373) B1851373
theorem B4164301 : Blo 1368503 4164301 := bstep (se 3 (by rfl) ⟨780806, by rfl⟩ : syracuseStep 4164301 = 1561613) B1561613
theorem B3468035 : Blo 1368503 3468035 := bstep (se 1 (by rfl) ⟨2601026, by rfl⟩ : syracuseStep 3468035 = 5202053) B5202053
theorem B2468657 : Blo 1368503 2468657 := bstep (se 2 (by rfl) ⟨925746, by rfl⟩ : syracuseStep 2468657 = 1851493) B1851493
theorem B3083057 : Blo 1368503 3083057 := bstep (se 2 (by rfl) ⟨1156146, by rfl⟩ : syracuseStep 3083057 = 2312293) B2312293
theorem B3083075 : Blo 1368503 3083075 := bstep (se 1 (by rfl) ⟨2312306, by rfl⟩ : syracuseStep 3083075 = 4624613) B4624613
theorem B5196707 : Blo 1368503 5196707 := bstep (se 1 (by rfl) ⟨3897530, by rfl⟩ : syracuseStep 5196707 = 7795061) B7795061
theorem B11693069 : Blo 1368503 11693069 := bstep (se 3 (by rfl) ⟨2192450, by rfl⟩ : syracuseStep 11693069 = 4384901) B4384901
theorem B3083345 : Blo 1368503 3083345 := bstep (se 2 (by rfl) ⟨1156254, by rfl⟩ : syracuseStep 3083345 = 2312509) B2312509
theorem B3083363 : Blo 1368503 3083363 := bstep (se 1 (by rfl) ⟨2312522, by rfl⟩ : syracuseStep 3083363 = 4625045) B4625045
theorem B8768675 : Blo 1368503 8768675 := bstep (se 1 (by rfl) ⟨6576506, by rfl⟩ : syracuseStep 8768675 = 13153013) B13153013
theorem B4623533 : Blo 1368503 4623533 := bstep (se 3 (by rfl) ⟨866912, by rfl⟩ : syracuseStep 4623533 = 1733825) B1733825
theorem B4623587 : Blo 1368503 4623587 := bstep (se 1 (by rfl) ⟨3467690, by rfl⟩ : syracuseStep 4623587 = 6935381) B6935381
theorem B63253781 : Blo 1368503 63253781 := bstep (se 6 (by rfl) ⟨1482510, by rfl⟩ : syracuseStep 63253781 = 2965021) B2965021
theorem B3083633 : Blo 1368503 3083633 := bstep (se 2 (by rfl) ⟨1156362, by rfl⟩ : syracuseStep 3083633 = 2312725) B2312725
theorem B6933923 : Blo 1368503 6933923 := bstep (se 1 (by rfl) ⟨5200442, by rfl⟩ : syracuseStep 6933923 = 10400885) B10400885
theorem B2600419 : Blo 1368503 2600419 := bstep (se 1 (by rfl) ⟨1950314, by rfl⟩ : syracuseStep 2600419 = 3900629) B3900629
theorem B9375203 : Blo 1368503 9375203 := bstep (se 1 (by rfl) ⟨7031402, by rfl⟩ : syracuseStep 9375203 = 14062805) B14062805
theorem B4623857 : Blo 1368503 4623857 := bstep (se 2 (by rfl) ⟨1733946, by rfl⟩ : syracuseStep 4623857 = 3467893) B3467893
theorem B1732099 : Blo 1368503 1732099 := bstep (se 1 (by rfl) ⟨1299074, by rfl⟩ : syracuseStep 1732099 = 2598149) B2598149
theorem B1732195 : Blo 1368503 1732195 := bstep (se 1 (by rfl) ⟨1299146, by rfl⟩ : syracuseStep 1732195 = 2598293) B2598293
theorem B2600579 : Blo 1368503 2600579 := bstep (se 1 (by rfl) ⟨1950434, by rfl⟩ : syracuseStep 2600579 = 3900869) B3900869
theorem B1461907 : Blo 1368503 1461907 := bstep (se 1 (by rfl) ⟨1096430, by rfl⟩ : syracuseStep 1461907 = 2192861) B2192861
theorem B3468977 : Blo 1368503 3468977 := bstep (se 2 (by rfl) ⟨1300866, by rfl⟩ : syracuseStep 3468977 = 2601733) B2601733
theorem B3469027 : Blo 1368503 3469027 := bstep (se 1 (by rfl) ⟨2601770, by rfl⟩ : syracuseStep 3469027 = 5203541) B5203541
theorem B4935437 : Blo 1368503 4935437 := bstep (se 3 (by rfl) ⟨925394, by rfl⟩ : syracuseStep 4935437 = 1850789) B1850789
theorem B3288899 : Blo 1368503 3288899 := bstep (se 1 (by rfl) ⟨2466674, by rfl⟩ : syracuseStep 3288899 = 4933349) B4933349
theorem B3125105 : Blo 1368503 3125105 := bstep (se 2 (by rfl) ⟨1171914, by rfl⟩ : syracuseStep 3125105 = 2343829) B2343829
theorem B5197709 : Blo 1368503 5197709 := bstep (se 3 (by rfl) ⟨974570, by rfl⟩ : syracuseStep 5197709 = 1949141) B1949141
theorem B7794629 : Blo 1368503 7794629 := bstep (se 4 (by rfl) ⟨730746, by rfl⟩ : syracuseStep 7794629 = 1461493) B1461493
theorem B7802851 : Blo 1368503 7802851 := bstep (se 1 (by rfl) ⟨5852138, by rfl⟩ : syracuseStep 7802851 = 11704277) B11704277
theorem B4624397 : Blo 1368503 4624397 := bstep (se 3 (by rfl) ⟨867074, by rfl⟩ : syracuseStep 4624397 = 1734149) B1734149
theorem B4681745 : Blo 1368503 4681745 := bstep (se 2 (by rfl) ⟨1755654, by rfl⟩ : syracuseStep 4681745 = 3511309) B3511309
theorem B1667123 : Blo 1368503 1667123 := bstep (se 1 (by rfl) ⟨1250342, by rfl⟩ : syracuseStep 1667123 = 2500685) B2500685
theorem B4624451 : Blo 1368503 4624451 := bstep (se 1 (by rfl) ⟨3468338, by rfl⟩ : syracuseStep 4624451 = 6936677) B6936677
theorem B1732691 : Blo 1368503 1732691 := bstep (se 1 (by rfl) ⟨1299518, by rfl⟩ : syracuseStep 1732691 = 2599037) B2599037
theorem B6934733 : Blo 1368503 6934733 := bstep (se 3 (by rfl) ⟨1300262, by rfl⟩ : syracuseStep 6934733 = 2600525) B2600525
theorem B1462531 : Blo 1368503 1462531 := bstep (se 1 (by rfl) ⟨1096898, by rfl⟩ : syracuseStep 1462531 = 2193797) B2193797
theorem B4624721 : Blo 1368503 4624721 := bstep (se 2 (by rfl) ⟨1734270, by rfl⟩ : syracuseStep 4624721 = 3468541) B3468541
theorem B1388899 : Blo 1368503 1388899 := bstep (se 1 (by rfl) ⟨1041674, by rfl⟩ : syracuseStep 1388899 = 2083349) B2083349
theorem B1560979 : Blo 1368503 1560979 := bstep (se 1 (by rfl) ⟨1170734, by rfl⟩ : syracuseStep 1560979 = 2341469) B2341469
theorem B7803377 : Blo 1368503 7803377 := bstep (se 2 (by rfl) ⟨2926266, by rfl⟩ : syracuseStep 7803377 = 5852533) B5852533
theorem B2052755 : Blo 1368503 2052755 := bstep (se 1 (by rfl) ⟨1539566, by rfl⟩ : syracuseStep 2052755 = 3079133) B3079133
theorem B1667747 : Blo 1368503 1667747 := bstep (se 1 (by rfl) ⟨1250810, by rfl⟩ : syracuseStep 1667747 = 2501621) B2501621
theorem B2052785 : Blo 1368503 2052785 := bstep (se 2 (by rfl) ⟨769794, by rfl⟩ : syracuseStep 2052785 = 1539589) B1539589
theorem B2601649 : Blo 1368503 2601649 := bstep (se 2 (by rfl) ⟨975618, by rfl⟩ : syracuseStep 2601649 = 1951237) B1951237
theorem B2052803 : Blo 1368503 2052803 := bstep (se 1 (by rfl) ⟨1539602, by rfl⟩ : syracuseStep 2052803 = 3079205) B3079205
theorem B2052833 : Blo 1368503 2052833 := bstep (se 2 (by rfl) ⟨769812, by rfl⟩ : syracuseStep 2052833 = 1539625) B1539625
theorem B2052851 : Blo 1368503 2052851 := bstep (se 1 (by rfl) ⟨1539638, by rfl⟩ : syracuseStep 2052851 = 3079277) B3079277
theorem B2052881 : Blo 1368503 2052881 := bstep (se 2 (by rfl) ⟨769830, by rfl⟩ : syracuseStep 2052881 = 1539661) B1539661
theorem B1733395 : Blo 1368503 1733395 := bstep (se 1 (by rfl) ⟨1300046, by rfl⟩ : syracuseStep 1733395 = 2600093) B2600093
theorem B2052899 : Blo 1368503 2052899 := bstep (se 1 (by rfl) ⟨1539674, by rfl⟩ : syracuseStep 2052899 = 3079349) B3079349
theorem B2052929 : Blo 1368503 2052929 := bstep (se 2 (by rfl) ⟨769848, by rfl⟩ : syracuseStep 2052929 = 1539697) B1539697
theorem B2052947 : Blo 1368503 2052947 := bstep (se 1 (by rfl) ⟨1539710, by rfl⟩ : syracuseStep 2052947 = 3079421) B3079421
theorem B4625261 : Blo 1368503 4625261 := bstep (se 3 (by rfl) ⟨867236, by rfl⟩ : syracuseStep 4625261 = 1734473) B1734473
theorem B2052977 : Blo 1368503 2052977 := bstep (se 2 (by rfl) ⟨769866, by rfl⟩ : syracuseStep 2052977 = 1539733) B1539733
theorem B1733491 : Blo 1368503 1733491 := bstep (se 1 (by rfl) ⟨1300118, by rfl⟩ : syracuseStep 1733491 = 2600237) B2600237
theorem B2052995 : Blo 1368503 2052995 := bstep (se 1 (by rfl) ⟨1539746, by rfl⟩ : syracuseStep 2052995 = 3079493) B3079493
theorem B2053025 : Blo 1368503 2053025 := bstep (se 2 (by rfl) ⟨769884, by rfl⟩ : syracuseStep 2053025 = 1539769) B1539769
theorem B4625315 : Blo 1368503 4625315 := bstep (se 1 (by rfl) ⟨3468986, by rfl⟩ : syracuseStep 4625315 = 6937973) B6937973
theorem B2053043 : Blo 1368503 2053043 := bstep (se 1 (by rfl) ⟨1539782, by rfl⟩ : syracuseStep 2053043 = 3079565) B3079565
theorem B15610805 : Blo 1368503 15610805 := bstep (se 5 (by rfl) ⟨731756, by rfl⟩ : syracuseStep 15610805 = 1463513) B1463513
theorem B2053073 : Blo 1368503 2053073 := bstep (se 2 (by rfl) ⟨769902, by rfl⟩ : syracuseStep 2053073 = 1539805) B1539805
theorem B2053091 : Blo 1368503 2053091 := bstep (se 1 (by rfl) ⟨1539818, by rfl⟩ : syracuseStep 2053091 = 3079637) B3079637
theorem B4510691 : Blo 1368503 4510691 := bstep (se 1 (by rfl) ⟨3383018, by rfl⟩ : syracuseStep 4510691 = 6766037) B6766037
theorem B2053121 : Blo 1368503 2053121 := bstep (se 2 (by rfl) ⟨769920, by rfl⟩ : syracuseStep 2053121 = 1539841) B1539841
theorem B3290129 : Blo 1368503 3290129 := bstep (se 2 (by rfl) ⟨1233798, by rfl⟩ : syracuseStep 3290129 = 2467597) B2467597
theorem B2053139 : Blo 1368503 2053139 := bstep (se 1 (by rfl) ⟨1539854, by rfl⟩ : syracuseStep 2053139 = 3079709) B3079709
theorem B2053169 : Blo 1368503 2053169 := bstep (se 2 (by rfl) ⟨769938, by rfl⟩ : syracuseStep 2053169 = 1539877) B1539877
theorem B2053187 : Blo 1368503 2053187 := bstep (se 1 (by rfl) ⟨1539890, by rfl⟩ : syracuseStep 2053187 = 3079781) B3079781
theorem B2053217 : Blo 1368503 2053217 := bstep (se 2 (by rfl) ⟨769956, by rfl⟩ : syracuseStep 2053217 = 1539913) B1539913
theorem B2053235 : Blo 1368503 2053235 := bstep (se 1 (by rfl) ⟨1539926, by rfl⟩ : syracuseStep 2053235 = 3079853) B3079853
theorem B2053265 : Blo 1368503 2053265 := bstep (se 2 (by rfl) ⟨769974, by rfl⟩ : syracuseStep 2053265 = 1539949) B1539949
theorem B2053283 : Blo 1368503 2053283 := bstep (se 1 (by rfl) ⟨1539962, by rfl⟩ : syracuseStep 2053283 = 3079925) B3079925
theorem B4388003 : Blo 1368503 4388003 := bstep (se 1 (by rfl) ⟨3291002, by rfl⟩ : syracuseStep 4388003 = 6582005) B6582005
theorem B2053313 : Blo 1368503 2053313 := bstep (se 2 (by rfl) ⟨769992, by rfl⟩ : syracuseStep 2053313 = 1539985) B1539985
theorem B2053331 : Blo 1368503 2053331 := bstep (se 1 (by rfl) ⟨1539998, by rfl⟩ : syracuseStep 2053331 = 3079997) B3079997
theorem B2053361 : Blo 1368503 2053361 := bstep (se 2 (by rfl) ⟨770010, by rfl⟩ : syracuseStep 2053361 = 1540021) B1540021
theorem B2053379 : Blo 1368503 2053379 := bstep (se 1 (by rfl) ⟨1540034, by rfl⟩ : syracuseStep 2053379 = 3080069) B3080069
theorem B2053409 : Blo 1368503 2053409 := bstep (se 2 (by rfl) ⟨770028, by rfl⟩ : syracuseStep 2053409 = 1540057) B1540057
theorem B2053427 : Blo 1368503 2053427 := bstep (se 1 (by rfl) ⟨1540070, by rfl⟩ : syracuseStep 2053427 = 3080141) B3080141
theorem B2192707 : Blo 1368503 2192707 := bstep (se 1 (by rfl) ⟨1644530, by rfl⟩ : syracuseStep 2192707 = 3289061) B3289061
theorem B4683089 : Blo 1368503 4683089 := bstep (se 2 (by rfl) ⟨1756158, by rfl⟩ : syracuseStep 4683089 = 3512317) B3512317
theorem B2053457 : Blo 1368503 2053457 := bstep (se 2 (by rfl) ⟨770046, by rfl⟩ : syracuseStep 2053457 = 1540093) B1540093
theorem B2053475 : Blo 1368503 2053475 := bstep (se 1 (by rfl) ⟨1540106, by rfl⟩ : syracuseStep 2053475 = 3080213) B3080213
theorem B1733987 : Blo 1368503 1733987 := bstep (se 1 (by rfl) ⟨1300490, by rfl⟩ : syracuseStep 1733987 = 2600981) B2600981
theorem B2192753 : Blo 1368503 2192753 := bstep (se 2 (by rfl) ⟨822282, by rfl⟩ : syracuseStep 2192753 = 1644565) B1644565
theorem B2053505 : Blo 1368503 2053505 := bstep (se 2 (by rfl) ⟨770064, by rfl⟩ : syracuseStep 2053505 = 1540129) B1540129
theorem B2053523 : Blo 1368503 2053523 := bstep (se 1 (by rfl) ⟨1540142, by rfl⟩ : syracuseStep 2053523 = 3080285) B3080285
theorem B2774449 : Blo 1368503 2774449 := bstep (se 2 (by rfl) ⟨1040418, by rfl⟩ : syracuseStep 2774449 = 2080837) B2080837
theorem B2053553 : Blo 1368503 2053553 := bstep (se 2 (by rfl) ⟨770082, by rfl⟩ : syracuseStep 2053553 = 1540165) B1540165
theorem B3659185 : Blo 1368503 3659185 := bstep (se 2 (by rfl) ⟨1372194, by rfl⟩ : syracuseStep 3659185 = 2744389) B2744389
theorem B2053571 : Blo 1368503 2053571 := bstep (se 1 (by rfl) ⟨1540178, by rfl⟩ : syracuseStep 2053571 = 3080357) B3080357
theorem B2053601 : Blo 1368503 2053601 := bstep (se 2 (by rfl) ⟨770100, by rfl⟩ : syracuseStep 2053601 = 1540201) B1540201
theorem B2053619 : Blo 1368503 2053619 := bstep (se 1 (by rfl) ⟨1540214, by rfl⟩ : syracuseStep 2053619 = 3080429) B3080429
theorem B2053649 : Blo 1368503 2053649 := bstep (se 2 (by rfl) ⟨770118, by rfl⟩ : syracuseStep 2053649 = 1540237) B1540237
theorem B2053667 : Blo 1368503 2053667 := bstep (se 1 (by rfl) ⟨1540250, by rfl⟩ : syracuseStep 2053667 = 3080501) B3080501
theorem B1668643 : Blo 1368503 1668643 := bstep (se 1 (by rfl) ⟨1251482, by rfl⟩ : syracuseStep 1668643 = 2502965) B2502965
theorem B2053697 : Blo 1368503 2053697 := bstep (se 2 (by rfl) ⟨770136, by rfl⟩ : syracuseStep 2053697 = 1540273) B1540273
theorem B2053715 : Blo 1368503 2053715 := bstep (se 1 (by rfl) ⟨1540286, by rfl⟩ : syracuseStep 2053715 = 3080573) B3080573
theorem B2053745 : Blo 1368503 2053745 := bstep (se 2 (by rfl) ⟨770154, by rfl⟩ : syracuseStep 2053745 = 1540309) B1540309
theorem B2053763 : Blo 1368503 2053763 := bstep (se 1 (by rfl) ⟨1540322, by rfl⟩ : syracuseStep 2053763 = 3080645) B3080645
theorem B6583949 : Blo 1368503 6583949 := bstep (se 3 (by rfl) ⟨1234490, by rfl⟩ : syracuseStep 6583949 = 2468981) B2468981
theorem B2053793 : Blo 1368503 2053793 := bstep (se 2 (by rfl) ⟨770172, by rfl⟩ : syracuseStep 2053793 = 1540345) B1540345
theorem B2053811 : Blo 1368503 2053811 := bstep (se 1 (by rfl) ⟨1540358, by rfl⟩ : syracuseStep 2053811 = 3080717) B3080717
theorem B2053841 : Blo 1368503 2053841 := bstep (se 2 (by rfl) ⟨770190, by rfl⟩ : syracuseStep 2053841 = 1540381) B1540381
theorem B2053859 : Blo 1368503 2053859 := bstep (se 1 (by rfl) ⟨1540394, by rfl⟩ : syracuseStep 2053859 = 3080789) B3080789
theorem B2053889 : Blo 1368503 2053889 := bstep (se 2 (by rfl) ⟨770208, by rfl⟩ : syracuseStep 2053889 = 1540417) B1540417
theorem B2053907 : Blo 1368503 2053907 := bstep (se 1 (by rfl) ⟨1540430, by rfl⟩ : syracuseStep 2053907 = 3080861) B3080861
theorem B2053937 : Blo 1368503 2053937 := bstep (se 2 (by rfl) ⟨770226, by rfl⟩ : syracuseStep 2053937 = 1540453) B1540453
theorem B2053955 : Blo 1368503 2053955 := bstep (se 1 (by rfl) ⟨1540466, by rfl⟩ : syracuseStep 2053955 = 3080933) B3080933
theorem B2053985 : Blo 1368503 2053985 := bstep (se 2 (by rfl) ⟨770244, by rfl⟩ : syracuseStep 2053985 = 1540489) B1540489
theorem B2193265 : Blo 1368503 2193265 := bstep (se 2 (by rfl) ⟨822474, by rfl⟩ : syracuseStep 2193265 = 1644949) B1644949
theorem B2054003 : Blo 1368503 2054003 := bstep (se 1 (by rfl) ⟨1540502, by rfl⟩ : syracuseStep 2054003 = 3081005) B3081005
theorem B2054033 : Blo 1368503 2054033 := bstep (se 2 (by rfl) ⟨770262, by rfl⟩ : syracuseStep 2054033 = 1540525) B1540525
theorem B2054051 : Blo 1368503 2054051 := bstep (se 1 (by rfl) ⟨1540538, by rfl⟩ : syracuseStep 2054051 = 3081077) B3081077
theorem B7804835 : Blo 1368503 7804835 := bstep (se 1 (by rfl) ⟨5853626, by rfl⟩ : syracuseStep 7804835 = 11707253) B11707253
theorem B8779697 : Blo 1368503 8779697 := bstep (se 2 (by rfl) ⟨3292386, by rfl⟩ : syracuseStep 8779697 = 6584773) B6584773
theorem B2054081 : Blo 1368503 2054081 := bstep (se 2 (by rfl) ⟨770280, by rfl⟩ : syracuseStep 2054081 = 1540561) B1540561
theorem B5199821 : Blo 1368503 5199821 := bstep (se 3 (by rfl) ⟨974966, by rfl⟩ : syracuseStep 5199821 = 1949933) B1949933
theorem B2054099 : Blo 1368503 2054099 := bstep (se 1 (by rfl) ⟨1540574, by rfl⟩ : syracuseStep 2054099 = 3081149) B3081149
theorem B3897325 : Blo 1368503 3897325 := bstep (se 3 (by rfl) ⟨730748, by rfl⟩ : syracuseStep 3897325 = 1461497) B1461497
theorem B2054129 : Blo 1368503 2054129 := bstep (se 2 (by rfl) ⟨770298, by rfl⟩ : syracuseStep 2054129 = 1540597) B1540597
theorem B4388849 : Blo 1368503 4388849 := bstep (se 2 (by rfl) ⟨1645818, by rfl⟩ : syracuseStep 4388849 = 3291637) B3291637
theorem B2054147 : Blo 1368503 2054147 := bstep (se 1 (by rfl) ⟨1540610, by rfl⟩ : syracuseStep 2054147 = 3081221) B3081221
theorem B2054177 : Blo 1368503 2054177 := bstep (se 2 (by rfl) ⟨770316, by rfl⟩ : syracuseStep 2054177 = 1540633) B1540633
theorem B4388899 : Blo 1368503 4388899 := bstep (se 1 (by rfl) ⟨3291674, by rfl⟩ : syracuseStep 4388899 = 6583349) B6583349
theorem B2054195 : Blo 1368503 2054195 := bstep (se 1 (by rfl) ⟨1540646, by rfl⟩ : syracuseStep 2054195 = 3081293) B3081293
theorem B2054225 : Blo 1368503 2054225 := bstep (se 2 (by rfl) ⟨770334, by rfl⟩ : syracuseStep 2054225 = 1540669) B1540669
theorem B2054243 : Blo 1368503 2054243 := bstep (se 1 (by rfl) ⟨1540682, by rfl⟩ : syracuseStep 2054243 = 3081365) B3081365
theorem B2054273 : Blo 1368503 2054273 := bstep (se 2 (by rfl) ⟨770352, by rfl⟩ : syracuseStep 2054273 = 1540705) B1540705
theorem B2054291 : Blo 1368503 2054291 := bstep (se 1 (by rfl) ⟨1540718, by rfl⟩ : syracuseStep 2054291 = 3081437) B3081437
theorem B1562771 : Blo 1368503 1562771 := bstep (se 1 (by rfl) ⟨1172078, by rfl⟩ : syracuseStep 1562771 = 2344157) B2344157
theorem B2054321 : Blo 1368503 2054321 := bstep (se 2 (by rfl) ⟨770370, by rfl⟩ : syracuseStep 2054321 = 1540741) B1540741
theorem B2054339 : Blo 1368503 2054339 := bstep (se 1 (by rfl) ⟨1540754, by rfl⟩ : syracuseStep 2054339 = 3081509) B3081509
theorem B3897553 : Blo 1368503 3897553 := bstep (se 2 (by rfl) ⟨1461582, by rfl⟩ : syracuseStep 3897553 = 2923165) B2923165
theorem B2054369 : Blo 1368503 2054369 := bstep (se 2 (by rfl) ⟨770388, by rfl⟩ : syracuseStep 2054369 = 1540777) B1540777
theorem B2054387 : Blo 1368503 2054387 := bstep (se 1 (by rfl) ⟨1540790, by rfl⟩ : syracuseStep 2054387 = 3081581) B3081581
theorem B2054417 : Blo 1368503 2054417 := bstep (se 2 (by rfl) ⟨770406, by rfl⟩ : syracuseStep 2054417 = 1540813) B1540813
theorem B2054435 : Blo 1368503 2054435 := bstep (se 1 (by rfl) ⟨1540826, by rfl⟩ : syracuseStep 2054435 = 3081653) B3081653
theorem B2054465 : Blo 1368503 2054465 := bstep (se 2 (by rfl) ⟨770424, by rfl⟩ : syracuseStep 2054465 = 1540849) B1540849
theorem B2054483 : Blo 1368503 2054483 := bstep (se 1 (by rfl) ⟨1540862, by rfl⟩ : syracuseStep 2054483 = 3081725) B3081725
theorem B6928739 : Blo 1368503 6928739 := bstep (se 1 (by rfl) ⟨5196554, by rfl⟩ : syracuseStep 6928739 = 10393109) B10393109
theorem B3897713 : Blo 1368503 3897713 := bstep (se 2 (by rfl) ⟨1461642, by rfl⟩ : syracuseStep 3897713 = 2923285) B2923285
theorem B2054513 : Blo 1368503 2054513 := bstep (se 2 (by rfl) ⟨770442, by rfl⟩ : syracuseStep 2054513 = 1540885) B1540885
theorem B2054531 : Blo 1368503 2054531 := bstep (se 1 (by rfl) ⟨1540898, by rfl⟩ : syracuseStep 2054531 = 3081797) B3081797
theorem B13171085 : Blo 1368503 13171085 := bstep (se 3 (by rfl) ⟨2469578, by rfl⟩ : syracuseStep 13171085 = 4939157) B4939157
theorem B2193809 : Blo 1368503 2193809 := bstep (se 2 (by rfl) ⟨822678, by rfl⟩ : syracuseStep 2193809 = 1645357) B1645357
theorem B2054561 : Blo 1368503 2054561 := bstep (se 2 (by rfl) ⟨770460, by rfl⟩ : syracuseStep 2054561 = 1540921) B1540921
theorem B2054579 : Blo 1368503 2054579 := bstep (se 1 (by rfl) ⟨1540934, by rfl⟩ : syracuseStep 2054579 = 3081869) B3081869
theorem B8444357 : Blo 1368503 8444357 := bstep (se 4 (by rfl) ⟨791658, by rfl⟩ : syracuseStep 8444357 = 1583317) B1583317
theorem B8780237 : Blo 1368503 8780237 := bstep (se 3 (by rfl) ⟨1646294, by rfl⟩ : syracuseStep 8780237 = 3292589) B3292589
theorem B2054609 : Blo 1368503 2054609 := bstep (se 2 (by rfl) ⟨770478, by rfl⟩ : syracuseStep 2054609 = 1540957) B1540957
theorem B3897827 : Blo 1368503 3897827 := bstep (se 1 (by rfl) ⟨2923370, by rfl⟩ : syracuseStep 3897827 = 5846741) B5846741
theorem B2054627 : Blo 1368503 2054627 := bstep (se 1 (by rfl) ⟨1540970, by rfl⟩ : syracuseStep 2054627 = 3081941) B3081941
theorem B2054657 : Blo 1368503 2054657 := bstep (se 2 (by rfl) ⟨770496, by rfl⟩ : syracuseStep 2054657 = 1540993) B1540993
theorem B2054675 : Blo 1368503 2054675 := bstep (se 1 (by rfl) ⟨1541006, by rfl⟩ : syracuseStep 2054675 = 3082013) B3082013
theorem B2054705 : Blo 1368503 2054705 := bstep (se 2 (by rfl) ⟨770514, by rfl⟩ : syracuseStep 2054705 = 1541029) B1541029
theorem B2054723 : Blo 1368503 2054723 := bstep (se 1 (by rfl) ⟨1541042, by rfl⟩ : syracuseStep 2054723 = 3082085) B3082085
theorem B2054753 : Blo 1368503 2054753 := bstep (se 2 (by rfl) ⟨770532, by rfl⟩ : syracuseStep 2054753 = 1541065) B1541065
theorem B2054771 : Blo 1368503 2054771 := bstep (se 1 (by rfl) ⟨1541078, by rfl⟩ : syracuseStep 2054771 = 3082157) B3082157
theorem B2775683 : Blo 1368503 2775683 := bstep (se 1 (by rfl) ⟨2081762, by rfl⟩ : syracuseStep 2775683 = 4163525) B4163525
theorem B2054801 : Blo 1368503 2054801 := bstep (se 2 (by rfl) ⟨770550, by rfl⟩ : syracuseStep 2054801 = 1541101) B1541101
theorem B2054819 : Blo 1368503 2054819 := bstep (se 1 (by rfl) ⟨1541114, by rfl⟩ : syracuseStep 2054819 = 3082229) B3082229
theorem B2054849 : Blo 1368503 2054849 := bstep (se 2 (by rfl) ⟨770568, by rfl⟩ : syracuseStep 2054849 = 1541137) B1541137
theorem B2054867 : Blo 1368503 2054867 := bstep (se 1 (by rfl) ⟨1541150, by rfl⟩ : syracuseStep 2054867 = 3082301) B3082301
theorem B11107043 : Blo 1368503 11107043 := bstep (se 1 (by rfl) ⟨8330282, by rfl⟩ : syracuseStep 11107043 = 16660565) B16660565
theorem B5200625 : Blo 1368503 5200625 := bstep (se 2 (by rfl) ⟨1950234, by rfl⟩ : syracuseStep 5200625 = 3900469) B3900469
theorem B2054897 : Blo 1368503 2054897 := bstep (se 2 (by rfl) ⟨770586, by rfl⟩ : syracuseStep 2054897 = 1541173) B1541173
theorem B2054915 : Blo 1368503 2054915 := bstep (se 1 (by rfl) ⟨1541186, by rfl⟩ : syracuseStep 2054915 = 3082373) B3082373
theorem B52632341 : Blo 1368503 52632341 := bstep (se 6 (by rfl) ⟨1233570, by rfl⟩ : syracuseStep 52632341 = 2467141) B2467141
theorem B94878485 : Blo 1368503 94878485 := bstep (se 6 (by rfl) ⟨2223714, by rfl⟩ : syracuseStep 94878485 = 4447429) B4447429
theorem B2054945 : Blo 1368503 2054945 := bstep (se 2 (by rfl) ⟨770604, by rfl⟩ : syracuseStep 2054945 = 1541209) B1541209
theorem B2054963 : Blo 1368503 2054963 := bstep (se 1 (by rfl) ⟨1541222, by rfl⟩ : syracuseStep 2054963 = 3082445) B3082445
theorem B2054993 : Blo 1368503 2054993 := bstep (se 2 (by rfl) ⟨770622, by rfl⟩ : syracuseStep 2054993 = 1541245) B1541245
theorem B2055011 : Blo 1368503 2055011 := bstep (se 1 (by rfl) ⟨1541258, by rfl⟩ : syracuseStep 2055011 = 3082517) B3082517
theorem B2055041 : Blo 1368503 2055041 := bstep (se 2 (by rfl) ⟨770640, by rfl⟩ : syracuseStep 2055041 = 1541281) B1541281
theorem B3750787 : Blo 1368503 3750787 := bstep (se 1 (by rfl) ⟨2813090, by rfl⟩ : syracuseStep 3750787 = 5626181) B5626181
theorem B2055059 : Blo 1368503 2055059 := bstep (se 1 (by rfl) ⟨1541294, by rfl⟩ : syracuseStep 2055059 = 3082589) B3082589
theorem B2055089 : Blo 1368503 2055089 := bstep (se 2 (by rfl) ⟨770658, by rfl⟩ : syracuseStep 2055089 = 1541317) B1541317
theorem B17546165 : Blo 1368503 17546165 := bstep (se 5 (by rfl) ⟨822476, by rfl⟩ : syracuseStep 17546165 = 1644953) B1644953
theorem B2055107 : Blo 1368503 2055107 := bstep (se 1 (by rfl) ⟨1541330, by rfl⟩ : syracuseStep 2055107 = 3082661) B3082661
theorem B4619213 : Blo 1368503 4619213 := bstep (se 3 (by rfl) ⟨866102, by rfl⟩ : syracuseStep 4619213 = 1732205) B1732205
theorem B7125965 : Blo 1368503 7125965 := bstep (se 3 (by rfl) ⟨1336118, by rfl⟩ : syracuseStep 7125965 = 2672237) B2672237
theorem B2055137 : Blo 1368503 2055137 := bstep (se 2 (by rfl) ⟨770676, by rfl⟩ : syracuseStep 2055137 = 1541353) B1541353
theorem B2055155 : Blo 1368503 2055155 := bstep (se 1 (by rfl) ⟨1541366, by rfl⟩ : syracuseStep 2055155 = 3082733) B3082733
theorem B4619267 : Blo 1368503 4619267 := bstep (se 1 (by rfl) ⟨3464450, by rfl⟩ : syracuseStep 4619267 = 6928901) B6928901
theorem B10402829 : Blo 1368503 10402829 := bstep (se 3 (by rfl) ⟨1950530, by rfl⟩ : syracuseStep 10402829 = 3901061) B3901061
theorem B2055185 : Blo 1368503 2055185 := bstep (se 2 (by rfl) ⟨770694, by rfl⟩ : syracuseStep 2055185 = 1541389) B1541389
theorem B2055203 : Blo 1368503 2055203 := bstep (se 1 (by rfl) ⟨1541402, by rfl⟩ : syracuseStep 2055203 = 3082805) B3082805
theorem B6937649 : Blo 1368503 6937649 := bstep (se 2 (by rfl) ⟨2601618, by rfl⟩ : syracuseStep 6937649 = 5203237) B5203237
theorem B2055233 : Blo 1368503 2055233 := bstep (se 2 (by rfl) ⟨770712, by rfl⟩ : syracuseStep 2055233 = 1541425) B1541425
theorem B3701837 : Blo 1368503 3701837 := bstep (se 3 (by rfl) ⟨694094, by rfl⟩ : syracuseStep 3701837 = 1388189) B1388189
theorem B2055251 : Blo 1368503 2055251 := bstep (se 1 (by rfl) ⟨1541438, by rfl⟩ : syracuseStep 2055251 = 3082877) B3082877
theorem B2055281 : Blo 1368503 2055281 := bstep (se 2 (by rfl) ⟨770730, by rfl⟩ : syracuseStep 2055281 = 1541461) B1541461
theorem B2055299 : Blo 1368503 2055299 := bstep (se 1 (by rfl) ⟨1541474, by rfl⟩ : syracuseStep 2055299 = 3082949) B3082949
theorem B6929549 : Blo 1368503 6929549 := bstep (se 3 (by rfl) ⟨1299290, by rfl⟩ : syracuseStep 6929549 = 2598581) B2598581
theorem B3079313 : Blo 1368503 3079313 := bstep (se 2 (by rfl) ⟨1154742, by rfl⟩ : syracuseStep 3079313 = 2309485) B2309485
theorem B2055329 : Blo 1368503 2055329 := bstep (se 2 (by rfl) ⟨770748, by rfl⟩ : syracuseStep 2055329 = 1541497) B1541497
theorem B3079331 : Blo 1368503 3079331 := bstep (se 1 (by rfl) ⟨2309498, by rfl⟩ : syracuseStep 3079331 = 4618997) B4618997
theorem B2055347 : Blo 1368503 2055347 := bstep (se 1 (by rfl) ⟨1541510, by rfl⟩ : syracuseStep 2055347 = 3083021) B3083021
theorem B3701969 : Blo 1368503 3701969 := bstep (se 2 (by rfl) ⟨1388238, by rfl⟩ : syracuseStep 3701969 = 2776477) B2776477
theorem B2055377 : Blo 1368503 2055377 := bstep (se 2 (by rfl) ⟨770766, by rfl⟩ : syracuseStep 2055377 = 1541533) B1541533
theorem B1645795 : Blo 1368503 1645795 := bstep (se 1 (by rfl) ⟨1234346, by rfl⟩ : syracuseStep 1645795 = 2468693) B2468693
theorem B2055395 : Blo 1368503 2055395 := bstep (se 1 (by rfl) ⟨1541546, by rfl⟩ : syracuseStep 2055395 = 3083093) B3083093
theorem B4390129 : Blo 1368503 4390129 := bstep (se 2 (by rfl) ⟨1646298, by rfl⟩ : syracuseStep 4390129 = 3292597) B3292597
theorem B2309377 : Blo 1368503 2309377 := bstep (se 2 (by rfl) ⟨866016, by rfl⟩ : syracuseStep 2309377 = 1732033) B1732033
theorem B2055425 : Blo 1368503 2055425 := bstep (se 2 (by rfl) ⟨770784, by rfl⟩ : syracuseStep 2055425 = 1541569) B1541569
theorem B8772877 : Blo 1368503 8772877 := bstep (se 3 (by rfl) ⟨1644914, by rfl⟩ : syracuseStep 8772877 = 3289829) B3289829
theorem B4619537 : Blo 1368503 4619537 := bstep (se 2 (by rfl) ⟨1732326, by rfl⟩ : syracuseStep 4619537 = 3464653) B3464653
theorem B2055443 : Blo 1368503 2055443 := bstep (se 1 (by rfl) ⟨1541582, by rfl⟩ : syracuseStep 2055443 = 3083165) B3083165
theorem B2309411 : Blo 1368503 2309411 := bstep (se 1 (by rfl) ⟨1732058, by rfl⟩ : syracuseStep 2309411 = 3464117) B3464117
theorem B2055473 : Blo 1368503 2055473 := bstep (se 2 (by rfl) ⟨770802, by rfl⟩ : syracuseStep 2055473 = 1541605) B1541605
theorem B1875251 : Blo 1368503 1875251 := bstep (se 1 (by rfl) ⟨1406438, by rfl⟩ : syracuseStep 1875251 = 2812877) B2812877
theorem B3292483 : Blo 1368503 3292483 := bstep (se 1 (by rfl) ⟨2469362, by rfl⟩ : syracuseStep 3292483 = 4938725) B4938725
theorem B2055491 : Blo 1368503 2055491 := bstep (se 1 (by rfl) ⟨1541618, by rfl⟩ : syracuseStep 2055491 = 3083237) B3083237
theorem B2194771 : Blo 1368503 2194771 := bstep (se 1 (by rfl) ⟨1646078, by rfl⟩ : syracuseStep 2194771 = 3292157) B3292157
theorem B2055521 : Blo 1368503 2055521 := bstep (se 2 (by rfl) ⟨770820, by rfl⟩ : syracuseStep 2055521 = 1541641) B1541641
theorem B1949027 : Blo 1368503 1949027 := bstep (se 1 (by rfl) ⟨1461770, by rfl⟩ : syracuseStep 1949027 = 2923541) B2923541
theorem B5848433 : Blo 1368503 5848433 := bstep (se 2 (by rfl) ⟨2193162, by rfl⟩ : syracuseStep 5848433 = 4386325) B4386325
theorem B2055539 : Blo 1368503 2055539 := bstep (se 1 (by rfl) ⟨1541654, by rfl⟩ : syracuseStep 2055539 = 3083309) B3083309
theorem B5201293 : Blo 1368503 5201293 := bstep (se 3 (by rfl) ⟨975242, by rfl⟩ : syracuseStep 5201293 = 1950485) B1950485
theorem B2055569 : Blo 1368503 2055569 := bstep (se 2 (by rfl) ⟨770838, by rfl⟩ : syracuseStep 2055569 = 1541677) B1541677
theorem B2309539 : Blo 1368503 2309539 := bstep (se 1 (by rfl) ⟨1732154, by rfl⟩ : syracuseStep 2309539 = 3464309) B3464309
theorem B5848483 : Blo 1368503 5848483 := bstep (se 1 (by rfl) ⟨4386362, by rfl⟩ : syracuseStep 5848483 = 8772725) B8772725
theorem B2055587 : Blo 1368503 2055587 := bstep (se 1 (by rfl) ⟨1541690, by rfl⟩ : syracuseStep 2055587 = 3083381) B3083381
theorem B3079601 : Blo 1368503 3079601 := bstep (se 2 (by rfl) ⟨1154850, by rfl⟩ : syracuseStep 3079601 = 2309701) B2309701
theorem B2055617 : Blo 1368503 2055617 := bstep (se 2 (by rfl) ⟨770856, by rfl⟩ : syracuseStep 2055617 = 1541713) B1541713
theorem B3079619 : Blo 1368503 3079619 := bstep (se 1 (by rfl) ⟨2309714, by rfl⟩ : syracuseStep 3079619 = 4619429) B4619429
theorem B3898829 : Blo 1368503 3898829 := bstep (se 3 (by rfl) ⟨731030, by rfl⟩ : syracuseStep 3898829 = 1462061) B1462061
theorem B2923985 : Blo 1368503 2923985 := bstep (se 2 (by rfl) ⟨1096494, by rfl⟩ : syracuseStep 2923985 = 2192989) B2192989
theorem B2055635 : Blo 1368503 2055635 := bstep (se 1 (by rfl) ⟨1541726, by rfl⟩ : syracuseStep 2055635 = 3083453) B3083453
theorem B2055665 : Blo 1368503 2055665 := bstep (se 2 (by rfl) ⟨770874, by rfl⟩ : syracuseStep 2055665 = 1541749) B1541749
theorem B1539571 : Blo 1368503 1539571 := bstep (se 1 (by rfl) ⟨1154678, by rfl⟩ : syracuseStep 1539571 = 2309357) B2309357
theorem B2055683 : Blo 1368503 2055683 := bstep (se 1 (by rfl) ⟨1541762, by rfl⟩ : syracuseStep 2055683 = 3083525) B3083525
theorem B2055713 : Blo 1368503 2055713 := bstep (se 2 (by rfl) ⟨770892, by rfl⟩ : syracuseStep 2055713 = 1541785) B1541785
theorem B6577699 : Blo 1368503 6577699 := bstep (se 1 (by rfl) ⟨4933274, by rfl⟩ : syracuseStep 6577699 = 9866549) B9866549
theorem B2309681 : Blo 1368503 2309681 := bstep (se 2 (by rfl) ⟨866130, by rfl⟩ : syracuseStep 2309681 = 1732261) B1732261
theorem B2055731 : Blo 1368503 2055731 := bstep (se 1 (by rfl) ⟨1541798, by rfl⟩ : syracuseStep 2055731 = 3083597) B3083597
theorem B2195027 : Blo 1368503 2195027 := bstep (se 1 (by rfl) ⟨1646270, by rfl⟩ : syracuseStep 2195027 = 3292541) B3292541
theorem B2342515 : Blo 1368503 2342515 := bstep (se 1 (by rfl) ⟨1756886, by rfl⟩ : syracuseStep 2342515 = 3513773) B3513773
theorem B1539715 : Blo 1368503 1539715 := bstep (se 1 (by rfl) ⟨1154786, by rfl⟩ : syracuseStep 1539715 = 2309573) B2309573
theorem B3899011 : Blo 1368503 3899011 := bstep (se 1 (by rfl) ⟨2924258, by rfl⟩ : syracuseStep 3899011 = 5848517) B5848517
theorem B2309809 : Blo 1368503 2309809 := bstep (se 2 (by rfl) ⟨866178, by rfl⟩ : syracuseStep 2309809 = 1732357) B1732357
theorem B7798477 : Blo 1368503 7798477 := bstep (se 3 (by rfl) ⟨1462214, by rfl⟩ : syracuseStep 7798477 = 2924429) B2924429
theorem B3079889 : Blo 1368503 3079889 := bstep (se 2 (by rfl) ⟨1154958, by rfl⟩ : syracuseStep 3079889 = 2309917) B2309917
theorem B2309843 : Blo 1368503 2309843 := bstep (se 1 (by rfl) ⟨1732382, by rfl⟩ : syracuseStep 2309843 = 3464765) B3464765
theorem B3079907 : Blo 1368503 3079907 := bstep (se 1 (by rfl) ⟨2309930, by rfl⟩ : syracuseStep 3079907 = 4619861) B4619861
theorem B3464977 : Blo 1368503 3464977 := bstep (se 2 (by rfl) ⟨1299366, by rfl⟩ : syracuseStep 3464977 = 2598733) B2598733
theorem B1539859 : Blo 1368503 1539859 := bstep (se 1 (by rfl) ⟨1154894, by rfl⟩ : syracuseStep 1539859 = 2309789) B2309789
theorem B3899171 : Blo 1368503 3899171 := bstep (se 1 (by rfl) ⟨2924378, by rfl⟩ : syracuseStep 3899171 = 5848757) B5848757
theorem B4620077 : Blo 1368503 4620077 := bstep (se 3 (by rfl) ⟨866264, by rfl⟩ : syracuseStep 4620077 = 1732529) B1732529
theorem B2309971 : Blo 1368503 2309971 := bstep (se 1 (by rfl) ⟨1732478, by rfl⟩ : syracuseStep 2309971 = 3464957) B3464957
theorem B4620131 : Blo 1368503 4620131 := bstep (se 1 (by rfl) ⟨3465098, by rfl⟩ : syracuseStep 4620131 = 6930197) B6930197
theorem B1540003 : Blo 1368503 1540003 := bstep (se 1 (by rfl) ⟨1155002, by rfl⟩ : syracuseStep 1540003 = 2310005) B2310005
theorem B2310113 : Blo 1368503 2310113 := bstep (se 2 (by rfl) ⟨866292, by rfl⟩ : syracuseStep 2310113 = 1732585) B1732585
theorem B1949665 : Blo 1368503 1949665 := bstep (se 2 (by rfl) ⟨731124, by rfl⟩ : syracuseStep 1949665 = 1462249) B1462249
theorem B2924515 : Blo 1368503 2924515 := bstep (se 1 (by rfl) ⟨2193386, by rfl⟩ : syracuseStep 2924515 = 4386773) B4386773
theorem B3080177 : Blo 1368503 3080177 := bstep (se 2 (by rfl) ⟨1155066, by rfl⟩ : syracuseStep 3080177 = 2310133) B2310133
theorem B3121163 : Blo 1368503 3121163 := bstep (se 1 (by rfl) ⟨2340872, by rfl⟩ : syracuseStep 3121163 = 4681745) B4681745
theorem B2310167 : Blo 1368503 2310167 := bstep (se 1 (by rfl) ⟨1732625, by rfl⟩ : syracuseStep 2310167 = 3465251) B3465251
theorem B3465281 : Blo 1368503 3465281 := bstep (se 2 (by rfl) ⟨1299480, by rfl⟩ : syracuseStep 3465281 = 2598961) B2598961
theorem B8773697 : Blo 1368503 8773697 := bstep (se 2 (by rfl) ⟨3290136, by rfl⟩ : syracuseStep 8773697 = 6580273) B6580273
theorem B3080267 : Blo 1368503 3080267 := bstep (se 1 (by rfl) ⟨2310200, by rfl⟩ : syracuseStep 3080267 = 4620401) B4620401
theorem B1540183 : Blo 1368503 1540183 := bstep (se 1 (by rfl) ⟨1155137, by rfl⟩ : syracuseStep 1540183 = 2310275) B2310275
theorem B3080321 : Blo 1368503 3080321 := bstep (se 2 (by rfl) ⟨1155120, by rfl⟩ : syracuseStep 3080321 = 2310241) B2310241
theorem B2310295 : Blo 1368503 2310295 := bstep (se 1 (by rfl) ⟨1732721, by rfl⟩ : syracuseStep 2310295 = 3465443) B3465443
theorem B4620509 : Blo 1368503 4620509 := bstep (se 3 (by rfl) ⟨866345, by rfl⟩ : syracuseStep 4620509 = 1732691) B1732691
theorem B1540363 : Blo 1368503 1540363 := bstep (se 1 (by rfl) ⟨1155272, by rfl⟩ : syracuseStep 1540363 = 2310545) B2310545
theorem B5202251 : Blo 1368503 5202251 := bstep (se 1 (by rfl) ⟨3901688, by rfl⟩ : syracuseStep 5202251 = 7803377) B7803377
theorem B3080537 : Blo 1368503 3080537 := bstep (se 2 (by rfl) ⟨1155201, by rfl⟩ : syracuseStep 3080537 = 2310403) B2310403
theorem B1950041 : Blo 1368503 1950041 := bstep (se 2 (by rfl) ⟨731265, by rfl⟩ : syracuseStep 1950041 = 1462531) B1462531
theorem B5202265 : Blo 1368503 5202265 := bstep (se 2 (by rfl) ⟨1950849, by rfl⟩ : syracuseStep 5202265 = 3901699) B3901699
theorem B1540471 : Blo 1368503 1540471 := bstep (se 1 (by rfl) ⟨1155353, by rfl⟩ : syracuseStep 1540471 = 2310707) B2310707
theorem B3080627 : Blo 1368503 3080627 := bstep (se 1 (by rfl) ⟨2310470, by rfl⟩ : syracuseStep 3080627 = 4620941) B4620941
theorem B1368503 : Blo 1368503 1368503 := bstep (se 1 (by rfl) ⟨1026377, by rfl⟩ : syracuseStep 1368503 = 2052755) B2052755
theorem B1368523 : Blo 1368503 1368523 := bstep (se 1 (by rfl) ⟨1026392, by rfl⟩ : syracuseStep 1368523 = 2052785) B2052785
theorem B1368535 : Blo 1368503 1368535 := bstep (se 1 (by rfl) ⟨1026401, by rfl⟩ : syracuseStep 1368535 = 2052803) B2052803
theorem B3080663 : Blo 1368503 3080663 := bstep (se 1 (by rfl) ⟨2310497, by rfl⟩ : syracuseStep 3080663 = 4620995) B4620995
theorem B1851865 : Blo 1368503 1851865 := bstep (se 2 (by rfl) ⟨694449, by rfl⟩ : syracuseStep 1851865 = 1388899) B1388899
theorem B1368555 : Blo 1368503 1368555 := bstep (se 1 (by rfl) ⟨1026416, by rfl⟩ : syracuseStep 1368555 = 2052833) B2052833
theorem B1368567 : Blo 1368503 1368567 := bstep (se 1 (by rfl) ⟨1026425, by rfl⟩ : syracuseStep 1368567 = 2052851) B2052851
theorem B1368587 : Blo 1368503 1368587 := bstep (se 1 (by rfl) ⟨1026440, by rfl⟩ : syracuseStep 1368587 = 2052881) B2052881
theorem B1368599 : Blo 1368503 1368599 := bstep (se 1 (by rfl) ⟨1026449, by rfl⟩ : syracuseStep 1368599 = 2052899) B2052899
theorem B2081305 : Blo 1368503 2081305 := bstep (se 2 (by rfl) ⟨780489, by rfl⟩ : syracuseStep 2081305 = 1560979) B1560979
theorem B1368619 : Blo 1368503 1368619 := bstep (se 1 (by rfl) ⟨1026464, by rfl⟩ : syracuseStep 1368619 = 2052929) B2052929
theorem B1540651 : Blo 1368503 1540651 := bstep (se 1 (by rfl) ⟨1155488, by rfl⟩ : syracuseStep 1540651 = 2310977) B2310977
theorem B1368631 : Blo 1368503 1368631 := bstep (se 1 (by rfl) ⟨1026473, by rfl⟩ : syracuseStep 1368631 = 2052947) B2052947
theorem B1368651 : Blo 1368503 1368651 := bstep (se 1 (by rfl) ⟨1026488, by rfl⟩ : syracuseStep 1368651 = 2052977) B2052977
theorem B1368663 : Blo 1368503 1368663 := bstep (se 1 (by rfl) ⟨1026497, by rfl⟩ : syracuseStep 1368663 = 2052995) B2052995
theorem B1368683 : Blo 1368503 1368683 := bstep (se 1 (by rfl) ⟨1026512, by rfl⟩ : syracuseStep 1368683 = 2053025) B2053025
theorem B1368695 : Blo 1368503 1368695 := bstep (se 1 (by rfl) ⟨1026521, by rfl⟩ : syracuseStep 1368695 = 2053043) B2053043
theorem B1368715 : Blo 1368503 1368715 := bstep (se 1 (by rfl) ⟨1026536, by rfl⟩ : syracuseStep 1368715 = 2053073) B2053073
theorem B3080843 : Blo 1368503 3080843 := bstep (se 1 (by rfl) ⟨2310632, by rfl⟩ : syracuseStep 3080843 = 4621265) B4621265
theorem B1368727 : Blo 1368503 1368727 := bstep (se 1 (by rfl) ⟨1026545, by rfl⟩ : syracuseStep 1368727 = 2053091) B2053091
theorem B1540759 : Blo 1368503 1540759 := bstep (se 1 (by rfl) ⟨1155569, by rfl⟩ : syracuseStep 1540759 = 2311139) B2311139
theorem B3007127 : Blo 1368503 3007127 := bstep (se 1 (by rfl) ⟨2255345, by rfl⟩ : syracuseStep 3007127 = 4510691) B4510691
theorem B1368747 : Blo 1368503 1368747 := bstep (se 1 (by rfl) ⟨1026560, by rfl⟩ : syracuseStep 1368747 = 2053121) B2053121
theorem B1368759 : Blo 1368503 1368759 := bstep (se 1 (by rfl) ⟨1026569, by rfl⟩ : syracuseStep 1368759 = 2053139) B2053139
theorem B3080897 : Blo 1368503 3080897 := bstep (se 2 (by rfl) ⟨1155336, by rfl⟩ : syracuseStep 3080897 = 2310673) B2310673
theorem B1368779 : Blo 1368503 1368779 := bstep (se 1 (by rfl) ⟨1026584, by rfl⟩ : syracuseStep 1368779 = 2053169) B2053169
theorem B1368791 : Blo 1368503 1368791 := bstep (se 1 (by rfl) ⟨1026593, by rfl⟩ : syracuseStep 1368791 = 2053187) B2053187
theorem B1368811 : Blo 1368503 1368811 := bstep (se 1 (by rfl) ⟨1026608, by rfl⟩ : syracuseStep 1368811 = 2053217) B2053217
theorem B1368823 : Blo 1368503 1368823 := bstep (se 1 (by rfl) ⟨1026617, by rfl⟩ : syracuseStep 1368823 = 2053235) B2053235
theorem B1368843 : Blo 1368503 1368843 := bstep (se 1 (by rfl) ⟨1026632, by rfl⟩ : syracuseStep 1368843 = 2053265) B2053265
theorem B2310923 : Blo 1368503 2310923 := bstep (se 1 (by rfl) ⟨1733192, by rfl⟩ : syracuseStep 2310923 = 3466385) B3466385
theorem B3425047 : Blo 1368503 3425047 := bstep (se 1 (by rfl) ⟨2568785, by rfl⟩ : syracuseStep 3425047 = 5137571) B5137571
theorem B1368855 : Blo 1368503 1368855 := bstep (se 1 (by rfl) ⟨1026641, by rfl⟩ : syracuseStep 1368855 = 2053283) B2053283
theorem B2925335 : Blo 1368503 2925335 := bstep (se 1 (by rfl) ⟨2194001, by rfl⟩ : syracuseStep 2925335 = 4388003) B4388003
theorem B1368875 : Blo 1368503 1368875 := bstep (se 1 (by rfl) ⟨1026656, by rfl⟩ : syracuseStep 1368875 = 2053313) B2053313
theorem B1368887 : Blo 1368503 1368887 := bstep (se 1 (by rfl) ⟨1026665, by rfl⟩ : syracuseStep 1368887 = 2053331) B2053331
theorem B1368907 : Blo 1368503 1368907 := bstep (se 1 (by rfl) ⟨1026680, by rfl⟩ : syracuseStep 1368907 = 2053361) B2053361
theorem B1540939 : Blo 1368503 1540939 := bstep (se 1 (by rfl) ⟨1155704, by rfl⟩ : syracuseStep 1540939 = 2311409) B2311409
theorem B1368919 : Blo 1368503 1368919 := bstep (se 1 (by rfl) ⟨1026689, by rfl⟩ : syracuseStep 1368919 = 2053379) B2053379
theorem B1368939 : Blo 1368503 1368939 := bstep (se 1 (by rfl) ⟨1026704, by rfl⟩ : syracuseStep 1368939 = 2053409) B2053409
theorem B1368951 : Blo 1368503 1368951 := bstep (se 1 (by rfl) ⟨1026713, by rfl⟩ : syracuseStep 1368951 = 2053427) B2053427
theorem B6931331 : Blo 1368503 6931331 := bstep (se 1 (by rfl) ⟨5198498, by rfl⟩ : syracuseStep 6931331 = 10396997) B10396997
theorem B3122059 : Blo 1368503 3122059 := bstep (se 1 (by rfl) ⟨2341544, by rfl⟩ : syracuseStep 3122059 = 4683089) B4683089
theorem B1368971 : Blo 1368503 1368971 := bstep (se 1 (by rfl) ⟨1026728, by rfl⟩ : syracuseStep 1368971 = 2053457) B2053457
theorem B2311051 : Blo 1368503 2311051 := bstep (se 1 (by rfl) ⟨1733288, by rfl⟩ : syracuseStep 2311051 = 3466577) B3466577
theorem B1368983 : Blo 1368503 1368983 := bstep (se 1 (by rfl) ⟨1026737, by rfl⟩ : syracuseStep 1368983 = 2053475) B2053475
theorem B3081113 : Blo 1368503 3081113 := bstep (se 2 (by rfl) ⟨1155417, by rfl⟩ : syracuseStep 3081113 = 2310835) B2310835
theorem B1369003 : Blo 1368503 1369003 := bstep (se 1 (by rfl) ⟨1026752, by rfl⟩ : syracuseStep 1369003 = 2053505) B2053505
theorem B1369015 : Blo 1368503 1369015 := bstep (se 1 (by rfl) ⟨1026761, by rfl⟩ : syracuseStep 1369015 = 2053523) B2053523
theorem B1541047 : Blo 1368503 1541047 := bstep (se 1 (by rfl) ⟨1155785, by rfl⟩ : syracuseStep 1541047 = 2311571) B2311571
theorem B1369035 : Blo 1368503 1369035 := bstep (se 1 (by rfl) ⟨1026776, by rfl⟩ : syracuseStep 1369035 = 2053553) B2053553
theorem B1369047 : Blo 1368503 1369047 := bstep (se 1 (by rfl) ⟨1026785, by rfl⟩ : syracuseStep 1369047 = 2053571) B2053571
theorem B1950679 : Blo 1368503 1950679 := bstep (se 1 (by rfl) ⟨1463009, by rfl⟩ : syracuseStep 1950679 = 2926019) B2926019
theorem B1369067 : Blo 1368503 1369067 := bstep (se 1 (by rfl) ⟨1026800, by rfl⟩ : syracuseStep 1369067 = 2053601) B2053601
theorem B3081203 : Blo 1368503 3081203 := bstep (se 1 (by rfl) ⟨2310902, by rfl⟩ : syracuseStep 3081203 = 4621805) B4621805
theorem B1369079 : Blo 1368503 1369079 := bstep (se 1 (by rfl) ⟨1026809, by rfl⟩ : syracuseStep 1369079 = 2053619) B2053619
theorem B6243331 : Blo 1368503 6243331 := bstep (se 1 (by rfl) ⟨4682498, by rfl⟩ : syracuseStep 6243331 = 9364997) B9364997
theorem B1369099 : Blo 1368503 1369099 := bstep (se 1 (by rfl) ⟨1026824, by rfl⟩ : syracuseStep 1369099 = 2053649) B2053649
theorem B1369111 : Blo 1368503 1369111 := bstep (se 1 (by rfl) ⟨1026833, by rfl⟩ : syracuseStep 1369111 = 2053667) B2053667
theorem B3081239 : Blo 1368503 3081239 := bstep (se 1 (by rfl) ⟨2310929, by rfl⟩ : syracuseStep 3081239 = 4621859) B4621859
theorem B2311193 : Blo 1368503 2311193 := bstep (se 2 (by rfl) ⟨866697, by rfl⟩ : syracuseStep 2311193 = 1733395) B1733395
theorem B1369131 : Blo 1368503 1369131 := bstep (se 1 (by rfl) ⟨1026848, by rfl⟩ : syracuseStep 1369131 = 2053697) B2053697
theorem B5850157 : Blo 1368503 5850157 := bstep (se 3 (by rfl) ⟨1096904, by rfl⟩ : syracuseStep 5850157 = 2193809) B2193809
theorem B1369143 : Blo 1368503 1369143 := bstep (se 1 (by rfl) ⟨1026857, by rfl⟩ : syracuseStep 1369143 = 2053715) B2053715
theorem B1369163 : Blo 1368503 1369163 := bstep (se 1 (by rfl) ⟨1026872, by rfl⟩ : syracuseStep 1369163 = 2053745) B2053745
theorem B1369175 : Blo 1368503 1369175 := bstep (se 1 (by rfl) ⟨1026881, by rfl⟩ : syracuseStep 1369175 = 2053763) B2053763
theorem B1369195 : Blo 1368503 1369195 := bstep (se 1 (by rfl) ⟨1026896, by rfl⟩ : syracuseStep 1369195 = 2053793) B2053793
theorem B1541227 : Blo 1368503 1541227 := bstep (se 1 (by rfl) ⟨1155920, by rfl⟩ : syracuseStep 1541227 = 2311841) B2311841
theorem B1369207 : Blo 1368503 1369207 := bstep (se 1 (by rfl) ⟨1026905, by rfl⟩ : syracuseStep 1369207 = 2053811) B2053811
theorem B1369227 : Blo 1368503 1369227 := bstep (se 1 (by rfl) ⟨1026920, by rfl⟩ : syracuseStep 1369227 = 2053841) B2053841
theorem B1369239 : Blo 1368503 1369239 := bstep (se 1 (by rfl) ⟨1026929, by rfl⟩ : syracuseStep 1369239 = 2053859) B2053859
theorem B2311321 : Blo 1368503 2311321 := bstep (se 2 (by rfl) ⟨866745, by rfl⟩ : syracuseStep 2311321 = 1733491) B1733491
theorem B1369259 : Blo 1368503 1369259 := bstep (se 1 (by rfl) ⟨1026944, by rfl⟩ : syracuseStep 1369259 = 2053889) B2053889
theorem B3900595 : Blo 1368503 3900595 := bstep (se 1 (by rfl) ⟨2925446, by rfl⟩ : syracuseStep 3900595 = 5850893) B5850893
theorem B1369271 : Blo 1368503 1369271 := bstep (se 1 (by rfl) ⟨1026953, by rfl⟩ : syracuseStep 1369271 = 2053907) B2053907
theorem B1369291 : Blo 1368503 1369291 := bstep (se 1 (by rfl) ⟨1026968, by rfl⟩ : syracuseStep 1369291 = 2053937) B2053937
theorem B3081419 : Blo 1368503 3081419 := bstep (se 1 (by rfl) ⟨2311064, by rfl⟩ : syracuseStep 3081419 = 4622129) B4622129
theorem B1369303 : Blo 1368503 1369303 := bstep (se 1 (by rfl) ⟨1026977, by rfl⟩ : syracuseStep 1369303 = 2053955) B2053955
theorem B1541335 : Blo 1368503 1541335 := bstep (se 1 (by rfl) ⟨1156001, by rfl⟩ : syracuseStep 1541335 = 2312003) B2312003
theorem B1369323 : Blo 1368503 1369323 := bstep (se 1 (by rfl) ⟨1026992, by rfl⟩ : syracuseStep 1369323 = 2053985) B2053985
theorem B1369335 : Blo 1368503 1369335 := bstep (se 1 (by rfl) ⟨1027001, by rfl⟩ : syracuseStep 1369335 = 2054003) B2054003
theorem B3081473 : Blo 1368503 3081473 := bstep (se 2 (by rfl) ⟨1155552, by rfl⟩ : syracuseStep 3081473 = 2311105) B2311105
theorem B59245829 : Blo 1368503 59245829 := bstep (se 4 (by rfl) ⟨5554296, by rfl⟩ : syracuseStep 59245829 = 11108593) B11108593
theorem B23414021 : Blo 1368503 23414021 := bstep (se 4 (by rfl) ⟨2195064, by rfl⟩ : syracuseStep 23414021 = 4390129) B4390129
theorem B1369355 : Blo 1368503 1369355 := bstep (se 1 (by rfl) ⟨1027016, by rfl⟩ : syracuseStep 1369355 = 2054033) B2054033
theorem B1369367 : Blo 1368503 1369367 := bstep (se 1 (by rfl) ⟨1027025, by rfl⟩ : syracuseStep 1369367 = 2054051) B2054051
theorem B5203223 : Blo 1368503 5203223 := bstep (se 1 (by rfl) ⟨3902417, by rfl⟩ : syracuseStep 5203223 = 7804835) B7804835
theorem B1369387 : Blo 1368503 1369387 := bstep (se 1 (by rfl) ⟨1027040, by rfl⟩ : syracuseStep 1369387 = 2054081) B2054081
theorem B3466547 : Blo 1368503 3466547 := bstep (se 1 (by rfl) ⟨2599910, by rfl⟩ : syracuseStep 3466547 = 5199821) B5199821
theorem B1369399 : Blo 1368503 1369399 := bstep (se 1 (by rfl) ⟨1027049, by rfl⟩ : syracuseStep 1369399 = 2054099) B2054099
theorem B4621643 : Blo 1368503 4621643 := bstep (se 1 (by rfl) ⟨3466232, by rfl⟩ : syracuseStep 4621643 = 6932465) B6932465
theorem B1369419 : Blo 1368503 1369419 := bstep (se 1 (by rfl) ⟨1027064, by rfl⟩ : syracuseStep 1369419 = 2054129) B2054129
theorem B2925899 : Blo 1368503 2925899 := bstep (se 1 (by rfl) ⟨2194424, by rfl⟩ : syracuseStep 2925899 = 4388849) B4388849
theorem B1369431 : Blo 1368503 1369431 := bstep (se 1 (by rfl) ⟨1027073, by rfl⟩ : syracuseStep 1369431 = 2054147) B2054147
theorem B1369451 : Blo 1368503 1369451 := bstep (se 1 (by rfl) ⟨1027088, by rfl⟩ : syracuseStep 1369451 = 2054177) B2054177
theorem B1369463 : Blo 1368503 1369463 := bstep (se 1 (by rfl) ⟨1027097, by rfl⟩ : syracuseStep 1369463 = 2054195) B2054195
theorem B1369483 : Blo 1368503 1369483 := bstep (se 1 (by rfl) ⟨1027112, by rfl⟩ : syracuseStep 1369483 = 2054225) B2054225
theorem B1541515 : Blo 1368503 1541515 := bstep (se 1 (by rfl) ⟨1156136, by rfl⟩ : syracuseStep 1541515 = 2312273) B2312273
theorem B2082199 : Blo 1368503 2082199 := bstep (se 1 (by rfl) ⟨1561649, by rfl⟩ : syracuseStep 2082199 = 3123299) B3123299
theorem B1369495 : Blo 1368503 1369495 := bstep (se 1 (by rfl) ⟨1027121, by rfl⟩ : syracuseStep 1369495 = 2054243) B2054243
theorem B1369515 : Blo 1368503 1369515 := bstep (se 1 (by rfl) ⟨1027136, by rfl⟩ : syracuseStep 1369515 = 2054273) B2054273
theorem B1369527 : Blo 1368503 1369527 := bstep (se 1 (by rfl) ⟨1027145, by rfl⟩ : syracuseStep 1369527 = 2054291) B2054291
theorem B1369547 : Blo 1368503 1369547 := bstep (se 1 (by rfl) ⟨1027160, by rfl⟩ : syracuseStep 1369547 = 2054321) B2054321
theorem B1369559 : Blo 1368503 1369559 := bstep (se 1 (by rfl) ⟨1027169, by rfl⟩ : syracuseStep 1369559 = 2054339) B2054339
theorem B3081689 : Blo 1368503 3081689 := bstep (se 2 (by rfl) ⟨1155633, by rfl⟩ : syracuseStep 3081689 = 2311267) B2311267
theorem B1369579 : Blo 1368503 1369579 := bstep (se 1 (by rfl) ⟨1027184, by rfl⟩ : syracuseStep 1369579 = 2054369) B2054369
theorem B1369591 : Blo 1368503 1369591 := bstep (se 1 (by rfl) ⟨1027193, by rfl⟩ : syracuseStep 1369591 = 2054387) B2054387
theorem B1541623 : Blo 1368503 1541623 := bstep (se 1 (by rfl) ⟨1156217, by rfl⟩ : syracuseStep 1541623 = 2312435) B2312435
theorem B1369611 : Blo 1368503 1369611 := bstep (se 1 (by rfl) ⟨1027208, by rfl⟩ : syracuseStep 1369611 = 2054417) B2054417
theorem B1369623 : Blo 1368503 1369623 := bstep (se 1 (by rfl) ⟨1027217, by rfl⟩ : syracuseStep 1369623 = 2054435) B2054435
theorem B1369643 : Blo 1368503 1369643 := bstep (se 1 (by rfl) ⟨1027232, by rfl⟩ : syracuseStep 1369643 = 2054465) B2054465
theorem B3081779 : Blo 1368503 3081779 := bstep (se 1 (by rfl) ⟨2311334, by rfl⟩ : syracuseStep 3081779 = 4622669) B4622669
theorem B1369655 : Blo 1368503 1369655 := bstep (se 1 (by rfl) ⟨1027241, by rfl⟩ : syracuseStep 1369655 = 2054483) B2054483
theorem B2598475 : Blo 1368503 2598475 := bstep (se 1 (by rfl) ⟨1948856, by rfl⟩ : syracuseStep 2598475 = 3897713) B3897713
theorem B1369675 : Blo 1368503 1369675 := bstep (se 1 (by rfl) ⟨1027256, by rfl⟩ : syracuseStep 1369675 = 2054513) B2054513
theorem B1369687 : Blo 1368503 1369687 := bstep (se 1 (by rfl) ⟨1027265, by rfl⟩ : syracuseStep 1369687 = 2054531) B2054531
theorem B3081815 : Blo 1368503 3081815 := bstep (se 1 (by rfl) ⟨2311361, by rfl⟩ : syracuseStep 3081815 = 4622723) B4622723
theorem B4621913 : Blo 1368503 4621913 := bstep (se 2 (by rfl) ⟨1733217, by rfl⟩ : syracuseStep 4621913 = 3466435) B3466435
theorem B1369707 : Blo 1368503 1369707 := bstep (se 1 (by rfl) ⟨1027280, by rfl⟩ : syracuseStep 1369707 = 2054561) B2054561
theorem B1369719 : Blo 1368503 1369719 := bstep (se 1 (by rfl) ⟨1027289, by rfl⟩ : syracuseStep 1369719 = 2054579) B2054579
theorem B5629571 : Blo 1368503 5629571 := bstep (se 1 (by rfl) ⟨4222178, by rfl⟩ : syracuseStep 5629571 = 8444357) B8444357
theorem B1369739 : Blo 1368503 1369739 := bstep (se 1 (by rfl) ⟨1027304, by rfl⟩ : syracuseStep 1369739 = 2054609) B2054609
theorem B2598551 : Blo 1368503 2598551 := bstep (se 1 (by rfl) ⟨1948913, by rfl⟩ : syracuseStep 2598551 = 3897827) B3897827
theorem B1369751 : Blo 1368503 1369751 := bstep (se 1 (by rfl) ⟨1027313, by rfl⟩ : syracuseStep 1369751 = 2054627) B2054627
theorem B1369771 : Blo 1368503 1369771 := bstep (se 1 (by rfl) ⟨1027328, by rfl⟩ : syracuseStep 1369771 = 2054657) B2054657
theorem B1541803 : Blo 1368503 1541803 := bstep (se 1 (by rfl) ⟨1156352, by rfl⟩ : syracuseStep 1541803 = 2312705) B2312705
theorem B1369783 : Blo 1368503 1369783 := bstep (se 1 (by rfl) ⟨1027337, by rfl⟩ : syracuseStep 1369783 = 2054675) B2054675
theorem B1369803 : Blo 1368503 1369803 := bstep (se 1 (by rfl) ⟨1027352, by rfl⟩ : syracuseStep 1369803 = 2054705) B2054705
theorem B1369815 : Blo 1368503 1369815 := bstep (se 1 (by rfl) ⟨1027361, by rfl⟩ : syracuseStep 1369815 = 2054723) B2054723
theorem B2311895 : Blo 1368503 2311895 := bstep (se 1 (by rfl) ⟨1733921, by rfl⟩ : syracuseStep 2311895 = 3467843) B3467843
theorem B4687577 : Blo 1368503 4687577 := bstep (se 2 (by rfl) ⟨1757841, by rfl⟩ : syracuseStep 4687577 = 3515683) B3515683
theorem B1369835 : Blo 1368503 1369835 := bstep (se 1 (by rfl) ⟨1027376, by rfl⟩ : syracuseStep 1369835 = 2054753) B2054753
theorem B1369847 : Blo 1368503 1369847 := bstep (se 1 (by rfl) ⟨1027385, by rfl⟩ : syracuseStep 1369847 = 2054771) B2054771
theorem B3081995 : Blo 1368503 3081995 := bstep (se 1 (by rfl) ⟨2311496, by rfl⟩ : syracuseStep 3081995 = 4622993) B4622993
theorem B1369867 : Blo 1368503 1369867 := bstep (se 1 (by rfl) ⟨1027400, by rfl⟩ : syracuseStep 1369867 = 2054801) B2054801
theorem B1369879 : Blo 1368503 1369879 := bstep (se 1 (by rfl) ⟨1027409, by rfl⟩ : syracuseStep 1369879 = 2054819) B2054819
theorem B2926361 : Blo 1368503 2926361 := bstep (se 2 (by rfl) ⟨1097385, by rfl⟩ : syracuseStep 2926361 = 2194771) B2194771
theorem B1369899 : Blo 1368503 1369899 := bstep (se 1 (by rfl) ⟨1027424, by rfl⟩ : syracuseStep 1369899 = 2054849) B2054849
theorem B1369911 : Blo 1368503 1369911 := bstep (se 1 (by rfl) ⟨1027433, by rfl⟩ : syracuseStep 1369911 = 2054867) B2054867
theorem B3082049 : Blo 1368503 3082049 := bstep (se 2 (by rfl) ⟨1155768, by rfl⟩ : syracuseStep 3082049 = 2311537) B2311537
theorem B3467083 : Blo 1368503 3467083 := bstep (se 1 (by rfl) ⟨2600312, by rfl⟩ : syracuseStep 3467083 = 5200625) B5200625
theorem B1369931 : Blo 1368503 1369931 := bstep (se 1 (by rfl) ⟨1027448, by rfl⟩ : syracuseStep 1369931 = 2054897) B2054897
theorem B1369943 : Blo 1368503 1369943 := bstep (se 1 (by rfl) ⟨1027457, by rfl⟩ : syracuseStep 1369943 = 2054915) B2054915
theorem B2312023 : Blo 1368503 2312023 := bstep (se 1 (by rfl) ⟨1734017, by rfl⟩ : syracuseStep 2312023 = 3468035) B3468035
theorem B35088227 : Blo 1368503 35088227 := bstep (se 1 (by rfl) ⟨26316170, by rfl⟩ : syracuseStep 35088227 = 52632341) B52632341
theorem B63252323 : Blo 1368503 63252323 := bstep (se 1 (by rfl) ⟨47439242, by rfl⟩ : syracuseStep 63252323 = 94878485) B94878485
theorem B1369963 : Blo 1368503 1369963 := bstep (se 1 (by rfl) ⟨1027472, by rfl⟩ : syracuseStep 1369963 = 2054945) B2054945
theorem B1369975 : Blo 1368503 1369975 := bstep (se 1 (by rfl) ⟨1027481, by rfl⟩ : syracuseStep 1369975 = 2054963) B2054963
theorem B1369995 : Blo 1368503 1369995 := bstep (se 1 (by rfl) ⟨1027496, by rfl⟩ : syracuseStep 1369995 = 2054993) B2054993
theorem B1370007 : Blo 1368503 1370007 := bstep (se 1 (by rfl) ⟨1027505, by rfl⟩ : syracuseStep 1370007 = 2055011) B2055011
theorem B1370027 : Blo 1368503 1370027 := bstep (se 1 (by rfl) ⟨1027520, by rfl⟩ : syracuseStep 1370027 = 2055041) B2055041
theorem B1370039 : Blo 1368503 1370039 := bstep (se 1 (by rfl) ⟨1027529, by rfl⟩ : syracuseStep 1370039 = 2055059) B2055059
theorem B1370059 : Blo 1368503 1370059 := bstep (se 1 (by rfl) ⟨1027544, by rfl⟩ : syracuseStep 1370059 = 2055089) B2055089
theorem B1370071 : Blo 1368503 1370071 := bstep (se 1 (by rfl) ⟨1027553, by rfl⟩ : syracuseStep 1370071 = 2055107) B2055107
theorem B3467225 : Blo 1368503 3467225 := bstep (se 2 (by rfl) ⟨1300209, by rfl⟩ : syracuseStep 3467225 = 2600419) B2600419
theorem B1370091 : Blo 1368503 1370091 := bstep (se 1 (by rfl) ⟨1027568, by rfl⟩ : syracuseStep 1370091 = 2055137) B2055137
theorem B1370103 : Blo 1368503 1370103 := bstep (se 1 (by rfl) ⟨1027577, by rfl⟩ : syracuseStep 1370103 = 2055155) B2055155
theorem B1370123 : Blo 1368503 1370123 := bstep (se 1 (by rfl) ⟨1027592, by rfl⟩ : syracuseStep 1370123 = 2055185) B2055185
theorem B1370135 : Blo 1368503 1370135 := bstep (se 1 (by rfl) ⟨1027601, by rfl⟩ : syracuseStep 1370135 = 2055203) B2055203
theorem B3082265 : Blo 1368503 3082265 := bstep (se 2 (by rfl) ⟨1155849, by rfl⟩ : syracuseStep 3082265 = 2311699) B2311699
theorem B1370155 : Blo 1368503 1370155 := bstep (se 1 (by rfl) ⟨1027616, by rfl⟩ : syracuseStep 1370155 = 2055233) B2055233
theorem B2467891 : Blo 1368503 2467891 := bstep (se 1 (by rfl) ⟨1850918, by rfl⟩ : syracuseStep 2467891 = 3701837) B3701837
theorem B1370167 : Blo 1368503 1370167 := bstep (se 1 (by rfl) ⟨1027625, by rfl⟩ : syracuseStep 1370167 = 2055251) B2055251
theorem B1370187 : Blo 1368503 1370187 := bstep (se 1 (by rfl) ⟨1027640, by rfl⟩ : syracuseStep 1370187 = 2055281) B2055281
theorem B1370199 : Blo 1368503 1370199 := bstep (se 1 (by rfl) ⟨1027649, by rfl⟩ : syracuseStep 1370199 = 2055299) B2055299
theorem B1370219 : Blo 1368503 1370219 := bstep (se 1 (by rfl) ⟨1027664, by rfl⟩ : syracuseStep 1370219 = 2055329) B2055329
theorem B3082355 : Blo 1368503 3082355 := bstep (se 1 (by rfl) ⟨2311766, by rfl⟩ : syracuseStep 3082355 = 4623533) B4623533
theorem B1370231 : Blo 1368503 1370231 := bstep (se 1 (by rfl) ⟨1027673, by rfl⟩ : syracuseStep 1370231 = 2055347) B2055347
theorem B2467979 : Blo 1368503 2467979 := bstep (se 1 (by rfl) ⟨1850984, by rfl⟩ : syracuseStep 2467979 = 3701969) B3701969
theorem B1370251 : Blo 1368503 1370251 := bstep (se 1 (by rfl) ⟨1027688, by rfl⟩ : syracuseStep 1370251 = 2055377) B2055377
theorem B3082391 : Blo 1368503 3082391 := bstep (se 1 (by rfl) ⟨2311793, by rfl⟩ : syracuseStep 3082391 = 4623587) B4623587
theorem B1370263 : Blo 1368503 1370263 := bstep (se 1 (by rfl) ⟨1027697, by rfl⟩ : syracuseStep 1370263 = 2055395) B2055395
theorem B3123353 : Blo 1368503 3123353 := bstep (se 2 (by rfl) ⟨1171257, by rfl⟩ : syracuseStep 3123353 = 2342515) B2342515
theorem B1370283 : Blo 1368503 1370283 := bstep (se 1 (by rfl) ⟨1027712, by rfl⟩ : syracuseStep 1370283 = 2055425) B2055425
theorem B1370295 : Blo 1368503 1370295 := bstep (se 1 (by rfl) ⟨1027721, by rfl⟩ : syracuseStep 1370295 = 2055443) B2055443
theorem B1370315 : Blo 1368503 1370315 := bstep (se 1 (by rfl) ⟨1027736, by rfl⟩ : syracuseStep 1370315 = 2055473) B2055473
theorem B1370327 : Blo 1368503 1370327 := bstep (se 1 (by rfl) ⟨1027745, by rfl⟩ : syracuseStep 1370327 = 2055491) B2055491
theorem B1370347 : Blo 1368503 1370347 := bstep (se 1 (by rfl) ⟨1027760, by rfl⟩ : syracuseStep 1370347 = 2055521) B2055521
theorem B1370359 : Blo 1368503 1370359 := bstep (se 1 (by rfl) ⟨1027769, by rfl⟩ : syracuseStep 1370359 = 2055539) B2055539
theorem B1370379 : Blo 1368503 1370379 := bstep (se 1 (by rfl) ⟨1027784, by rfl⟩ : syracuseStep 1370379 = 2055569) B2055569
theorem B10397969 : Blo 1368503 10397969 := bstep (se 2 (by rfl) ⟨3899238, by rfl⟩ : syracuseStep 10397969 = 7798477) B7798477
theorem B4622615 : Blo 1368503 4622615 := bstep (se 1 (by rfl) ⟨3466961, by rfl⟩ : syracuseStep 4622615 = 6933923) B6933923
theorem B1370391 : Blo 1368503 1370391 := bstep (se 1 (by rfl) ⟨1027793, by rfl⟩ : syracuseStep 1370391 = 2055587) B2055587
theorem B1370411 : Blo 1368503 1370411 := bstep (se 1 (by rfl) ⟨1027808, by rfl⟩ : syracuseStep 1370411 = 2055617) B2055617
theorem B2599219 : Blo 1368503 2599219 := bstep (se 1 (by rfl) ⟨1949414, by rfl⟩ : syracuseStep 2599219 = 3898829) B3898829
theorem B1370423 : Blo 1368503 1370423 := bstep (se 1 (by rfl) ⟨1027817, by rfl⟩ : syracuseStep 1370423 = 2055635) B2055635
theorem B3082571 : Blo 1368503 3082571 := bstep (se 1 (by rfl) ⟨2311928, by rfl⟩ : syracuseStep 3082571 = 4623857) B4623857
theorem B1370443 : Blo 1368503 1370443 := bstep (se 1 (by rfl) ⟨1027832, by rfl⟩ : syracuseStep 1370443 = 2055665) B2055665
theorem B1370455 : Blo 1368503 1370455 := bstep (se 1 (by rfl) ⟨1027841, by rfl⟩ : syracuseStep 1370455 = 2055683) B2055683
theorem B1370475 : Blo 1368503 1370475 := bstep (se 1 (by rfl) ⟨1027856, by rfl⟩ : syracuseStep 1370475 = 2055713) B2055713
theorem B1370487 : Blo 1368503 1370487 := bstep (se 1 (by rfl) ⟨1027865, by rfl⟩ : syracuseStep 1370487 = 2055731) B2055731
theorem B3082625 : Blo 1368503 3082625 := bstep (se 2 (by rfl) ⟨1155984, by rfl⟩ : syracuseStep 3082625 = 2311969) B2311969
theorem B2312651 : Blo 1368503 2312651 := bstep (se 1 (by rfl) ⟨1734488, by rfl⟩ : syracuseStep 2312651 = 3468977) B3468977
theorem B2599447 : Blo 1368503 2599447 := bstep (se 1 (by rfl) ⟨1949585, by rfl⟩ : syracuseStep 2599447 = 3899171) B3899171
theorem B2083403 : Blo 1368503 2083403 := bstep (se 1 (by rfl) ⟨1562552, by rfl⟩ : syracuseStep 2083403 = 3125105) B3125105
theorem B3082841 : Blo 1368503 3082841 := bstep (se 2 (by rfl) ⟨1156065, by rfl⟩ : syracuseStep 3082841 = 2312131) B2312131
theorem B2599553 : Blo 1368503 2599553 := bstep (se 2 (by rfl) ⟨974832, by rfl⟩ : syracuseStep 2599553 = 1949665) B1949665
theorem B5196419 : Blo 1368503 5196419 := bstep (se 1 (by rfl) ⟨3897314, by rfl⟩ : syracuseStep 5196419 = 7794629) B7794629
theorem B5196433 : Blo 1368503 5196433 := bstep (se 2 (by rfl) ⟨1948662, by rfl⟩ : syracuseStep 5196433 = 3897325) B3897325
theorem B3082931 : Blo 1368503 3082931 := bstep (se 1 (by rfl) ⟨2312198, by rfl⟩ : syracuseStep 3082931 = 4624397) B4624397
theorem B3082967 : Blo 1368503 3082967 := bstep (se 1 (by rfl) ⟨2312225, by rfl⟩ : syracuseStep 3082967 = 4624451) B4624451
theorem B5851865 : Blo 1368503 5851865 := bstep (se 2 (by rfl) ⟨2194449, by rfl⟩ : syracuseStep 5851865 = 4388899) B4388899
theorem B6007517 : Blo 1368503 6007517 := bstep (se 3 (by rfl) ⟨1126409, by rfl⟩ : syracuseStep 6007517 = 2252819) B2252819
theorem B3468055 : Blo 1368503 3468055 := bstep (se 1 (by rfl) ⟨2601041, by rfl⟩ : syracuseStep 3468055 = 5202083) B5202083
theorem B2599705 : Blo 1368503 2599705 := bstep (se 2 (by rfl) ⟨974889, by rfl⟩ : syracuseStep 2599705 = 1949779) B1949779
theorem B4623155 : Blo 1368503 4623155 := bstep (se 1 (by rfl) ⟨3467366, by rfl⟩ : syracuseStep 4623155 = 6934733) B6934733
theorem B3083147 : Blo 1368503 3083147 := bstep (se 1 (by rfl) ⟨2312360, by rfl⟩ : syracuseStep 3083147 = 4624721) B4624721
theorem B5196737 : Blo 1368503 5196737 := bstep (se 2 (by rfl) ⟨1948776, by rfl⟩ : syracuseStep 5196737 = 3897553) B3897553
theorem B3083201 : Blo 1368503 3083201 := bstep (se 2 (by rfl) ⟨1156200, by rfl⟩ : syracuseStep 3083201 = 2312401) B2312401
theorem B4623425 : Blo 1368503 4623425 := bstep (se 2 (by rfl) ⟨1733784, by rfl⟩ : syracuseStep 4623425 = 3467569) B3467569
theorem B3288215 : Blo 1368503 3288215 := bstep (se 1 (by rfl) ⟨2466161, by rfl⟩ : syracuseStep 3288215 = 4932323) B4932323
theorem B3083417 : Blo 1368503 3083417 := bstep (se 2 (by rfl) ⟨1156281, by rfl⟩ : syracuseStep 3083417 = 2312563) B2312563
theorem B3468491 : Blo 1368503 3468491 := bstep (se 1 (by rfl) ⟨2601368, by rfl⟩ : syracuseStep 3468491 = 5202737) B5202737
theorem B2813143 : Blo 1368503 2813143 := bstep (se 1 (by rfl) ⟨2109857, by rfl⟩ : syracuseStep 2813143 = 4219715) B4219715
theorem B1387735 : Blo 1368503 1387735 := bstep (se 1 (by rfl) ⟨1040801, by rfl⟩ : syracuseStep 1387735 = 2081603) B2081603
theorem B3083507 : Blo 1368503 3083507 := bstep (se 1 (by rfl) ⟨2312630, by rfl⟩ : syracuseStep 3083507 = 4625261) B4625261
theorem B3083543 : Blo 1368503 3083543 := bstep (se 1 (by rfl) ⟨2312657, by rfl⟩ : syracuseStep 3083543 = 4625315) B4625315
theorem B10407203 : Blo 1368503 10407203 := bstep (se 1 (by rfl) ⟨7805402, by rfl⟩ : syracuseStep 10407203 = 15610805) B15610805
theorem B35597717 : Blo 1368503 35597717 := bstep (se 6 (by rfl) ⟨834321, by rfl⟩ : syracuseStep 35597717 = 1668643) B1668643
theorem B1732043 : Blo 1368503 1732043 := bstep (se 1 (by rfl) ⟨1299032, by rfl⟩ : syracuseStep 1732043 = 2598065) B2598065
theorem B5000669 : Blo 1368503 5000669 := bstep (se 3 (by rfl) ⟨937625, by rfl⟩ : syracuseStep 5000669 = 1875251) B1875251
theorem B3468865 : Blo 1368503 3468865 := bstep (se 2 (by rfl) ⟨1300824, by rfl⟩ : syracuseStep 3468865 = 2601649) B2601649
theorem B1461835 : Blo 1368503 1461835 := bstep (se 1 (by rfl) ⟨1096376, by rfl⟩ : syracuseStep 1461835 = 2192753) B2192753
theorem B5197405 : Blo 1368503 5197405 := bstep (se 3 (by rfl) ⟨974513, by rfl⟩ : syracuseStep 5197405 = 1949027) B1949027
theorem B12496477 : Blo 1368503 12496477 := bstep (se 3 (by rfl) ⟨2343089, by rfl⟩ : syracuseStep 12496477 = 4686179) B4686179
theorem B4623965 : Blo 1368503 4623965 := bstep (se 3 (by rfl) ⟨866993, by rfl⟩ : syracuseStep 4623965 = 1733987) B1733987
theorem B5549771 : Blo 1368503 5549771 := bstep (se 1 (by rfl) ⟨4162328, by rfl⟩ : syracuseStep 5549771 = 8324657) B8324657
theorem B7802669 : Blo 1368503 7802669 := bstep (se 3 (by rfl) ⟨1463000, by rfl⟩ : syracuseStep 7802669 = 2926001) B2926001
theorem B5001049 : Blo 1368503 5001049 := bstep (se 2 (by rfl) ⟨1875393, by rfl⟩ : syracuseStep 5001049 = 3750787) B3750787
theorem B5853131 : Blo 1368503 5853131 := bstep (se 1 (by rfl) ⟨4389848, by rfl⟩ : syracuseStep 5853131 = 8779697) B8779697
theorem B2601011 : Blo 1368503 2601011 := bstep (se 1 (by rfl) ⟨1950758, by rfl⟩ : syracuseStep 2601011 = 3901517) B3901517
theorem B1732747 : Blo 1368503 1732747 := bstep (se 1 (by rfl) ⟨1299560, by rfl⟩ : syracuseStep 1732747 = 2599121) B2599121
theorem B2601163 : Blo 1368503 2601163 := bstep (se 1 (by rfl) ⟨1950872, by rfl⟩ : syracuseStep 2601163 = 3901745) B3901745
theorem B5853491 : Blo 1368503 5853491 := bstep (se 1 (by rfl) ⟨4390118, by rfl⟩ : syracuseStep 5853491 = 8780237) B8780237
theorem B3125633 : Blo 1368503 3125633 := bstep (se 2 (by rfl) ⟨1172112, by rfl⟩ : syracuseStep 3125633 = 2344225) B2344225
theorem B1733015 : Blo 1368503 1733015 := bstep (se 1 (by rfl) ⟨1299761, by rfl⟩ : syracuseStep 1733015 = 2599523) B2599523
theorem B22196753 : Blo 1368503 22196753 := bstep (se 2 (by rfl) ⟨8323782, by rfl⟩ : syracuseStep 22196753 = 16647565) B16647565
theorem B6935057 : Blo 1368503 6935057 := bstep (se 2 (by rfl) ⟨2600646, by rfl⟩ : syracuseStep 6935057 = 5201293) B5201293
theorem B2601497 : Blo 1368503 2601497 := bstep (se 2 (by rfl) ⟨975561, by rfl⟩ : syracuseStep 2601497 = 1951123) B1951123
theorem B3699265 : Blo 1368503 3699265 := bstep (se 2 (by rfl) ⟨1387224, by rfl⟩ : syracuseStep 3699265 = 2774449) B2774449
theorem B4878913 : Blo 1368503 4878913 := bstep (se 2 (by rfl) ⟨1829592, by rfl⟩ : syracuseStep 4878913 = 3659185) B3659185
theorem B2052761 : Blo 1368503 2052761 := bstep (se 2 (by rfl) ⟨769785, by rfl⟩ : syracuseStep 2052761 = 1539571) B1539571
theorem B7795379 : Blo 1368503 7795379 := bstep (se 1 (by rfl) ⟨5846534, by rfl⟩ : syracuseStep 7795379 = 11693069) B11693069
theorem B6935219 : Blo 1368503 6935219 := bstep (se 1 (by rfl) ⟨5201414, by rfl⟩ : syracuseStep 6935219 = 10402829) B10402829
theorem B4625099 : Blo 1368503 4625099 := bstep (se 1 (by rfl) ⟨3468824, by rfl⟩ : syracuseStep 4625099 = 6937649) B6937649
theorem B8770265 : Blo 1368503 8770265 := bstep (se 2 (by rfl) ⟨3288849, by rfl⟩ : syracuseStep 8770265 = 6577699) B6577699
theorem B2052875 : Blo 1368503 2052875 := bstep (se 1 (by rfl) ⟨1539656, by rfl⟩ : syracuseStep 2052875 = 3079313) B3079313
theorem B5845783 : Blo 1368503 5845783 := bstep (se 1 (by rfl) ⟨4384337, by rfl⟩ : syracuseStep 5845783 = 8768675) B8768675
theorem B2052887 : Blo 1368503 2052887 := bstep (se 1 (by rfl) ⟨1539665, by rfl⟩ : syracuseStep 2052887 = 3079331) B3079331
theorem B2052953 : Blo 1368503 2052953 := bstep (se 2 (by rfl) ⟨769857, by rfl⟩ : syracuseStep 2052953 = 1539715) B1539715
theorem B5198681 : Blo 1368503 5198681 := bstep (se 2 (by rfl) ⟨1949505, by rfl⟩ : syracuseStep 5198681 = 3899011) B3899011
theorem B42169187 : Blo 1368503 42169187 := bstep (se 1 (by rfl) ⟨31626890, by rfl⟩ : syracuseStep 42169187 = 63253781) B63253781
theorem B2053067 : Blo 1368503 2053067 := bstep (se 1 (by rfl) ⟨1539800, by rfl⟩ : syracuseStep 2053067 = 3079601) B3079601
theorem B2053079 : Blo 1368503 2053079 := bstep (se 1 (by rfl) ⟨1539809, by rfl⟩ : syracuseStep 2053079 = 3079619) B3079619
theorem B4625369 : Blo 1368503 4625369 := bstep (se 2 (by rfl) ⟨1734513, by rfl⟩ : syracuseStep 4625369 = 3469027) B3469027
theorem B2053145 : Blo 1368503 2053145 := bstep (se 2 (by rfl) ⟨769929, by rfl⟩ : syracuseStep 2053145 = 1539859) B1539859
theorem B1463351 : Blo 1368503 1463351 := bstep (se 1 (by rfl) ⟨1097513, by rfl⟩ : syracuseStep 1463351 = 2195027) B2195027
theorem B1733719 : Blo 1368503 1733719 := bstep (se 1 (by rfl) ⟨1300289, by rfl⟩ : syracuseStep 1733719 = 2600579) B2600579
theorem B2053259 : Blo 1368503 2053259 := bstep (se 1 (by rfl) ⟨1539944, by rfl⟩ : syracuseStep 2053259 = 3079889) B3079889
theorem B2053271 : Blo 1368503 2053271 := bstep (se 1 (by rfl) ⟨1539953, by rfl⟩ : syracuseStep 2053271 = 3079907) B3079907
theorem B3290291 : Blo 1368503 3290291 := bstep (se 1 (by rfl) ⟨2467718, by rfl⟩ : syracuseStep 3290291 = 4935437) B4935437
theorem B2192599 : Blo 1368503 2192599 := bstep (se 1 (by rfl) ⟨1644449, by rfl⟩ : syracuseStep 2192599 = 3288899) B3288899
theorem B2053337 : Blo 1368503 2053337 := bstep (se 2 (by rfl) ⟨770001, by rfl⟩ : syracuseStep 2053337 = 1540003) B1540003
theorem B2053451 : Blo 1368503 2053451 := bstep (se 1 (by rfl) ⟨1540088, by rfl⟩ : syracuseStep 2053451 = 3080177) B3080177
theorem B2053463 : Blo 1368503 2053463 := bstep (se 1 (by rfl) ⟨1540097, by rfl⟩ : syracuseStep 2053463 = 3080195) B3080195
theorem B2053529 : Blo 1368503 2053529 := bstep (se 2 (by rfl) ⟨770073, by rfl⟩ : syracuseStep 2053529 = 1540147) B1540147
theorem B12490163 : Blo 1368503 12490163 := bstep (se 1 (by rfl) ⟨9367622, by rfl⟩ : syracuseStep 12490163 = 18735245) B18735245
theorem B2053643 : Blo 1368503 2053643 := bstep (se 1 (by rfl) ⟨1540232, by rfl⟩ : syracuseStep 2053643 = 3080465) B3080465
theorem B2053655 : Blo 1368503 2053655 := bstep (se 1 (by rfl) ⟨1540241, by rfl⟩ : syracuseStep 2053655 = 3080483) B3080483
theorem B2053721 : Blo 1368503 2053721 := bstep (se 2 (by rfl) ⟨770145, by rfl⟩ : syracuseStep 2053721 = 1540291) B1540291
theorem B2053835 : Blo 1368503 2053835 := bstep (se 1 (by rfl) ⟨1540376, by rfl⟩ : syracuseStep 2053835 = 3080753) B3080753
theorem B2053847 : Blo 1368503 2053847 := bstep (se 1 (by rfl) ⟨1540385, by rfl⟩ : syracuseStep 2053847 = 3080771) B3080771
theorem B4167389 : Blo 1368503 4167389 := bstep (se 3 (by rfl) ⟨781385, by rfl⟩ : syracuseStep 4167389 = 1562771) B1562771
theorem B7124753 : Blo 1368503 7124753 := bstep (se 2 (by rfl) ⟨2671782, by rfl⟩ : syracuseStep 7124753 = 5343565) B5343565
theorem B2053913 : Blo 1368503 2053913 := bstep (se 2 (by rfl) ⟨770217, by rfl⟩ : syracuseStep 2053913 = 1540435) B1540435
theorem B47404865 : Blo 1368503 47404865 := bstep (se 2 (by rfl) ⟨17776824, by rfl⟩ : syracuseStep 47404865 = 35553649) B35553649
theorem B2054027 : Blo 1368503 2054027 := bstep (se 1 (by rfl) ⟨1540520, by rfl⟩ : syracuseStep 2054027 = 3081041) B3081041
theorem B2054039 : Blo 1368503 2054039 := bstep (se 1 (by rfl) ⟨1540529, by rfl⟩ : syracuseStep 2054039 = 3081059) B3081059
theorem B2054105 : Blo 1368503 2054105 := bstep (se 2 (by rfl) ⟨770289, by rfl⟩ : syracuseStep 2054105 = 1540579) B1540579
theorem B2193419 : Blo 1368503 2193419 := bstep (se 1 (by rfl) ⟨1645064, by rfl⟩ : syracuseStep 2193419 = 3290129) B3290129
theorem B10401857 : Blo 1368503 10401857 := bstep (se 2 (by rfl) ⟨3900696, by rfl⟩ : syracuseStep 10401857 = 7801393) B7801393
theorem B64968779 : Blo 1368503 64968779 := bstep (se 1 (by rfl) ⟨48726584, by rfl⟩ : syracuseStep 64968779 = 97453169) B97453169
theorem B2054219 : Blo 1368503 2054219 := bstep (se 1 (by rfl) ⟨1540664, by rfl⟩ : syracuseStep 2054219 = 3081329) B3081329
theorem B2054231 : Blo 1368503 2054231 := bstep (se 1 (by rfl) ⟨1540673, by rfl⟩ : syracuseStep 2054231 = 3081347) B3081347
theorem B5552221 : Blo 1368503 5552221 := bstep (se 3 (by rfl) ⟨1041041, by rfl⟩ : syracuseStep 5552221 = 2082083) B2082083
theorem B7796837 : Blo 1368503 7796837 := bstep (se 4 (by rfl) ⟨730953, by rfl⟩ : syracuseStep 7796837 = 1461907) B1461907
theorem B3954839 : Blo 1368503 3954839 := bstep (se 1 (by rfl) ⟨2966129, by rfl⟩ : syracuseStep 3954839 = 5932259) B5932259
theorem B2054297 : Blo 1368503 2054297 := bstep (se 2 (by rfl) ⟨770361, by rfl⟩ : syracuseStep 2054297 = 1540723) B1540723
theorem B3291329 : Blo 1368503 3291329 := bstep (se 2 (by rfl) ⟨1234248, by rfl⟩ : syracuseStep 3291329 = 2468497) B2468497
theorem B2054411 : Blo 1368503 2054411 := bstep (se 1 (by rfl) ⟨1540808, by rfl⟩ : syracuseStep 2054411 = 3081617) B3081617
theorem B5552401 : Blo 1368503 5552401 := bstep (se 2 (by rfl) ⟨2082150, by rfl⟩ : syracuseStep 5552401 = 4164301) B4164301
theorem B2054423 : Blo 1368503 2054423 := bstep (se 1 (by rfl) ⟨1540817, by rfl⟩ : syracuseStep 2054423 = 3081635) B3081635
theorem B2054489 : Blo 1368503 2054489 := bstep (se 2 (by rfl) ⟨770433, by rfl⟩ : syracuseStep 2054489 = 1540867) B1540867
theorem B5003651 : Blo 1368503 5003651 := bstep (se 1 (by rfl) ⟨3752738, by rfl⟩ : syracuseStep 5003651 = 7505477) B7505477
theorem B5200307 : Blo 1368503 5200307 := bstep (se 1 (by rfl) ⟨3900230, by rfl⟩ : syracuseStep 5200307 = 7800461) B7800461
theorem B4389299 : Blo 1368503 4389299 := bstep (se 1 (by rfl) ⟨3291974, by rfl⟩ : syracuseStep 4389299 = 6583949) B6583949
theorem B5200321 : Blo 1368503 5200321 := bstep (se 2 (by rfl) ⟨1950120, by rfl⟩ : syracuseStep 5200321 = 3900241) B3900241
theorem B2054603 : Blo 1368503 2054603 := bstep (se 1 (by rfl) ⟨1540952, by rfl⟩ : syracuseStep 2054603 = 3081905) B3081905
theorem B2054615 : Blo 1368503 2054615 := bstep (se 1 (by rfl) ⟨1540961, by rfl⟩ : syracuseStep 2054615 = 3081923) B3081923
theorem B4938205 : Blo 1368503 4938205 := bstep (se 3 (by rfl) ⟨925913, by rfl⟩ : syracuseStep 4938205 = 1851827) B1851827
theorem B2054681 : Blo 1368503 2054681 := bstep (se 2 (by rfl) ⟨770505, by rfl⟩ : syracuseStep 2054681 = 1541011) B1541011
theorem B17553955 : Blo 1368503 17553955 := bstep (se 1 (by rfl) ⟨13165466, by rfl⟩ : syracuseStep 17553955 = 26330933) B26330933
theorem B7797293 : Blo 1368503 7797293 := bstep (se 3 (by rfl) ⟨1461992, by rfl⟩ : syracuseStep 7797293 = 2923985) B2923985
theorem B6937163 : Blo 1368503 6937163 := bstep (se 1 (by rfl) ⟨5202872, by rfl⟩ : syracuseStep 6937163 = 10405745) B10405745
theorem B2923123 : Blo 1368503 2923123 := bstep (se 1 (by rfl) ⟨2192342, by rfl⟩ : syracuseStep 2923123 = 4384685) B4384685
theorem B2054795 : Blo 1368503 2054795 := bstep (se 1 (by rfl) ⟨1541096, by rfl⟩ : syracuseStep 2054795 = 3082193) B3082193
theorem B2054807 : Blo 1368503 2054807 := bstep (se 1 (by rfl) ⟨1541105, by rfl⟩ : syracuseStep 2054807 = 3082211) B3082211
theorem B2054873 : Blo 1368503 2054873 := bstep (se 2 (by rfl) ⟨770577, by rfl⟩ : syracuseStep 2054873 = 1541155) B1541155
theorem B2054987 : Blo 1368503 2054987 := bstep (se 1 (by rfl) ⟨1541240, by rfl⟩ : syracuseStep 2054987 = 3082481) B3082481
theorem B2054999 : Blo 1368503 2054999 := bstep (se 1 (by rfl) ⟨1541249, by rfl⟩ : syracuseStep 2054999 = 3082499) B3082499
theorem B4619159 : Blo 1368503 4619159 := bstep (se 1 (by rfl) ⟨3464369, by rfl⟩ : syracuseStep 4619159 = 6928739) B6928739
theorem B2055065 : Blo 1368503 2055065 := bstep (se 2 (by rfl) ⟨770649, by rfl⟩ : syracuseStep 2055065 = 1541299) B1541299
theorem B8780723 : Blo 1368503 8780723 := bstep (se 1 (by rfl) ⟨6585542, by rfl⟩ : syracuseStep 8780723 = 13171085) B13171085
theorem B2194393 : Blo 1368503 2194393 := bstep (se 2 (by rfl) ⟨822897, by rfl⟩ : syracuseStep 2194393 = 1645795) B1645795
theorem B3079169 : Blo 1368503 3079169 := bstep (se 2 (by rfl) ⟨1154688, by rfl⟩ : syracuseStep 3079169 = 2309377) B2309377
theorem B2055179 : Blo 1368503 2055179 := bstep (se 1 (by rfl) ⟨1541384, by rfl⟩ : syracuseStep 2055179 = 3082769) B3082769
theorem B11697169 : Blo 1368503 11697169 := bstep (se 2 (by rfl) ⟨4386438, by rfl⟩ : syracuseStep 11697169 = 8772877) B8772877
theorem B2055191 : Blo 1368503 2055191 := bstep (se 1 (by rfl) ⟨1541393, by rfl⟩ : syracuseStep 2055191 = 3082787) B3082787
theorem B1850455 : Blo 1368503 1850455 := bstep (se 1 (by rfl) ⟨1387841, by rfl⟩ : syracuseStep 1850455 = 2775683) B2775683
theorem B2923609 : Blo 1368503 2923609 := bstep (se 2 (by rfl) ⟨1096353, by rfl⟩ : syracuseStep 2923609 = 2192707) B2192707
theorem B1645655 : Blo 1368503 1645655 := bstep (se 1 (by rfl) ⟨1234241, by rfl⟩ : syracuseStep 1645655 = 2468483) B2468483
theorem B4447325 : Blo 1368503 4447325 := bstep (se 3 (by rfl) ⟨833873, by rfl⟩ : syracuseStep 4447325 = 1667747) B1667747
theorem B2055257 : Blo 1368503 2055257 := bstep (se 2 (by rfl) ⟨770721, by rfl⟩ : syracuseStep 2055257 = 1541443) B1541443
theorem B4389977 : Blo 1368503 4389977 := bstep (se 2 (by rfl) ⟨1646241, by rfl⟩ : syracuseStep 4389977 = 3292483) B3292483
theorem B7404695 : Blo 1368503 7404695 := bstep (se 1 (by rfl) ⟨5553521, by rfl⟩ : syracuseStep 7404695 = 11107043) B11107043
theorem B1645771 : Blo 1368503 1645771 := bstep (se 1 (by rfl) ⟨1234328, by rfl⟩ : syracuseStep 1645771 = 2468657) B2468657
theorem B2055371 : Blo 1368503 2055371 := bstep (se 1 (by rfl) ⟨1541528, by rfl⟩ : syracuseStep 2055371 = 3083057) B3083057
theorem B2055383 : Blo 1368503 2055383 := bstep (se 1 (by rfl) ⟨1541537, by rfl⟩ : syracuseStep 2055383 = 3083075) B3083075
theorem B3079385 : Blo 1368503 3079385 := bstep (se 2 (by rfl) ⟨1154769, by rfl⟩ : syracuseStep 3079385 = 2309539) B2309539
theorem B7797977 : Blo 1368503 7797977 := bstep (se 2 (by rfl) ⟨2924241, by rfl⟩ : syracuseStep 7797977 = 5848483) B5848483
theorem B3464471 : Blo 1368503 3464471 := bstep (se 1 (by rfl) ⟨2598353, by rfl⟩ : syracuseStep 3464471 = 5196707) B5196707
theorem B2055449 : Blo 1368503 2055449 := bstep (se 2 (by rfl) ⟨770793, by rfl⟩ : syracuseStep 2055449 = 1541587) B1541587
theorem B11697443 : Blo 1368503 11697443 := bstep (se 1 (by rfl) ⟨8773082, by rfl⟩ : syracuseStep 11697443 = 17546165) B17546165
theorem B3079475 : Blo 1368503 3079475 := bstep (se 1 (by rfl) ⟨2309606, by rfl⟩ : syracuseStep 3079475 = 4619213) B4619213
theorem B4750643 : Blo 1368503 4750643 := bstep (se 1 (by rfl) ⟨3562982, by rfl⟩ : syracuseStep 4750643 = 7125965) B7125965
theorem B3079511 : Blo 1368503 3079511 := bstep (se 1 (by rfl) ⟨2309633, by rfl⟩ : syracuseStep 3079511 = 4619267) B4619267
theorem B2309465 : Blo 1368503 2309465 := bstep (se 2 (by rfl) ⟨866049, by rfl⟩ : syracuseStep 2309465 = 1732099) B1732099
theorem B2055563 : Blo 1368503 2055563 := bstep (se 1 (by rfl) ⟨1541672, by rfl⟩ : syracuseStep 2055563 = 3083345) B3083345
theorem B2055575 : Blo 1368503 2055575 := bstep (se 1 (by rfl) ⟨1541681, by rfl⟩ : syracuseStep 2055575 = 3083363) B3083363
theorem B4619699 : Blo 1368503 4619699 := bstep (se 1 (by rfl) ⟨3464774, by rfl⟩ : syracuseStep 4619699 = 6929549) B6929549
theorem B71130581 : Blo 1368503 71130581 := bstep (se 7 (by rfl) ⟨833561, by rfl⟩ : syracuseStep 71130581 = 1667123) B1667123
theorem B2309593 : Blo 1368503 2309593 := bstep (se 2 (by rfl) ⟨866097, by rfl⟩ : syracuseStep 2309593 = 1732195) B1732195
theorem B2055641 : Blo 1368503 2055641 := bstep (se 2 (by rfl) ⟨770865, by rfl⟩ : syracuseStep 2055641 = 1541731) B1541731
theorem B3079691 : Blo 1368503 3079691 := bstep (se 1 (by rfl) ⟨2309768, by rfl⟩ : syracuseStep 3079691 = 4619537) B4619537
theorem B1539607 : Blo 1368503 1539607 := bstep (se 1 (by rfl) ⟨1154705, by rfl⟩ : syracuseStep 1539607 = 2309411) B2309411
theorem B3079745 : Blo 1368503 3079745 := bstep (se 2 (by rfl) ⟨1154904, by rfl⟩ : syracuseStep 3079745 = 2309809) B2309809
theorem B3898955 : Blo 1368503 3898955 := bstep (se 1 (by rfl) ⟨2924216, by rfl⟩ : syracuseStep 3898955 = 5848433) B5848433
theorem B2055755 : Blo 1368503 2055755 := bstep (se 1 (by rfl) ⟨1541816, by rfl⟩ : syracuseStep 2055755 = 3083633) B3083633
theorem B6250135 : Blo 1368503 6250135 := bstep (se 1 (by rfl) ⟨4687601, by rfl⟩ : syracuseStep 6250135 = 9375203) B9375203
theorem B4619969 : Blo 1368503 4619969 := bstep (se 2 (by rfl) ⟨1732488, by rfl⟩ : syracuseStep 4619969 = 3464977) B3464977
theorem B1539787 : Blo 1368503 1539787 := bstep (se 1 (by rfl) ⟨1154840, by rfl⟩ : syracuseStep 1539787 = 2309681) B2309681
theorem B3079961 : Blo 1368503 3079961 := bstep (se 2 (by rfl) ⟨1154985, by rfl⟩ : syracuseStep 3079961 = 2309971) B2309971
theorem B1539895 : Blo 1368503 1539895 := bstep (se 1 (by rfl) ⟨1154921, by rfl⟩ : syracuseStep 1539895 = 2309843) B2309843
theorem B2924353 : Blo 1368503 2924353 := bstep (se 2 (by rfl) ⟨1096632, by rfl⟩ : syracuseStep 2924353 = 2193265) B2193265
theorem B3080051 : Blo 1368503 3080051 := bstep (se 1 (by rfl) ⟨2310038, by rfl⟩ : syracuseStep 3080051 = 4620077) B4620077
theorem B3080087 : Blo 1368503 3080087 := bstep (se 1 (by rfl) ⟨2310065, by rfl⟩ : syracuseStep 3080087 = 4620131) B4620131
theorem B3465139 : Blo 1368503 3465139 := bstep (se 1 (by rfl) ⟨2598854, by rfl⟩ : syracuseStep 3465139 = 5197709) B5197709
theorem B3899353 : Blo 1368503 3899353 := bstep (se 2 (by rfl) ⟨1462257, by rfl⟩ : syracuseStep 3899353 = 2924515) B2924515
theorem B10403801 : Blo 1368503 10403801 := bstep (se 2 (by rfl) ⟨3901425, by rfl⟩ : syracuseStep 10403801 = 7802851) B7802851
theorem B1540075 : Blo 1368503 1540075 := bstep (se 1 (by rfl) ⟨1155056, by rfl⟩ : syracuseStep 1540075 = 2310113) B2310113
theorem B2080775 : Blo 1368503 2080775 := bstep (se 1 (by rfl) ⟨1560581, by rfl⟩ : syracuseStep 2080775 = 3121163) B3121163
theorem B1540111 : Blo 1368503 1540111 := bstep (se 1 (by rfl) ⟨1155083, by rfl⟩ : syracuseStep 1540111 = 2310167) B2310167
theorem B5849117 : Blo 1368503 5849117 := bstep (se 3 (by rfl) ⟨1096709, by rfl⟩ : syracuseStep 5849117 = 2193419) B2193419
theorem B2310187 : Blo 1368503 2310187 := bstep (se 1 (by rfl) ⟨1732640, by rfl⟩ : syracuseStep 2310187 = 3465281) B3465281
theorem B3080339 : Blo 1368503 3080339 := bstep (se 1 (by rfl) ⟨2310254, by rfl⟩ : syracuseStep 3080339 = 4620509) B4620509
theorem B23396525 : Blo 1368503 23396525 := bstep (se 3 (by rfl) ⟨4386848, by rfl⟩ : syracuseStep 23396525 = 8773697) B8773697
theorem B2310329 : Blo 1368503 2310329 := bstep (se 2 (by rfl) ⟨866373, by rfl⟩ : syracuseStep 2310329 = 1732747) B1732747
theorem B3080393 : Blo 1368503 3080393 := bstep (se 2 (by rfl) ⟨1155147, by rfl⟩ : syracuseStep 3080393 = 2310295) B2310295
theorem B3465625 : Blo 1368503 3465625 := bstep (se 2 (by rfl) ⟨1299609, by rfl⟩ : syracuseStep 3465625 = 2599219) B2599219
theorem B1368507 : Blo 1368503 1368507 := bstep (se 1 (by rfl) ⟨1026380, by rfl⟩ : syracuseStep 1368507 = 2052761) B2052761
theorem B1368583 : Blo 1368503 1368583 := bstep (se 1 (by rfl) ⟨1026437, by rfl⟩ : syracuseStep 1368583 = 2052875) B2052875
theorem B1540615 : Blo 1368503 1540615 := bstep (se 1 (by rfl) ⟨1155461, by rfl⟩ : syracuseStep 1540615 = 2310923) B2310923
theorem B1368591 : Blo 1368503 1368591 := bstep (se 1 (by rfl) ⟨1026443, by rfl⟩ : syracuseStep 1368591 = 2052887) B2052887
theorem B1368635 : Blo 1368503 1368635 := bstep (se 1 (by rfl) ⟨1026476, by rfl⟩ : syracuseStep 1368635 = 2052953) B2052953
theorem B3465787 : Blo 1368503 3465787 := bstep (se 1 (by rfl) ⟨2599340, by rfl⟩ : syracuseStep 3465787 = 5198681) B5198681
theorem B4620887 : Blo 1368503 4620887 := bstep (se 1 (by rfl) ⟨3465665, by rfl⟩ : syracuseStep 4620887 = 6931331) B6931331
theorem B1368711 : Blo 1368503 1368711 := bstep (se 1 (by rfl) ⟨1026533, by rfl⟩ : syracuseStep 1368711 = 2053067) B2053067
theorem B1368719 : Blo 1368503 1368719 := bstep (se 1 (by rfl) ⟨1026539, by rfl⟩ : syracuseStep 1368719 = 2053079) B2053079
theorem B1368763 : Blo 1368503 1368763 := bstep (se 1 (by rfl) ⟨1026572, by rfl⟩ : syracuseStep 1368763 = 2053145) B2053145
theorem B1540795 : Blo 1368503 1540795 := bstep (se 1 (by rfl) ⟨1155596, by rfl⟩ : syracuseStep 1540795 = 2311193) B2311193
theorem B3465929 : Blo 1368503 3465929 := bstep (se 2 (by rfl) ⟨1299723, by rfl⟩ : syracuseStep 3465929 = 2599447) B2599447
theorem B23405273 : Blo 1368503 23405273 := bstep (se 2 (by rfl) ⟨8776977, by rfl⟩ : syracuseStep 23405273 = 17553955) B17553955
theorem B4932353 : Blo 1368503 4932353 := bstep (se 2 (by rfl) ⟨1849632, by rfl⟩ : syracuseStep 4932353 = 3699265) B3699265
theorem B6505217 : Blo 1368503 6505217 := bstep (se 2 (by rfl) ⟨2439456, by rfl⟩ : syracuseStep 6505217 = 4878913) B4878913
theorem B1368839 : Blo 1368503 1368839 := bstep (se 1 (by rfl) ⟨1026629, by rfl⟩ : syracuseStep 1368839 = 2053259) B2053259
theorem B1368847 : Blo 1368503 1368847 := bstep (se 1 (by rfl) ⟨1026635, by rfl⟩ : syracuseStep 1368847 = 2053271) B2053271
theorem B1368891 : Blo 1368503 1368891 := bstep (se 1 (by rfl) ⟨1026668, by rfl⟩ : syracuseStep 1368891 = 2053337) B2053337
theorem B2311031 : Blo 1368503 2311031 := bstep (se 1 (by rfl) ⟨1733273, by rfl⟩ : syracuseStep 2311031 = 3466547) B3466547
theorem B1368967 : Blo 1368503 1368967 := bstep (se 1 (by rfl) ⟨1026725, by rfl⟩ : syracuseStep 1368967 = 2053451) B2053451
theorem B3081095 : Blo 1368503 3081095 := bstep (se 1 (by rfl) ⟨2310821, by rfl⟩ : syracuseStep 3081095 = 4621643) B4621643
theorem B1950599 : Blo 1368503 1950599 := bstep (se 1 (by rfl) ⟨1462949, by rfl⟩ : syracuseStep 1950599 = 2925899) B2925899
theorem B1368975 : Blo 1368503 1368975 := bstep (se 1 (by rfl) ⟨1026731, by rfl⟩ : syracuseStep 1368975 = 2053463) B2053463
theorem B1369019 : Blo 1368503 1369019 := bstep (se 1 (by rfl) ⟨1026764, by rfl⟩ : syracuseStep 1369019 = 2053529) B2053529
theorem B1369095 : Blo 1368503 1369095 := bstep (se 1 (by rfl) ⟨1026821, by rfl⟩ : syracuseStep 1369095 = 2053643) B2053643
theorem B1369103 : Blo 1368503 1369103 := bstep (se 1 (by rfl) ⟨1026827, by rfl⟩ : syracuseStep 1369103 = 2053655) B2053655
theorem B3466273 : Blo 1368503 3466273 := bstep (se 2 (by rfl) ⟨1299852, by rfl⟩ : syracuseStep 3466273 = 2599705) B2599705
theorem B1369147 : Blo 1368503 1369147 := bstep (se 1 (by rfl) ⟨1026860, by rfl⟩ : syracuseStep 1369147 = 2053721) B2053721
theorem B3081275 : Blo 1368503 3081275 := bstep (se 1 (by rfl) ⟨2310956, by rfl⟩ : syracuseStep 3081275 = 4621913) B4621913
theorem B4621373 : Blo 1368503 4621373 := bstep (se 3 (by rfl) ⟨866507, by rfl⟩ : syracuseStep 4621373 = 1733015) B1733015
theorem B3753047 : Blo 1368503 3753047 := bstep (se 1 (by rfl) ⟨2814785, by rfl⟩ : syracuseStep 3753047 = 5629571) B5629571
theorem B1369223 : Blo 1368503 1369223 := bstep (se 1 (by rfl) ⟨1026917, by rfl⟩ : syracuseStep 1369223 = 2053835) B2053835
theorem B1369231 : Blo 1368503 1369231 := bstep (se 1 (by rfl) ⟨1026923, by rfl⟩ : syracuseStep 1369231 = 2053847) B2053847
theorem B1541263 : Blo 1368503 1541263 := bstep (se 1 (by rfl) ⟨1155947, by rfl⟩ : syracuseStep 1541263 = 2311895) B2311895
theorem B4162745 : Blo 1368503 4162745 := bstep (se 2 (by rfl) ⟨1561029, by rfl⟩ : syracuseStep 4162745 = 3122059) B3122059
theorem B3081401 : Blo 1368503 3081401 := bstep (se 2 (by rfl) ⟨1155525, by rfl⟩ : syracuseStep 3081401 = 2311051) B2311051
theorem B1369275 : Blo 1368503 1369275 := bstep (se 1 (by rfl) ⟨1026956, by rfl⟩ : syracuseStep 1369275 = 2053913) B2053913
theorem B1950907 : Blo 1368503 1950907 := bstep (se 1 (by rfl) ⟨1463180, by rfl⟩ : syracuseStep 1950907 = 2926361) B2926361
theorem B1369351 : Blo 1368503 1369351 := bstep (se 1 (by rfl) ⟨1027013, by rfl⟩ : syracuseStep 1369351 = 2054027) B2054027
theorem B1369359 : Blo 1368503 1369359 := bstep (se 1 (by rfl) ⟨1027019, by rfl⟩ : syracuseStep 1369359 = 2054039) B2054039
theorem B2925857 : Blo 1368503 2925857 := bstep (se 2 (by rfl) ⟨1097196, by rfl⟩ : syracuseStep 2925857 = 2194393) B2194393
theorem B1369403 : Blo 1368503 1369403 := bstep (se 1 (by rfl) ⟨1027052, by rfl⟩ : syracuseStep 1369403 = 2054105) B2054105
theorem B2311483 : Blo 1368503 2311483 := bstep (se 1 (by rfl) ⟨1733612, by rfl⟩ : syracuseStep 2311483 = 3467225) B3467225
theorem B8324441 : Blo 1368503 8324441 := bstep (se 2 (by rfl) ⟨3121665, by rfl⟩ : syracuseStep 8324441 = 6243331) B6243331
theorem B43312519 : Blo 1368503 43312519 := bstep (se 1 (by rfl) ⟨32484389, by rfl⟩ : syracuseStep 43312519 = 64968779) B64968779
theorem B1369479 : Blo 1368503 1369479 := bstep (se 1 (by rfl) ⟨1027109, by rfl⟩ : syracuseStep 1369479 = 2054219) B2054219
theorem B1369487 : Blo 1368503 1369487 := bstep (se 1 (by rfl) ⟨1027115, by rfl⟩ : syracuseStep 1369487 = 2054231) B2054231
theorem B7800209 : Blo 1368503 7800209 := bstep (se 2 (by rfl) ⟨2925078, by rfl⟩ : syracuseStep 7800209 = 5850157) B5850157
theorem B2082235 : Blo 1368503 2082235 := bstep (se 1 (by rfl) ⟨1561676, by rfl⟩ : syracuseStep 2082235 = 3123353) B3123353
theorem B1369531 : Blo 1368503 1369531 := bstep (se 1 (by rfl) ⟨1027148, by rfl⟩ : syracuseStep 1369531 = 2054297) B2054297
theorem B2467273 : Blo 1368503 2467273 := bstep (se 2 (by rfl) ⟨925227, by rfl⟩ : syracuseStep 2467273 = 1850455) B1850455
theorem B2311625 : Blo 1368503 2311625 := bstep (se 2 (by rfl) ⟨866859, by rfl⟩ : syracuseStep 2311625 = 1733719) B1733719
theorem B1369607 : Blo 1368503 1369607 := bstep (se 1 (by rfl) ⟨1027205, by rfl⟩ : syracuseStep 1369607 = 2054411) B2054411
theorem B6931979 : Blo 1368503 6931979 := bstep (se 1 (by rfl) ⟨5198984, by rfl⟩ : syracuseStep 6931979 = 10397969) B10397969
theorem B1369615 : Blo 1368503 1369615 := bstep (se 1 (by rfl) ⟨1027211, by rfl⟩ : syracuseStep 1369615 = 2054423) B2054423
theorem B3081743 : Blo 1368503 3081743 := bstep (se 1 (by rfl) ⟨2311307, by rfl⟩ : syracuseStep 3081743 = 4622615) B4622615
theorem B3081761 : Blo 1368503 3081761 := bstep (se 2 (by rfl) ⟨1155660, by rfl⟩ : syracuseStep 3081761 = 2311321) B2311321
theorem B1369659 : Blo 1368503 1369659 := bstep (se 1 (by rfl) ⟨1027244, by rfl⟩ : syracuseStep 1369659 = 2054489) B2054489
theorem B3466871 : Blo 1368503 3466871 := bstep (se 1 (by rfl) ⟨2600153, by rfl⟩ : syracuseStep 3466871 = 5200307) B5200307
theorem B2926199 : Blo 1368503 2926199 := bstep (se 1 (by rfl) ⟨2194649, by rfl⟩ : syracuseStep 2926199 = 4389299) B4389299
theorem B1369735 : Blo 1368503 1369735 := bstep (se 1 (by rfl) ⟨1027301, by rfl⟩ : syracuseStep 1369735 = 2054603) B2054603
theorem B1541767 : Blo 1368503 1541767 := bstep (se 1 (by rfl) ⟨1156325, by rfl⟩ : syracuseStep 1541767 = 2312651) B2312651
theorem B1369743 : Blo 1368503 1369743 := bstep (se 1 (by rfl) ⟨1027307, by rfl⟩ : syracuseStep 1369743 = 2054615) B2054615
theorem B6932141 : Blo 1368503 6932141 := bstep (se 3 (by rfl) ⟨1299776, by rfl⟩ : syracuseStep 6932141 = 2599553) B2599553
theorem B1369787 : Blo 1368503 1369787 := bstep (se 1 (by rfl) ⟨1027340, by rfl⟩ : syracuseStep 1369787 = 2054681) B2054681
theorem B1369863 : Blo 1368503 1369863 := bstep (se 1 (by rfl) ⟨1027397, by rfl⟩ : syracuseStep 1369863 = 2054795) B2054795
theorem B1369871 : Blo 1368503 1369871 := bstep (se 1 (by rfl) ⟨1027403, by rfl⟩ : syracuseStep 1369871 = 2054807) B2054807
theorem B1369915 : Blo 1368503 1369915 := bstep (se 1 (by rfl) ⟨1027436, by rfl⟩ : syracuseStep 1369915 = 2054873) B2054873
theorem B3082103 : Blo 1368503 3082103 := bstep (se 1 (by rfl) ⟨2311577, by rfl⟩ : syracuseStep 3082103 = 4623155) B4623155
theorem B1369991 : Blo 1368503 1369991 := bstep (se 1 (by rfl) ⟨1027493, by rfl⟩ : syracuseStep 1369991 = 2054987) B2054987
theorem B1369999 : Blo 1368503 1369999 := bstep (se 1 (by rfl) ⟨1027499, by rfl⟩ : syracuseStep 1369999 = 2054999) B2054999
theorem B1370043 : Blo 1368503 1370043 := bstep (se 1 (by rfl) ⟨1027532, by rfl⟩ : syracuseStep 1370043 = 2055065) B2055065
theorem B1370119 : Blo 1368503 1370119 := bstep (se 1 (by rfl) ⟨1027589, by rfl⟩ : syracuseStep 1370119 = 2055179) B2055179
theorem B1370127 : Blo 1368503 1370127 := bstep (se 1 (by rfl) ⟨1027595, by rfl⟩ : syracuseStep 1370127 = 2055191) B2055191
theorem B3082283 : Blo 1368503 3082283 := bstep (se 1 (by rfl) ⟨2311712, by rfl⟩ : syracuseStep 3082283 = 4623425) B4623425
theorem B18999341 : Blo 1368503 18999341 := bstep (se 3 (by rfl) ⟨3562376, by rfl⟩ : syracuseStep 18999341 = 7124753) B7124753
theorem B1370171 : Blo 1368503 1370171 := bstep (se 1 (by rfl) ⟨1027628, by rfl⟩ : syracuseStep 1370171 = 2055257) B2055257
theorem B2926651 : Blo 1368503 2926651 := bstep (se 1 (by rfl) ⟨2194988, by rfl⟩ : syracuseStep 2926651 = 4389977) B4389977
theorem B7800893 : Blo 1368503 7800893 := bstep (se 3 (by rfl) ⟨1462667, by rfl⟩ : syracuseStep 7800893 = 2925335) B2925335
theorem B1370247 : Blo 1368503 1370247 := bstep (se 1 (by rfl) ⟨1027685, by rfl⟩ : syracuseStep 1370247 = 2055371) B2055371
theorem B2312327 : Blo 1368503 2312327 := bstep (se 1 (by rfl) ⟨1734245, by rfl⟩ : syracuseStep 2312327 = 3468491) B3468491
theorem B1370255 : Blo 1368503 1370255 := bstep (se 1 (by rfl) ⟨1027691, by rfl⟩ : syracuseStep 1370255 = 2055383) B2055383
theorem B126412973 : Blo 1368503 126412973 := bstep (se 3 (by rfl) ⟨23702432, by rfl⟩ : syracuseStep 126412973 = 47404865) B47404865
theorem B1370299 : Blo 1368503 1370299 := bstep (se 1 (by rfl) ⟨1027724, by rfl⟩ : syracuseStep 1370299 = 2055449) B2055449
theorem B8333513 : Blo 1368503 8333513 := bstep (se 2 (by rfl) ⟨3125067, by rfl⟩ : syracuseStep 8333513 = 6250135) B6250135
theorem B1370375 : Blo 1368503 1370375 := bstep (se 1 (by rfl) ⟨1027781, by rfl⟩ : syracuseStep 1370375 = 2055563) B2055563
theorem B1370383 : Blo 1368503 1370383 := bstep (se 1 (by rfl) ⟨1027787, by rfl⟩ : syracuseStep 1370383 = 2055575) B2055575
theorem B1370427 : Blo 1368503 1370427 := bstep (se 1 (by rfl) ⟨1027820, by rfl⟩ : syracuseStep 1370427 = 2055641) B2055641
theorem B2599303 : Blo 1368503 2599303 := bstep (se 1 (by rfl) ⟨1949477, by rfl⟩ : syracuseStep 2599303 = 3898955) B3898955
theorem B1370503 : Blo 1368503 1370503 := bstep (se 1 (by rfl) ⟨1027877, by rfl⟩ : syracuseStep 1370503 = 2055755) B2055755
theorem B3082643 : Blo 1368503 3082643 := bstep (se 1 (by rfl) ⟨2311982, by rfl⟩ : syracuseStep 3082643 = 4623965) B4623965
theorem B4622777 : Blo 1368503 4622777 := bstep (se 2 (by rfl) ⟨1733541, by rfl⟩ : syracuseStep 4622777 = 3467083) B3467083
theorem B3082697 : Blo 1368503 3082697 := bstep (se 2 (by rfl) ⟨1156011, by rfl⟩ : syracuseStep 3082697 = 2312023) B2312023
theorem B3902087 : Blo 1368503 3902087 := bstep (se 1 (by rfl) ⟨2926565, by rfl⟩ : syracuseStep 3902087 = 5853131) B5853131
theorem B3902269 : Blo 1368503 3902269 := bstep (se 3 (by rfl) ⟨731675, by rfl⟩ : syracuseStep 3902269 = 1463351) B1463351
theorem B3902327 : Blo 1368503 3902327 := bstep (se 1 (by rfl) ⟨2926745, by rfl⟩ : syracuseStep 3902327 = 5853491) B5853491
theorem B3468167 : Blo 1368503 3468167 := bstep (se 1 (by rfl) ⟨2601125, by rfl⟩ : syracuseStep 3468167 = 5202251) B5202251
theorem B3468217 : Blo 1368503 3468217 := bstep (se 2 (by rfl) ⟨1300581, by rfl⟩ : syracuseStep 3468217 = 2601163) B2601163
theorem B14797835 : Blo 1368503 14797835 := bstep (se 1 (by rfl) ⟨11098376, by rfl⟩ : syracuseStep 14797835 = 22196753) B22196753
theorem B4623371 : Blo 1368503 4623371 := bstep (se 1 (by rfl) ⟨3467528, by rfl⟩ : syracuseStep 4623371 = 6935057) B6935057
theorem B8768573 : Blo 1368503 8768573 := bstep (se 3 (by rfl) ⟨1644107, by rfl⟩ : syracuseStep 8768573 = 3288215) B3288215
theorem B10546237 : Blo 1368503 10546237 := bstep (se 3 (by rfl) ⟨1977419, by rfl⟩ : syracuseStep 10546237 = 3954839) B3954839
theorem B5196919 : Blo 1368503 5196919 := bstep (se 1 (by rfl) ⟨3897689, by rfl⟩ : syracuseStep 5196919 = 7795379) B7795379
theorem B4623479 : Blo 1368503 4623479 := bstep (se 1 (by rfl) ⟨3467609, by rfl⟩ : syracuseStep 4623479 = 6935219) B6935219
theorem B3083399 : Blo 1368503 3083399 := bstep (se 1 (by rfl) ⟨2312549, by rfl⟩ : syracuseStep 3083399 = 4625099) B4625099
theorem B6933761 : Blo 1368503 6933761 := bstep (se 2 (by rfl) ⟨2600160, by rfl⟩ : syracuseStep 6933761 = 5200321) B5200321
theorem B3083579 : Blo 1368503 3083579 := bstep (se 1 (by rfl) ⟨2312684, by rfl⟩ : syracuseStep 3083579 = 4625369) B4625369
theorem B39497219 : Blo 1368503 39497219 := bstep (se 1 (by rfl) ⟨29622914, by rfl⟩ : syracuseStep 39497219 = 59245829) B59245829
theorem B15609347 : Blo 1368503 15609347 := bstep (se 1 (by rfl) ⟨11707010, by rfl⟩ : syracuseStep 15609347 = 23414021) B23414021
theorem B3468815 : Blo 1368503 3468815 := bstep (se 1 (by rfl) ⟨2601611, by rfl⟩ : syracuseStep 3468815 = 5203223) B5203223
theorem B8326775 : Blo 1368503 8326775 := bstep (se 1 (by rfl) ⟨6245081, by rfl⟩ : syracuseStep 8326775 = 12490163) B12490163
theorem B7794377 : Blo 1368503 7794377 := bstep (se 2 (by rfl) ⟨2922891, by rfl⟩ : syracuseStep 7794377 = 5845783) B5845783
theorem B4624073 : Blo 1368503 4624073 := bstep (se 2 (by rfl) ⟨1734027, by rfl⟩ : syracuseStep 4624073 = 3468055) B3468055
theorem B1732367 : Blo 1368503 1732367 := bstep (se 1 (by rfl) ⟨1299275, by rfl⟩ : syracuseStep 1732367 = 2598551) B2598551
theorem B7401253 : Blo 1368503 7401253 := bstep (se 4 (by rfl) ⟨693867, by rfl⟩ : syracuseStep 7401253 = 1387735) B1387735
theorem B3125051 : Blo 1368503 3125051 := bstep (se 1 (by rfl) ⟨2343788, by rfl⟩ : syracuseStep 3125051 = 4687577) B4687577
theorem B23392151 : Blo 1368503 23392151 := bstep (se 1 (by rfl) ⟨17544113, by rfl⟩ : syracuseStep 23392151 = 35088227) B35088227
theorem B42168215 : Blo 1368503 42168215 := bstep (se 1 (by rfl) ⟨31626161, by rfl⟩ : syracuseStep 42168215 = 63252323) B63252323
theorem B2600905 : Blo 1368503 2600905 := bstep (se 2 (by rfl) ⟨975339, by rfl⟩ : syracuseStep 2600905 = 1950679) B1950679
theorem B6934571 : Blo 1368503 6934571 := bstep (se 1 (by rfl) ⟨5200928, by rfl⟩ : syracuseStep 6934571 = 10401857) B10401857
theorem B5197891 : Blo 1368503 5197891 := bstep (se 1 (by rfl) ⟨3898418, by rfl⟩ : syracuseStep 5197891 = 7796837) B7796837
theorem B5198195 : Blo 1368503 5198195 := bstep (se 1 (by rfl) ⟨3898646, by rfl⟩ : syracuseStep 5198195 = 7797293) B7797293
theorem B1388935 : Blo 1368503 1388935 := bstep (se 1 (by rfl) ⟨1041701, by rfl⟩ : syracuseStep 1388935 = 2083403) B2083403
theorem B4624775 : Blo 1368503 4624775 := bstep (se 1 (by rfl) ⟨3468581, by rfl⟩ : syracuseStep 4624775 = 6937163) B6937163
theorem B11113037 : Blo 1368503 11113037 := bstep (se 3 (by rfl) ⟨2083694, by rfl⟩ : syracuseStep 11113037 = 4167389) B4167389
theorem B5853815 : Blo 1368503 5853815 := bstep (se 1 (by rfl) ⟨4390361, by rfl⟩ : syracuseStep 5853815 = 8780723) B8780723
theorem B2052779 : Blo 1368503 2052779 := bstep (se 1 (by rfl) ⟨1539584, by rfl⟩ : syracuseStep 2052779 = 3079169) B3079169
theorem B2052809 : Blo 1368503 2052809 := bstep (se 2 (by rfl) ⟨769803, by rfl⟩ : syracuseStep 2052809 = 1539607) B1539607
theorem B4625153 : Blo 1368503 4625153 := bstep (se 2 (by rfl) ⟨1734432, by rfl⟩ : syracuseStep 4625153 = 3468865) B3468865
theorem B4936463 : Blo 1368503 4936463 := bstep (se 1 (by rfl) ⟨3702347, by rfl⟩ : syracuseStep 4936463 = 7404695) B7404695
theorem B2052923 : Blo 1368503 2052923 := bstep (se 1 (by rfl) ⟨1539692, by rfl⟩ : syracuseStep 2052923 = 3079385) B3079385
theorem B5198651 : Blo 1368503 5198651 := bstep (se 1 (by rfl) ⟨3898988, by rfl⟩ : syracuseStep 5198651 = 7797977) B7797977
theorem B2052983 : Blo 1368503 2052983 := bstep (se 1 (by rfl) ⟨1539737, by rfl⟩ : syracuseStep 2052983 = 3079475) B3079475
theorem B3167095 : Blo 1368503 3167095 := bstep (se 1 (by rfl) ⟨2375321, by rfl⟩ : syracuseStep 3167095 = 4750643) B4750643
theorem B2053007 : Blo 1368503 2053007 := bstep (se 1 (by rfl) ⟨1539755, by rfl⟩ : syracuseStep 2053007 = 3079511) B3079511
theorem B2053049 : Blo 1368503 2053049 := bstep (se 2 (by rfl) ⟨769893, by rfl⟩ : syracuseStep 2053049 = 1539787) B1539787
theorem B47420387 : Blo 1368503 47420387 := bstep (se 1 (by rfl) ⟨35565290, by rfl⟩ : syracuseStep 47420387 = 71130581) B71130581
theorem B2053127 : Blo 1368503 2053127 := bstep (se 1 (by rfl) ⟨1539845, by rfl⟩ : syracuseStep 2053127 = 3079691) B3079691
theorem B2053163 : Blo 1368503 2053163 := bstep (se 1 (by rfl) ⟨1539872, by rfl⟩ : syracuseStep 2053163 = 3079745) B3079745
theorem B2053193 : Blo 1368503 2053193 := bstep (se 2 (by rfl) ⟨769947, by rfl⟩ : syracuseStep 2053193 = 1539895) B1539895
theorem B9876613 : Blo 1368503 9876613 := bstep (se 4 (by rfl) ⟨925932, by rfl⟩ : syracuseStep 9876613 = 1851865) B1851865
theorem B3699847 : Blo 1368503 3699847 := bstep (se 1 (by rfl) ⟨2774885, by rfl⟩ : syracuseStep 3699847 = 5549771) B5549771
theorem B2053307 : Blo 1368503 2053307 := bstep (se 1 (by rfl) ⟨1539980, by rfl⟩ : syracuseStep 2053307 = 3079961) B3079961
theorem B2053367 : Blo 1368503 2053367 := bstep (se 1 (by rfl) ⟨1540025, by rfl⟩ : syracuseStep 2053367 = 3080051) B3080051
theorem B2053391 : Blo 1368503 2053391 := bstep (se 1 (by rfl) ⟨1540043, by rfl⟩ : syracuseStep 2053391 = 3080087) B3080087
theorem B5199137 : Blo 1368503 5199137 := bstep (se 2 (by rfl) ⟨1949676, by rfl⟩ : syracuseStep 5199137 = 3899353) B3899353
theorem B2053433 : Blo 1368503 2053433 := bstep (se 2 (by rfl) ⟨770037, by rfl⟩ : syracuseStep 2053433 = 1540075) B1540075
theorem B6935867 : Blo 1368503 6935867 := bstep (se 1 (by rfl) ⟨5201900, by rfl⟩ : syracuseStep 6935867 = 10403801) B10403801
theorem B2053511 : Blo 1368503 2053511 := bstep (se 1 (by rfl) ⟨1540133, by rfl⟩ : syracuseStep 2053511 = 3080267) B3080267
theorem B2053547 : Blo 1368503 2053547 := bstep (se 1 (by rfl) ⟨1540160, by rfl⟩ : syracuseStep 2053547 = 3080321) B3080321
theorem B2053577 : Blo 1368503 2053577 := bstep (se 2 (by rfl) ⟨770091, by rfl⟩ : syracuseStep 2053577 = 1540183) B1540183
theorem B7402961 : Blo 1368503 7402961 := bstep (se 2 (by rfl) ⟨2776110, by rfl⟩ : syracuseStep 7402961 = 5552221) B5552221
theorem B6936029 : Blo 1368503 6936029 := bstep (se 3 (by rfl) ⟨1300505, by rfl⟩ : syracuseStep 6936029 = 2601011) B2601011
theorem B2053691 : Blo 1368503 2053691 := bstep (se 1 (by rfl) ⟨1540268, by rfl⟩ : syracuseStep 2053691 = 3080537) B3080537
theorem B4388413 : Blo 1368503 4388413 := bstep (se 3 (by rfl) ⟨822827, by rfl⟩ : syracuseStep 4388413 = 1645655) B1645655
theorem B11859533 : Blo 1368503 11859533 := bstep (se 3 (by rfl) ⟨2223662, by rfl⟩ : syracuseStep 11859533 = 4447325) B4447325
theorem B13162085 : Blo 1368503 13162085 := bstep (se 4 (by rfl) ⟨1233945, by rfl⟩ : syracuseStep 13162085 = 2467891) B2467891
theorem B2053751 : Blo 1368503 2053751 := bstep (se 1 (by rfl) ⟨1540313, by rfl⟩ : syracuseStep 2053751 = 3080627) B3080627
theorem B2053775 : Blo 1368503 2053775 := bstep (se 1 (by rfl) ⟨1540331, by rfl⟩ : syracuseStep 2053775 = 3080663) B3080663
theorem B2053817 : Blo 1368503 2053817 := bstep (se 2 (by rfl) ⟨770181, by rfl⟩ : syracuseStep 2053817 = 1540363) B1540363
theorem B7403201 : Blo 1368503 7403201 := bstep (se 2 (by rfl) ⟨2776200, by rfl⟩ : syracuseStep 7403201 = 5552401) B5552401
theorem B2053895 : Blo 1368503 2053895 := bstep (se 1 (by rfl) ⟨1540421, by rfl⟩ : syracuseStep 2053895 = 3080843) B3080843
theorem B2004751 : Blo 1368503 2004751 := bstep (se 1 (by rfl) ⟨1503563, by rfl⟩ : syracuseStep 2004751 = 3007127) B3007127
theorem B6936353 : Blo 1368503 6936353 := bstep (se 2 (by rfl) ⟨2601132, by rfl⟩ : syracuseStep 6936353 = 5202265) B5202265
theorem B2053931 : Blo 1368503 2053931 := bstep (se 1 (by rfl) ⟨1540448, by rfl⟩ : syracuseStep 2053931 = 3080897) B3080897
theorem B5846843 : Blo 1368503 5846843 := bstep (se 1 (by rfl) ⟨4385132, by rfl⟩ : syracuseStep 5846843 = 8770265) B8770265
theorem B2053961 : Blo 1368503 2053961 := bstep (se 2 (by rfl) ⟨770235, by rfl⟩ : syracuseStep 2053961 = 1540471) B1540471
theorem B2054075 : Blo 1368503 2054075 := bstep (se 1 (by rfl) ⟨1540556, by rfl⟩ : syracuseStep 2054075 = 3081113) B3081113
theorem B6584273 : Blo 1368503 6584273 := bstep (se 2 (by rfl) ⟨2469102, by rfl⟩ : syracuseStep 6584273 = 4938205) B4938205
theorem B2054135 : Blo 1368503 2054135 := bstep (se 1 (by rfl) ⟨1540601, by rfl⟩ : syracuseStep 2054135 = 3081203) B3081203
theorem B2054159 : Blo 1368503 2054159 := bstep (se 1 (by rfl) ⟨1540619, by rfl⟩ : syracuseStep 2054159 = 3081239) B3081239
theorem B2775073 : Blo 1368503 2775073 := bstep (se 2 (by rfl) ⟨1040652, by rfl⟩ : syracuseStep 2775073 = 2081305) B2081305
theorem B2054201 : Blo 1368503 2054201 := bstep (se 2 (by rfl) ⟨770325, by rfl⟩ : syracuseStep 2054201 = 1540651) B1540651
theorem B2193527 : Blo 1368503 2193527 := bstep (se 1 (by rfl) ⟨1645145, by rfl⟩ : syracuseStep 2193527 = 3290291) B3290291
theorem B2054279 : Blo 1368503 2054279 := bstep (se 1 (by rfl) ⟨1540709, by rfl⟩ : syracuseStep 2054279 = 3081419) B3081419
theorem B3897497 : Blo 1368503 3897497 := bstep (se 2 (by rfl) ⟨1461561, by rfl⟩ : syracuseStep 3897497 = 2923123) B2923123
theorem B2054315 : Blo 1368503 2054315 := bstep (se 1 (by rfl) ⟨1540736, by rfl⟩ : syracuseStep 2054315 = 3081473) B3081473
theorem B6928577 : Blo 1368503 6928577 := bstep (se 2 (by rfl) ⟨2598216, by rfl⟩ : syracuseStep 6928577 = 5196433) B5196433
theorem B2054345 : Blo 1368503 2054345 := bstep (se 2 (by rfl) ⟨770379, by rfl⟩ : syracuseStep 2054345 = 1540759) B1540759
theorem B5200109 : Blo 1368503 5200109 := bstep (se 3 (by rfl) ⟨975020, by rfl⟩ : syracuseStep 5200109 = 1950041) B1950041
theorem B2054459 : Blo 1368503 2054459 := bstep (se 1 (by rfl) ⟨1540844, by rfl⟩ : syracuseStep 2054459 = 3081689) B3081689
theorem B13343069 : Blo 1368503 13343069 := bstep (se 3 (by rfl) ⟨2501825, by rfl⟩ : syracuseStep 13343069 = 5003651) B5003651
theorem B2054519 : Blo 1368503 2054519 := bstep (se 1 (by rfl) ⟨1540889, by rfl⟩ : syracuseStep 2054519 = 3081779) B3081779
theorem B2054543 : Blo 1368503 2054543 := bstep (se 1 (by rfl) ⟨1540907, by rfl⟩ : syracuseStep 2054543 = 3081815) B3081815
theorem B2054585 : Blo 1368503 2054585 := bstep (se 2 (by rfl) ⟨770469, by rfl⟩ : syracuseStep 2054585 = 1540939) B1540939
theorem B2054663 : Blo 1368503 2054663 := bstep (se 1 (by rfl) ⟨1540997, by rfl⟩ : syracuseStep 2054663 = 3081995) B3081995
theorem B4618781 : Blo 1368503 4618781 := bstep (se 3 (by rfl) ⟨866021, by rfl⟩ : syracuseStep 4618781 = 1732043) B1732043
theorem B2054699 : Blo 1368503 2054699 := bstep (se 1 (by rfl) ⟨1541024, by rfl⟩ : syracuseStep 2054699 = 3082049) B3082049
theorem B2054729 : Blo 1368503 2054729 := bstep (se 2 (by rfl) ⟨770523, by rfl⟩ : syracuseStep 2054729 = 1541047) B1541047
theorem B33340085 : Blo 1368503 33340085 := bstep (se 5 (by rfl) ⟨1562816, by rfl⟩ : syracuseStep 33340085 = 3125633) B3125633
theorem B2054843 : Blo 1368503 2054843 := bstep (se 1 (by rfl) ⟨1541132, by rfl⟩ : syracuseStep 2054843 = 3082265) B3082265
theorem B15596225 : Blo 1368503 15596225 := bstep (se 2 (by rfl) ⟨5848584, by rfl⟩ : syracuseStep 15596225 = 11697169) B11697169
theorem B6937325 : Blo 1368503 6937325 := bstep (se 3 (by rfl) ⟨1300748, by rfl⟩ : syracuseStep 6937325 = 2601497) B2601497
theorem B2054903 : Blo 1368503 2054903 := bstep (se 1 (by rfl) ⟨1541177, by rfl⟩ : syracuseStep 2054903 = 3082355) B3082355
theorem B1645319 : Blo 1368503 1645319 := bstep (se 1 (by rfl) ⟨1233989, by rfl⟩ : syracuseStep 1645319 = 2467979) B2467979
theorem B2054927 : Blo 1368503 2054927 := bstep (se 1 (by rfl) ⟨1541195, by rfl⟩ : syracuseStep 2054927 = 3082391) B3082391
theorem B3898145 : Blo 1368503 3898145 := bstep (se 2 (by rfl) ⟨1461804, by rfl⟩ : syracuseStep 3898145 = 2923609) B2923609
theorem B18266917 : Blo 1368503 18266917 := bstep (se 4 (by rfl) ⟨1712523, by rfl⟩ : syracuseStep 18266917 = 3425047) B3425047
theorem B2194219 : Blo 1368503 2194219 := bstep (se 1 (by rfl) ⟨1645664, by rfl⟩ : syracuseStep 2194219 = 3291329) B3291329
theorem B2054969 : Blo 1368503 2054969 := bstep (se 2 (by rfl) ⟨770613, by rfl⟩ : syracuseStep 2054969 = 1541227) B1541227
theorem B2055047 : Blo 1368503 2055047 := bstep (se 1 (by rfl) ⟨1541285, by rfl⟩ : syracuseStep 2055047 = 3082571) B3082571
theorem B5200793 : Blo 1368503 5200793 := bstep (se 2 (by rfl) ⟨1950297, by rfl⟩ : syracuseStep 5200793 = 3900595) B3900595
theorem B2055083 : Blo 1368503 2055083 := bstep (se 1 (by rfl) ⟨1541312, by rfl⟩ : syracuseStep 2055083 = 3082625) B3082625
theorem B2194361 : Blo 1368503 2194361 := bstep (se 2 (by rfl) ⟨822885, by rfl⟩ : syracuseStep 2194361 = 1645771) B1645771
theorem B2923465 : Blo 1368503 2923465 := bstep (se 2 (by rfl) ⟨1096299, by rfl⟩ : syracuseStep 2923465 = 2192599) B2192599
theorem B3750857 : Blo 1368503 3750857 := bstep (se 2 (by rfl) ⟨1406571, by rfl⟩ : syracuseStep 3750857 = 2813143) B2813143
theorem B2055113 : Blo 1368503 2055113 := bstep (se 2 (by rfl) ⟨770667, by rfl⟩ : syracuseStep 2055113 = 1541335) B1541335
theorem B2055227 : Blo 1368503 2055227 := bstep (se 1 (by rfl) ⟨1541420, by rfl⟩ : syracuseStep 2055227 = 3082841) B3082841
theorem B3464279 : Blo 1368503 3464279 := bstep (se 1 (by rfl) ⟨2598209, by rfl⟩ : syracuseStep 3464279 = 5196419) B5196419
theorem B2055287 : Blo 1368503 2055287 := bstep (se 1 (by rfl) ⟨1541465, by rfl⟩ : syracuseStep 2055287 = 3082931) B3082931
theorem B2055311 : Blo 1368503 2055311 := bstep (se 1 (by rfl) ⟨1541483, by rfl⟩ : syracuseStep 2055311 = 3082967) B3082967
theorem B4005011 : Blo 1368503 4005011 := bstep (se 1 (by rfl) ⟨3003758, by rfl⟩ : syracuseStep 4005011 = 6007517) B6007517
theorem B2055353 : Blo 1368503 2055353 := bstep (se 2 (by rfl) ⟨770757, by rfl⟩ : syracuseStep 2055353 = 1541515) B1541515
theorem B2776265 : Blo 1368503 2776265 := bstep (se 2 (by rfl) ⟨1041099, by rfl⟩ : syracuseStep 2776265 = 2082199) B2082199
theorem B15604973 : Blo 1368503 15604973 := bstep (se 3 (by rfl) ⟨2925932, by rfl⟩ : syracuseStep 15604973 = 5851865) B5851865
theorem B2055431 : Blo 1368503 2055431 := bstep (se 1 (by rfl) ⟨1541573, by rfl⟩ : syracuseStep 2055431 = 3083147) B3083147
theorem B3079439 : Blo 1368503 3079439 := bstep (se 1 (by rfl) ⟨2309579, by rfl⟩ : syracuseStep 3079439 = 4619159) B4619159
theorem B3079457 : Blo 1368503 3079457 := bstep (se 2 (by rfl) ⟨1154796, by rfl⟩ : syracuseStep 3079457 = 2309593) B2309593
theorem B3464491 : Blo 1368503 3464491 := bstep (se 1 (by rfl) ⟨2598368, by rfl⟩ : syracuseStep 3464491 = 5196737) B5196737
theorem B2055467 : Blo 1368503 2055467 := bstep (se 1 (by rfl) ⟨1541600, by rfl⟩ : syracuseStep 2055467 = 3083201) B3083201
theorem B2055497 : Blo 1368503 2055497 := bstep (se 2 (by rfl) ⟨770811, by rfl⟩ : syracuseStep 2055497 = 1541623) B1541623
theorem B3464633 : Blo 1368503 3464633 := bstep (se 2 (by rfl) ⟨1299237, by rfl⟩ : syracuseStep 3464633 = 2598475) B2598475
theorem B1949113 : Blo 1368503 1949113 := bstep (se 2 (by rfl) ⟨730917, by rfl⟩ : syracuseStep 1949113 = 1461835) B1461835
theorem B2055611 : Blo 1368503 2055611 := bstep (se 1 (by rfl) ⟨1541708, by rfl⟩ : syracuseStep 2055611 = 3083417) B3083417
theorem B6929873 : Blo 1368503 6929873 := bstep (se 2 (by rfl) ⟨2598702, by rfl⟩ : syracuseStep 6929873 = 5197405) B5197405
theorem B16661969 : Blo 1368503 16661969 := bstep (se 2 (by rfl) ⟨6248238, by rfl⟩ : syracuseStep 16661969 = 12496477) B12496477
theorem B2055671 : Blo 1368503 2055671 := bstep (se 1 (by rfl) ⟨1541753, by rfl⟩ : syracuseStep 2055671 = 3083507) B3083507
theorem B2309647 : Blo 1368503 2309647 := bstep (se 1 (by rfl) ⟨1732235, by rfl⟩ : syracuseStep 2309647 = 3464471) B3464471
theorem B2055695 : Blo 1368503 2055695 := bstep (se 1 (by rfl) ⟨1541771, by rfl⟩ : syracuseStep 2055695 = 3083543) B3083543
theorem B7798295 : Blo 1368503 7798295 := bstep (se 1 (by rfl) ⟨5848721, by rfl⟩ : syracuseStep 7798295 = 11697443) B11697443
theorem B6938135 : Blo 1368503 6938135 := bstep (se 1 (by rfl) ⟨5203601, by rfl⟩ : syracuseStep 6938135 = 10407203) B10407203
theorem B2055737 : Blo 1368503 2055737 := bstep (se 2 (by rfl) ⟨770901, by rfl⟩ : syracuseStep 2055737 = 1541803) B1541803
theorem B1539643 : Blo 1368503 1539643 := bstep (se 1 (by rfl) ⟨1154732, by rfl⟩ : syracuseStep 1539643 = 2309465) B2309465
theorem B112451165 : Blo 1368503 112451165 := bstep (se 3 (by rfl) ⟨21084593, by rfl⟩ : syracuseStep 112451165 = 42169187) B42169187
theorem B23731811 : Blo 1368503 23731811 := bstep (se 1 (by rfl) ⟨17798858, by rfl⟩ : syracuseStep 23731811 = 35597717) B35597717
theorem B3079799 : Blo 1368503 3079799 := bstep (se 1 (by rfl) ⟨2309849, by rfl⟩ : syracuseStep 3079799 = 4619699) B4619699
theorem B3333779 : Blo 1368503 3333779 := bstep (se 1 (by rfl) ⟨2500334, by rfl⟩ : syracuseStep 3333779 = 5000669) B5000669
theorem B3899137 : Blo 1368503 3899137 := bstep (se 2 (by rfl) ⟨1462176, by rfl⟩ : syracuseStep 3899137 = 2924353) B2924353
theorem B6668065 : Blo 1368503 6668065 := bstep (se 2 (by rfl) ⟨2500524, by rfl⟩ : syracuseStep 6668065 = 5001049) B5001049
theorem B3079979 : Blo 1368503 3079979 := bstep (se 1 (by rfl) ⟨2309984, by rfl⟩ : syracuseStep 3079979 = 4619969) B4619969
theorem B5201779 : Blo 1368503 5201779 := bstep (se 1 (by rfl) ⟨3901334, by rfl⟩ : syracuseStep 5201779 = 7802669) B7802669
theorem B4620185 : Blo 1368503 4620185 := bstep (se 2 (by rfl) ⟨1732569, by rfl⟩ : syracuseStep 4620185 = 3465139) B3465139
theorem B3899411 : Blo 1368503 3899411 := bstep (se 1 (by rfl) ⟨2924558, by rfl⟩ : syracuseStep 3899411 = 5849117) B5849117
theorem B3080249 : Blo 1368503 3080249 := bstep (se 2 (by rfl) ⟨1155093, by rfl⟩ : syracuseStep 3080249 = 2310187) B2310187
theorem B6930521 : Blo 1368503 6930521 := bstep (se 2 (by rfl) ⟨2598945, by rfl⟩ : syracuseStep 6930521 = 5197891) B5197891
theorem B15597683 : Blo 1368503 15597683 := bstep (se 1 (by rfl) ⟨11698262, by rfl⟩ : syracuseStep 15597683 = 23396525) B23396525
theorem B1540219 : Blo 1368503 1540219 := bstep (se 1 (by rfl) ⟨1155164, by rfl⟩ : syracuseStep 1540219 = 2310329) B2310329
theorem B3465463 : Blo 1368503 3465463 := bstep (se 1 (by rfl) ⟨2599097, by rfl⟩ : syracuseStep 3465463 = 5198195) B5198195
theorem B5849405 : Blo 1368503 5849405 := bstep (se 3 (by rfl) ⟨1096763, by rfl⟩ : syracuseStep 5849405 = 2193527) B2193527
theorem B3080591 : Blo 1368503 3080591 := bstep (se 1 (by rfl) ⟨2310443, by rfl⟩ : syracuseStep 3080591 = 4620887) B4620887
theorem B1368519 : Blo 1368503 1368519 := bstep (se 1 (by rfl) ⟨1026389, by rfl⟩ : syracuseStep 1368519 = 2052779) B2052779
theorem B1368539 : Blo 1368503 1368539 := bstep (se 1 (by rfl) ⟨1026404, by rfl⟩ : syracuseStep 1368539 = 2052809) B2052809
theorem B2310619 : Blo 1368503 2310619 := bstep (se 1 (by rfl) ⟨1732964, by rfl⟩ : syracuseStep 2310619 = 3465929) B3465929
theorem B3465737 : Blo 1368503 3465737 := bstep (se 2 (by rfl) ⟨1299651, by rfl⟩ : syracuseStep 3465737 = 2599303) B2599303
theorem B1851913 : Blo 1368503 1851913 := bstep (se 2 (by rfl) ⟨694467, by rfl⟩ : syracuseStep 1851913 = 1388935) B1388935
theorem B4620833 : Blo 1368503 4620833 := bstep (se 2 (by rfl) ⟨1732812, by rfl⟩ : syracuseStep 4620833 = 3465625) B3465625
theorem B1368615 : Blo 1368503 1368615 := bstep (se 1 (by rfl) ⟨1026461, by rfl⟩ : syracuseStep 1368615 = 2052923) B2052923
theorem B3465767 : Blo 1368503 3465767 := bstep (se 1 (by rfl) ⟨2599325, by rfl⟩ : syracuseStep 3465767 = 5198651) B5198651
theorem B1368655 : Blo 1368503 1368655 := bstep (se 1 (by rfl) ⟨1026491, by rfl⟩ : syracuseStep 1368655 = 2052983) B2052983
theorem B1540687 : Blo 1368503 1540687 := bstep (se 1 (by rfl) ⟨1155515, by rfl⟩ : syracuseStep 1540687 = 2311031) B2311031
theorem B1368671 : Blo 1368503 1368671 := bstep (se 1 (by rfl) ⟨1026503, by rfl⟩ : syracuseStep 1368671 = 2053007) B2053007
theorem B1368699 : Blo 1368503 1368699 := bstep (se 1 (by rfl) ⟨1026524, by rfl⟩ : syracuseStep 1368699 = 2053049) B2053049
theorem B31613591 : Blo 1368503 31613591 := bstep (se 1 (by rfl) ⟨23710193, by rfl⟩ : syracuseStep 31613591 = 47420387) B47420387
theorem B1368751 : Blo 1368503 1368751 := bstep (se 1 (by rfl) ⟨1026563, by rfl⟩ : syracuseStep 1368751 = 2053127) B2053127
theorem B1368775 : Blo 1368503 1368775 := bstep (se 1 (by rfl) ⟨1026581, by rfl⟩ : syracuseStep 1368775 = 2053163) B2053163
theorem B3080915 : Blo 1368503 3080915 := bstep (se 1 (by rfl) ⟨2310686, by rfl⟩ : syracuseStep 3080915 = 4621373) B4621373
theorem B1368795 : Blo 1368503 1368795 := bstep (se 1 (by rfl) ⟨1026596, by rfl⟩ : syracuseStep 1368795 = 2053193) B2053193
theorem B4621049 : Blo 1368503 4621049 := bstep (se 2 (by rfl) ⟨1732893, by rfl⟩ : syracuseStep 4621049 = 3465787) B3465787
theorem B1368871 : Blo 1368503 1368871 := bstep (se 1 (by rfl) ⟨1026653, by rfl⟩ : syracuseStep 1368871 = 2053307) B2053307
theorem B1368911 : Blo 1368503 1368911 := bstep (se 1 (by rfl) ⟨1026683, by rfl⟩ : syracuseStep 1368911 = 2053367) B2053367
theorem B1368927 : Blo 1368503 1368927 := bstep (se 1 (by rfl) ⟨1026695, by rfl⟩ : syracuseStep 1368927 = 2053391) B2053391
theorem B3466091 : Blo 1368503 3466091 := bstep (se 1 (by rfl) ⟨2599568, by rfl⟩ : syracuseStep 3466091 = 5199137) B5199137
theorem B1950571 : Blo 1368503 1950571 := bstep (se 1 (by rfl) ⟨1462928, by rfl⟩ : syracuseStep 1950571 = 2925857) B2925857
theorem B1368955 : Blo 1368503 1368955 := bstep (se 1 (by rfl) ⟨1026716, by rfl⟩ : syracuseStep 1368955 = 2053433) B2053433
theorem B1369007 : Blo 1368503 1369007 := bstep (se 1 (by rfl) ⟨1026755, by rfl⟩ : syracuseStep 1369007 = 2053511) B2053511
theorem B1369031 : Blo 1368503 1369031 := bstep (se 1 (by rfl) ⟨1026773, by rfl⟩ : syracuseStep 1369031 = 2053547) B2053547
theorem B1369051 : Blo 1368503 1369051 := bstep (se 1 (by rfl) ⟨1026788, by rfl⟩ : syracuseStep 1369051 = 2053577) B2053577
theorem B1541083 : Blo 1368503 1541083 := bstep (se 1 (by rfl) ⟨1155812, by rfl⟩ : syracuseStep 1541083 = 2311625) B2311625
theorem B4621319 : Blo 1368503 4621319 := bstep (se 1 (by rfl) ⟨3465989, by rfl⟩ : syracuseStep 4621319 = 6931979) B6931979
theorem B1369127 : Blo 1368503 1369127 := bstep (se 1 (by rfl) ⟨1026845, by rfl⟩ : syracuseStep 1369127 = 2053691) B2053691
theorem B24355889 : Blo 1368503 24355889 := bstep (se 2 (by rfl) ⟨9133458, by rfl⟩ : syracuseStep 24355889 = 18266917) B18266917
theorem B7906355 : Blo 1368503 7906355 := bstep (se 1 (by rfl) ⟨5929766, by rfl⟩ : syracuseStep 7906355 = 11859533) B11859533
theorem B8774723 : Blo 1368503 8774723 := bstep (se 1 (by rfl) ⟨6581042, by rfl⟩ : syracuseStep 8774723 = 13162085) B13162085
theorem B1369167 : Blo 1368503 1369167 := bstep (se 1 (by rfl) ⟨1026875, by rfl⟩ : syracuseStep 1369167 = 2053751) B2053751
theorem B2311247 : Blo 1368503 2311247 := bstep (se 1 (by rfl) ⟨1733435, by rfl⟩ : syracuseStep 2311247 = 3466871) B3466871
theorem B1950799 : Blo 1368503 1950799 := bstep (se 1 (by rfl) ⟨1463099, by rfl⟩ : syracuseStep 1950799 = 2926199) B2926199
theorem B5203025 : Blo 1368503 5203025 := bstep (se 2 (by rfl) ⟨1951134, by rfl⟩ : syracuseStep 5203025 = 3902269) B3902269
theorem B1369183 : Blo 1368503 1369183 := bstep (se 1 (by rfl) ⟨1026887, by rfl⟩ : syracuseStep 1369183 = 2053775) B2053775
theorem B4621427 : Blo 1368503 4621427 := bstep (se 1 (by rfl) ⟨3466070, by rfl⟩ : syracuseStep 4621427 = 6932141) B6932141
theorem B1369211 : Blo 1368503 1369211 := bstep (se 1 (by rfl) ⟨1026908, by rfl⟩ : syracuseStep 1369211 = 2053817) B2053817
theorem B1369263 : Blo 1368503 1369263 := bstep (se 1 (by rfl) ⟨1026947, by rfl⟩ : syracuseStep 1369263 = 2053895) B2053895
theorem B1369287 : Blo 1368503 1369287 := bstep (se 1 (by rfl) ⟨1026965, by rfl⟩ : syracuseStep 1369287 = 2053931) B2053931
theorem B1369307 : Blo 1368503 1369307 := bstep (se 1 (by rfl) ⟨1026980, by rfl⟩ : syracuseStep 1369307 = 2053961) B2053961
theorem B1369383 : Blo 1368503 1369383 := bstep (se 1 (by rfl) ⟨1027037, by rfl⟩ : syracuseStep 1369383 = 2054075) B2054075
theorem B1369423 : Blo 1368503 1369423 := bstep (se 1 (by rfl) ⟨1027067, by rfl⟩ : syracuseStep 1369423 = 2054135) B2054135
theorem B1369439 : Blo 1368503 1369439 := bstep (se 1 (by rfl) ⟨1027079, by rfl⟩ : syracuseStep 1369439 = 2054159) B2054159
theorem B12666227 : Blo 1368503 12666227 := bstep (se 1 (by rfl) ⟨9499670, by rfl⟩ : syracuseStep 12666227 = 18999341) B18999341
theorem B1369467 : Blo 1368503 1369467 := bstep (se 1 (by rfl) ⟨1027100, by rfl⟩ : syracuseStep 1369467 = 2054201) B2054201
theorem B4621697 : Blo 1368503 4621697 := bstep (se 2 (by rfl) ⟨1733136, by rfl⟩ : syracuseStep 4621697 = 3466273) B3466273
theorem B1369519 : Blo 1368503 1369519 := bstep (se 1 (by rfl) ⟨1027139, by rfl⟩ : syracuseStep 1369519 = 2054279) B2054279
theorem B1541551 : Blo 1368503 1541551 := bstep (se 1 (by rfl) ⟨1156163, by rfl⟩ : syracuseStep 1541551 = 2312327) B2312327
theorem B2598331 : Blo 1368503 2598331 := bstep (se 1 (by rfl) ⟨1948748, by rfl⟩ : syracuseStep 2598331 = 3897497) B3897497
theorem B1369543 : Blo 1368503 1369543 := bstep (se 1 (by rfl) ⟨1027157, by rfl⟩ : syracuseStep 1369543 = 2054315) B2054315
theorem B1369563 : Blo 1368503 1369563 := bstep (se 1 (by rfl) ⟨1027172, by rfl⟩ : syracuseStep 1369563 = 2054345) B2054345
theorem B5555675 : Blo 1368503 5555675 := bstep (se 1 (by rfl) ⟨4166756, by rfl⟩ : syracuseStep 5555675 = 8333513) B8333513
theorem B3466739 : Blo 1368503 3466739 := bstep (se 1 (by rfl) ⟨2600054, by rfl⟩ : syracuseStep 3466739 = 5200109) B5200109
theorem B35563013 : Blo 1368503 35563013 := bstep (se 4 (by rfl) ⟨3334032, by rfl⟩ : syracuseStep 35563013 = 6668065) B6668065
theorem B1369639 : Blo 1368503 1369639 := bstep (se 1 (by rfl) ⟨1027229, by rfl⟩ : syracuseStep 1369639 = 2054459) B2054459
theorem B1369679 : Blo 1368503 1369679 := bstep (se 1 (by rfl) ⟨1027259, by rfl⟩ : syracuseStep 1369679 = 2054519) B2054519
theorem B1369695 : Blo 1368503 1369695 := bstep (se 1 (by rfl) ⟨1027271, by rfl⟩ : syracuseStep 1369695 = 2054543) B2054543
theorem B3081851 : Blo 1368503 3081851 := bstep (se 1 (by rfl) ⟨2311388, by rfl⟩ : syracuseStep 3081851 = 4622777) B4622777
theorem B1369723 : Blo 1368503 1369723 := bstep (se 1 (by rfl) ⟨1027292, by rfl⟩ : syracuseStep 1369723 = 2054585) B2054585
theorem B1369775 : Blo 1368503 1369775 := bstep (se 1 (by rfl) ⟨1027331, by rfl⟩ : syracuseStep 1369775 = 2054663) B2054663
theorem B1369799 : Blo 1368503 1369799 := bstep (se 1 (by rfl) ⟨1027349, by rfl⟩ : syracuseStep 1369799 = 2054699) B2054699
theorem B1369819 : Blo 1368503 1369819 := bstep (se 1 (by rfl) ⟨1027364, by rfl⟩ : syracuseStep 1369819 = 2054729) B2054729
theorem B3081977 : Blo 1368503 3081977 := bstep (se 2 (by rfl) ⟨1155741, by rfl⟩ : syracuseStep 3081977 = 2311483) B2311483
theorem B22226723 : Blo 1368503 22226723 := bstep (se 1 (by rfl) ⟨16670042, by rfl⟩ : syracuseStep 22226723 = 33340085) B33340085
theorem B1369895 : Blo 1368503 1369895 := bstep (se 1 (by rfl) ⟨1027421, by rfl⟩ : syracuseStep 1369895 = 2054843) B2054843
theorem B10397483 : Blo 1368503 10397483 := bstep (se 1 (by rfl) ⟨7798112, by rfl⟩ : syracuseStep 10397483 = 15596225) B15596225
theorem B1369935 : Blo 1368503 1369935 := bstep (se 1 (by rfl) ⟨1027451, by rfl⟩ : syracuseStep 1369935 = 2054903) B2054903
theorem B1369951 : Blo 1368503 1369951 := bstep (se 1 (by rfl) ⟨1027463, by rfl⟩ : syracuseStep 1369951 = 2054927) B2054927
theorem B1369979 : Blo 1368503 1369979 := bstep (se 1 (by rfl) ⟨1027484, by rfl⟩ : syracuseStep 1369979 = 2054969) B2054969
theorem B2598817 : Blo 1368503 2598817 := bstep (se 2 (by rfl) ⟨974556, by rfl⟩ : syracuseStep 2598817 = 1949113) B1949113
theorem B1370031 : Blo 1368503 1370031 := bstep (se 1 (by rfl) ⟨1027523, by rfl⟩ : syracuseStep 1370031 = 2055047) B2055047
theorem B2312111 : Blo 1368503 2312111 := bstep (se 1 (by rfl) ⟨1734083, by rfl⟩ : syracuseStep 2312111 = 3468167) B3468167
theorem B3467195 : Blo 1368503 3467195 := bstep (se 1 (by rfl) ⟨2600396, by rfl⟩ : syracuseStep 3467195 = 5200793) B5200793
theorem B1370055 : Blo 1368503 1370055 := bstep (se 1 (by rfl) ⟨1027541, by rfl⟩ : syracuseStep 1370055 = 2055083) B2055083
theorem B2500571 : Blo 1368503 2500571 := bstep (se 1 (by rfl) ⟨1875428, by rfl⟩ : syracuseStep 2500571 = 3750857) B3750857
theorem B1370075 : Blo 1368503 1370075 := bstep (se 1 (by rfl) ⟨1027556, by rfl⟩ : syracuseStep 1370075 = 2055113) B2055113
theorem B9865223 : Blo 1368503 9865223 := bstep (se 1 (by rfl) ⟨7398917, by rfl⟩ : syracuseStep 9865223 = 14797835) B14797835
theorem B3082247 : Blo 1368503 3082247 := bstep (se 1 (by rfl) ⟨2311685, by rfl⟩ : syracuseStep 3082247 = 4623371) B4623371
theorem B1370151 : Blo 1368503 1370151 := bstep (se 1 (by rfl) ⟨1027613, by rfl⟩ : syracuseStep 1370151 = 2055227) B2055227
theorem B3082319 : Blo 1368503 3082319 := bstep (se 1 (by rfl) ⟨2311739, by rfl⟩ : syracuseStep 3082319 = 4623479) B4623479
theorem B5851217 : Blo 1368503 5851217 := bstep (se 2 (by rfl) ⟨2194206, by rfl⟩ : syracuseStep 5851217 = 4388413) B4388413
theorem B1370191 : Blo 1368503 1370191 := bstep (se 1 (by rfl) ⟨1027643, by rfl⟩ : syracuseStep 1370191 = 2055287) B2055287
theorem B1370207 : Blo 1368503 1370207 := bstep (se 1 (by rfl) ⟨1027655, by rfl⟩ : syracuseStep 1370207 = 2055311) B2055311
theorem B1370235 : Blo 1368503 1370235 := bstep (se 1 (by rfl) ⟨1027676, by rfl⟩ : syracuseStep 1370235 = 2055353) B2055353
theorem B4622507 : Blo 1368503 4622507 := bstep (se 1 (by rfl) ⟨3466880, by rfl⟩ : syracuseStep 4622507 = 6933761) B6933761
theorem B1370287 : Blo 1368503 1370287 := bstep (se 1 (by rfl) ⟨1027715, by rfl⟩ : syracuseStep 1370287 = 2055431) B2055431
theorem B1370311 : Blo 1368503 1370311 := bstep (se 1 (by rfl) ⟨1027733, by rfl⟩ : syracuseStep 1370311 = 2055467) B2055467
theorem B1370331 : Blo 1368503 1370331 := bstep (se 1 (by rfl) ⟨1027748, by rfl⟩ : syracuseStep 1370331 = 2055497) B2055497
theorem B1370407 : Blo 1368503 1370407 := bstep (se 1 (by rfl) ⟨1027805, by rfl⟩ : syracuseStep 1370407 = 2055611) B2055611
theorem B1370447 : Blo 1368503 1370447 := bstep (se 1 (by rfl) ⟨1027835, by rfl⟩ : syracuseStep 1370447 = 2055671) B2055671
theorem B26331479 : Blo 1368503 26331479 := bstep (se 1 (by rfl) ⟨19748609, by rfl⟩ : syracuseStep 26331479 = 39497219) B39497219
theorem B10406231 : Blo 1368503 10406231 := bstep (se 1 (by rfl) ⟨7804673, by rfl⟩ : syracuseStep 10406231 = 15609347) B15609347
theorem B2312543 : Blo 1368503 2312543 := bstep (se 1 (by rfl) ⟨1734407, by rfl⟩ : syracuseStep 2312543 = 3468815) B3468815
theorem B1370463 : Blo 1368503 1370463 := bstep (se 1 (by rfl) ⟨1027847, by rfl⟩ : syracuseStep 1370463 = 2055695) B2055695
theorem B2673001 : Blo 1368503 2673001 := bstep (se 2 (by rfl) ⟨1002375, by rfl⟩ : syracuseStep 2673001 = 2004751) B2004751
theorem B1370491 : Blo 1368503 1370491 := bstep (se 1 (by rfl) ⟨1027868, by rfl⟩ : syracuseStep 1370491 = 2055737) B2055737
theorem B74967443 : Blo 1368503 74967443 := bstep (se 1 (by rfl) ⟨56225582, by rfl⟩ : syracuseStep 74967443 = 112451165) B112451165
theorem B15821207 : Blo 1368503 15821207 := bstep (se 1 (by rfl) ⟨11865905, by rfl⟩ : syracuseStep 15821207 = 23731811) B23731811
theorem B2222519 : Blo 1368503 2222519 := bstep (se 1 (by rfl) ⟨1666889, by rfl⟩ : syracuseStep 2222519 = 3333779) B3333779
theorem B5196251 : Blo 1368503 5196251 := bstep (se 1 (by rfl) ⟨3897188, by rfl⟩ : syracuseStep 5196251 = 7794377) B7794377
theorem B3082715 : Blo 1368503 3082715 := bstep (se 1 (by rfl) ⟨2312036, by rfl⟩ : syracuseStep 3082715 = 4624073) B4624073
theorem B2083367 : Blo 1368503 2083367 := bstep (se 1 (by rfl) ⟨1562525, by rfl⟩ : syracuseStep 2083367 = 3125051) B3125051
theorem B3467873 : Blo 1368503 3467873 := bstep (se 2 (by rfl) ⟨1300452, by rfl⟩ : syracuseStep 3467873 = 2600905) B2600905
theorem B5548733 : Blo 1368503 5548733 := bstep (se 3 (by rfl) ⟨1040387, by rfl⟩ : syracuseStep 5548733 = 2080775) B2080775
theorem B4623047 : Blo 1368503 4623047 := bstep (se 1 (by rfl) ⟨3467285, by rfl⟩ : syracuseStep 4623047 = 6934571) B6934571
theorem B3902201 : Blo 1368503 3902201 := bstep (se 2 (by rfl) ⟨1463325, by rfl⟩ : syracuseStep 3902201 = 2926651) B2926651
theorem B3083183 : Blo 1368503 3083183 := bstep (se 1 (by rfl) ⟨2312387, by rfl⟩ : syracuseStep 3083183 = 4624775) B4624775
theorem B7408691 : Blo 1368503 7408691 := bstep (se 1 (by rfl) ⟨5556518, by rfl⟩ : syracuseStep 7408691 = 11113037) B11113037
theorem B3902543 : Blo 1368503 3902543 := bstep (se 1 (by rfl) ⟨2926907, by rfl⟩ : syracuseStep 3902543 = 5853815) B5853815
theorem B3288235 : Blo 1368503 3288235 := bstep (se 1 (by rfl) ⟨2466176, by rfl⟩ : syracuseStep 3288235 = 4932353) B4932353
theorem B4336811 : Blo 1368503 4336811 := bstep (se 1 (by rfl) ⟨3252608, by rfl⟩ : syracuseStep 4336811 = 6505217) B6505217
theorem B3083435 : Blo 1368503 3083435 := bstep (se 1 (by rfl) ⟨2312576, by rfl⟩ : syracuseStep 3083435 = 4625153) B4625153
theorem B2502031 : Blo 1368503 2502031 := bstep (se 1 (by rfl) ⟨1876523, by rfl⟩ : syracuseStep 2502031 = 3753047) B3753047
theorem B4623911 : Blo 1368503 4623911 := bstep (se 1 (by rfl) ⟨3467933, by rfl⟩ : syracuseStep 4623911 = 6935867) B6935867
theorem B5549627 : Blo 1368503 5549627 := bstep (se 1 (by rfl) ⟨4162220, by rfl⟩ : syracuseStep 5549627 = 8324441) B8324441
theorem B4624019 : Blo 1368503 4624019 := bstep (se 1 (by rfl) ⟨3468014, by rfl⟩ : syracuseStep 4624019 = 6936029) B6936029
theorem B4935467 : Blo 1368503 4935467 := bstep (se 1 (by rfl) ⟨3701600, by rfl⟩ : syracuseStep 4935467 = 7403201) B7403201
theorem B4222793 : Blo 1368503 4222793 := bstep (se 2 (by rfl) ⟨1583547, by rfl⟩ : syracuseStep 4222793 = 3167095) B3167095
theorem B4624235 : Blo 1368503 4624235 := bstep (se 1 (by rfl) ⟨3468176, by rfl⟩ : syracuseStep 4624235 = 6936353) B6936353
theorem B4624289 : Blo 1368503 4624289 := bstep (se 2 (by rfl) ⟨1734108, by rfl⟩ : syracuseStep 4624289 = 3468217) B3468217
theorem B14061649 : Blo 1368503 14061649 := bstep (se 2 (by rfl) ⟨5273118, by rfl⟩ : syracuseStep 14061649 = 10546237) B10546237
theorem B84275315 : Blo 1368503 84275315 := bstep (se 1 (by rfl) ⟨63206486, by rfl⟩ : syracuseStep 84275315 = 126412973) B126412973
theorem B13168817 : Blo 1368503 13168817 := bstep (se 2 (by rfl) ⟨4938306, by rfl⟩ : syracuseStep 13168817 = 9876613) B9876613
theorem B11702501 : Blo 1368503 11702501 := bstep (se 4 (by rfl) ⟨1097109, by rfl⟩ : syracuseStep 11702501 = 2194219) B2194219
theorem B2601209 : Blo 1368503 2601209 := bstep (se 2 (by rfl) ⟨975453, by rfl⟩ : syracuseStep 2601209 = 1950907) B1950907
theorem B2601391 : Blo 1368503 2601391 := bstep (se 1 (by rfl) ⟨1951043, by rfl⟩ : syracuseStep 2601391 = 3902087) B3902087
theorem B4624883 : Blo 1368503 4624883 := bstep (se 1 (by rfl) ⟨3468662, by rfl⟩ : syracuseStep 4624883 = 6937325) B6937325
theorem B57750025 : Blo 1368503 57750025 := bstep (se 2 (by rfl) ⟨21656259, by rfl⟩ : syracuseStep 57750025 = 43312519) B43312519
theorem B2601551 : Blo 1368503 2601551 := bstep (se 1 (by rfl) ⟨1951163, by rfl⟩ : syracuseStep 2601551 = 3902327) B3902327
theorem B3289697 : Blo 1368503 3289697 := bstep (se 2 (by rfl) ⟨1233636, by rfl⟩ : syracuseStep 3289697 = 2467273) B2467273
theorem B1462907 : Blo 1368503 1462907 := bstep (se 1 (by rfl) ⟨1097180, by rfl⟩ : syracuseStep 1462907 = 2194361) B2194361
theorem B4387517 : Blo 1368503 4387517 := bstep (se 3 (by rfl) ⟨822659, by rfl⟩ : syracuseStep 4387517 = 1645319) B1645319
theorem B5845715 : Blo 1368503 5845715 := bstep (se 1 (by rfl) ⟨4384286, by rfl⟩ : syracuseStep 5845715 = 8768573) B8768573
theorem B2052857 : Blo 1368503 2052857 := bstep (se 2 (by rfl) ⟨769821, by rfl⟩ : syracuseStep 2052857 = 1539643) B1539643
theorem B2052959 : Blo 1368503 2052959 := bstep (se 1 (by rfl) ⟨1539719, by rfl⟩ : syracuseStep 2052959 = 3079439) B3079439
theorem B2052971 : Blo 1368503 2052971 := bstep (se 1 (by rfl) ⟨1539728, by rfl⟩ : syracuseStep 2052971 = 3079457) B3079457
theorem B5198849 : Blo 1368503 5198849 := bstep (se 2 (by rfl) ⟨1949568, by rfl⟩ : syracuseStep 5198849 = 3899137) B3899137
theorem B5198863 : Blo 1368503 5198863 := bstep (se 1 (by rfl) ⟨3899147, by rfl⟩ : syracuseStep 5198863 = 7798295) B7798295
theorem B4625423 : Blo 1368503 4625423 := bstep (se 1 (by rfl) ⟨3469067, by rfl⟩ : syracuseStep 4625423 = 6938135) B6938135
theorem B9868337 : Blo 1368503 9868337 := bstep (se 2 (by rfl) ⟨3700626, by rfl⟩ : syracuseStep 9868337 = 7401253) B7401253
theorem B2053199 : Blo 1368503 2053199 := bstep (se 1 (by rfl) ⟨1539899, by rfl⟩ : syracuseStep 2053199 = 3079799) B3079799
theorem B5551183 : Blo 1368503 5551183 := bstep (se 1 (by rfl) ⟨4163387, by rfl⟩ : syracuseStep 5551183 = 8326775) B8326775
theorem B6935705 : Blo 1368503 6935705 := bstep (se 2 (by rfl) ⟨2600889, by rfl⟩ : syracuseStep 6935705 = 5201779) B5201779
theorem B2053319 : Blo 1368503 2053319 := bstep (se 1 (by rfl) ⟨1539989, by rfl⟩ : syracuseStep 2053319 = 3079979) B3079979
theorem B15594767 : Blo 1368503 15594767 := bstep (se 1 (by rfl) ⟨11696075, by rfl⟩ : syracuseStep 15594767 = 23392151) B23392151
theorem B28112143 : Blo 1368503 28112143 := bstep (se 1 (by rfl) ⟨21084107, by rfl⟩ : syracuseStep 28112143 = 42168215) B42168215
theorem B2053481 : Blo 1368503 2053481 := bstep (se 2 (by rfl) ⟨770055, by rfl⟩ : syracuseStep 2053481 = 1540111) B1540111
theorem B3700097 : Blo 1368503 3700097 := bstep (se 2 (by rfl) ⟨1387536, by rfl⟩ : syracuseStep 3700097 = 2775073) B2775073
theorem B2053559 : Blo 1368503 2053559 := bstep (se 1 (by rfl) ⟨1540169, by rfl⟩ : syracuseStep 2053559 = 3080339) B3080339
theorem B2053595 : Blo 1368503 2053595 := bstep (se 1 (by rfl) ⟨1540196, by rfl⟩ : syracuseStep 2053595 = 3080393) B3080393
theorem B15603515 : Blo 1368503 15603515 := bstep (se 1 (by rfl) ⟨11702636, by rfl⟩ : syracuseStep 15603515 = 23405273) B23405273
theorem B3290975 : Blo 1368503 3290975 := bstep (se 1 (by rfl) ⟨2468231, by rfl⟩ : syracuseStep 3290975 = 4936463) B4936463
theorem B2054063 : Blo 1368503 2054063 := bstep (se 1 (by rfl) ⟨1540547, by rfl⟩ : syracuseStep 2054063 = 3081095) B3081095
theorem B2054153 : Blo 1368503 2054153 := bstep (se 2 (by rfl) ⟨770307, by rfl⟩ : syracuseStep 2054153 = 1540615) B1540615
theorem B19732517 : Blo 1368503 19732517 := bstep (se 4 (by rfl) ⟨1849923, by rfl⟩ : syracuseStep 19732517 = 3699847) B3699847
theorem B2054183 : Blo 1368503 2054183 := bstep (se 1 (by rfl) ⟨1540637, by rfl⟩ : syracuseStep 2054183 = 3081275) B3081275
theorem B2775163 : Blo 1368503 2775163 := bstep (se 1 (by rfl) ⟨2081372, by rfl⟩ : syracuseStep 2775163 = 4162745) B4162745
theorem B2054267 : Blo 1368503 2054267 := bstep (se 1 (by rfl) ⟨1540700, by rfl⟩ : syracuseStep 2054267 = 3081401) B3081401
theorem B2054393 : Blo 1368503 2054393 := bstep (se 2 (by rfl) ⟨770397, by rfl⟩ : syracuseStep 2054393 = 1540795) B1540795
theorem B5200139 : Blo 1368503 5200139 := bstep (se 1 (by rfl) ⟨3900104, by rfl⟩ : syracuseStep 5200139 = 7800209) B7800209
theorem B2054495 : Blo 1368503 2054495 := bstep (se 1 (by rfl) ⟨1540871, by rfl⟩ : syracuseStep 2054495 = 3081743) B3081743
theorem B2054507 : Blo 1368503 2054507 := bstep (se 1 (by rfl) ⟨1540880, by rfl⟩ : syracuseStep 2054507 = 3081761) B3081761
theorem B3897895 : Blo 1368503 3897895 := bstep (se 1 (by rfl) ⟨2923421, by rfl⟩ : syracuseStep 3897895 = 5846843) B5846843
theorem B19741229 : Blo 1368503 19741229 := bstep (se 3 (by rfl) ⟨3701480, by rfl⟩ : syracuseStep 19741229 = 7402961) B7402961
theorem B2054735 : Blo 1368503 2054735 := bstep (se 1 (by rfl) ⟨1541051, by rfl⟩ : syracuseStep 2054735 = 3082103) B3082103
theorem B3897953 : Blo 1368503 3897953 := bstep (se 2 (by rfl) ⟨1461732, by rfl⟩ : syracuseStep 3897953 = 2923465) B2923465
theorem B4389515 : Blo 1368503 4389515 := bstep (se 1 (by rfl) ⟨3292136, by rfl⟩ : syracuseStep 4389515 = 6584273) B6584273
theorem B2054855 : Blo 1368503 2054855 := bstep (se 1 (by rfl) ⟨1541141, by rfl⟩ : syracuseStep 2054855 = 3082283) B3082283
theorem B5200595 : Blo 1368503 5200595 := bstep (se 1 (by rfl) ⟨3900446, by rfl⟩ : syracuseStep 5200595 = 7800893) B7800893
theorem B4619051 : Blo 1368503 4619051 := bstep (se 1 (by rfl) ⟨3464288, by rfl⟩ : syracuseStep 4619051 = 6928577) B6928577
theorem B6929225 : Blo 1368503 6929225 := bstep (se 2 (by rfl) ⟨2598459, by rfl⟩ : syracuseStep 6929225 = 5196919) B5196919
theorem B2055017 : Blo 1368503 2055017 := bstep (se 2 (by rfl) ⟨770631, by rfl⟩ : syracuseStep 2055017 = 1541263) B1541263
theorem B8895379 : Blo 1368503 8895379 := bstep (se 1 (by rfl) ⟨6671534, by rfl⟩ : syracuseStep 8895379 = 13343069) B13343069
theorem B2055095 : Blo 1368503 2055095 := bstep (se 1 (by rfl) ⟨1541321, by rfl⟩ : syracuseStep 2055095 = 3082643) B3082643
theorem B2055131 : Blo 1368503 2055131 := bstep (se 1 (by rfl) ⟨1541348, by rfl⟩ : syracuseStep 2055131 = 3082697) B3082697
theorem B3079187 : Blo 1368503 3079187 := bstep (se 1 (by rfl) ⟨2309390, by rfl⟩ : syracuseStep 3079187 = 4618781) B4618781
theorem B4619321 : Blo 1368503 4619321 := bstep (se 2 (by rfl) ⟨1732245, by rfl⟩ : syracuseStep 4619321 = 3464491) B3464491
theorem B2776313 : Blo 1368503 2776313 := bstep (se 2 (by rfl) ⟨1041117, by rfl⟩ : syracuseStep 2776313 = 2082235) B2082235
theorem B3079529 : Blo 1368503 3079529 := bstep (se 2 (by rfl) ⟨1154823, by rfl⟩ : syracuseStep 3079529 = 2309647) B2309647
theorem B4619645 : Blo 1368503 4619645 := bstep (se 3 (by rfl) ⟨866183, by rfl⟩ : syracuseStep 4619645 = 1732367) B1732367
theorem B2309519 : Blo 1368503 2309519 := bstep (se 1 (by rfl) ⟨1732139, by rfl⟩ : syracuseStep 2309519 = 3464279) B3464279
theorem B10395053 : Blo 1368503 10395053 := bstep (se 3 (by rfl) ⟨1949072, by rfl⟩ : syracuseStep 10395053 = 3898145) B3898145
theorem B2055599 : Blo 1368503 2055599 := bstep (se 1 (by rfl) ⟨1541699, by rfl⟩ : syracuseStep 2055599 = 3083399) B3083399
theorem B2670007 : Blo 1368503 2670007 := bstep (se 1 (by rfl) ⟨2002505, by rfl⟩ : syracuseStep 2670007 = 4005011) B4005011
theorem B1850843 : Blo 1368503 1850843 := bstep (se 1 (by rfl) ⟨1388132, by rfl⟩ : syracuseStep 1850843 = 2776265) B2776265
theorem B10403315 : Blo 1368503 10403315 := bstep (se 1 (by rfl) ⟨7802486, by rfl⟩ : syracuseStep 10403315 = 15604973) B15604973
theorem B2055689 : Blo 1368503 2055689 := bstep (se 2 (by rfl) ⟨770883, by rfl⟩ : syracuseStep 2055689 = 1541767) B1541767
theorem B2055719 : Blo 1368503 2055719 := bstep (se 1 (by rfl) ⟨1541789, by rfl⟩ : syracuseStep 2055719 = 3083579) B3083579
theorem B2309755 : Blo 1368503 2309755 := bstep (se 1 (by rfl) ⟨1732316, by rfl⟩ : syracuseStep 2309755 = 3464633) B3464633
theorem B4619915 : Blo 1368503 4619915 := bstep (se 1 (by rfl) ⟨3464936, by rfl⟩ : syracuseStep 4619915 = 6929873) B6929873
theorem B11107979 : Blo 1368503 11107979 := bstep (se 1 (by rfl) ⟨8330984, by rfl⟩ : syracuseStep 11107979 = 16661969) B16661969
theorem B5201597 : Blo 1368503 5201597 := bstep (se 3 (by rfl) ⟨975299, by rfl⟩ : syracuseStep 5201597 = 1950599) B1950599
theorem B3080123 : Blo 1368503 3080123 := bstep (se 1 (by rfl) ⟨2310092, by rfl⟩ : syracuseStep 3080123 = 4620185) B4620185
theorem B4620347 : Blo 1368503 4620347 := bstep (se 1 (by rfl) ⟨3465260, by rfl⟩ : syracuseStep 4620347 = 6930521) B6930521
theorem B3899603 : Blo 1368503 3899603 := bstep (se 1 (by rfl) ⟨2924702, by rfl⟩ : syracuseStep 3899603 = 5849405) B5849405
theorem B4620617 : Blo 1368503 4620617 := bstep (se 2 (by rfl) ⟨1732731, by rfl⟩ : syracuseStep 4620617 = 3465463) B3465463
theorem B2310491 : Blo 1368503 2310491 := bstep (se 1 (by rfl) ⟨1732868, by rfl⟩ : syracuseStep 2310491 = 3465737) B3465737
theorem B3080555 : Blo 1368503 3080555 := bstep (se 1 (by rfl) ⟨2310416, by rfl⟩ : syracuseStep 3080555 = 4620833) B4620833
theorem B2310511 : Blo 1368503 2310511 := bstep (se 1 (by rfl) ⟨1732883, by rfl⟩ : syracuseStep 2310511 = 3465767) B3465767
theorem B29606309 : Blo 1368503 29606309 := bstep (se 4 (by rfl) ⟨2775591, by rfl⟩ : syracuseStep 29606309 = 5551183) B5551183
theorem B2925011 : Blo 1368503 2925011 := bstep (se 1 (by rfl) ⟨2193758, by rfl⟩ : syracuseStep 2925011 = 4387517) B4387517
theorem B3564001 : Blo 1368503 3564001 := bstep (se 2 (by rfl) ⟨1336500, by rfl⟩ : syracuseStep 3564001 = 2673001) B2673001
theorem B1368571 : Blo 1368503 1368571 := bstep (se 1 (by rfl) ⟨1026428, by rfl⟩ : syracuseStep 1368571 = 2052857) B2052857
theorem B3080699 : Blo 1368503 3080699 := bstep (se 1 (by rfl) ⟨2310524, by rfl⟩ : syracuseStep 3080699 = 4621049) B4621049
theorem B1368639 : Blo 1368503 1368639 := bstep (se 1 (by rfl) ⟨1026479, by rfl⟩ : syracuseStep 1368639 = 2052959) B2052959
theorem B1368647 : Blo 1368503 1368647 := bstep (se 1 (by rfl) ⟨1026485, by rfl⟩ : syracuseStep 1368647 = 2052971) B2052971
theorem B2310727 : Blo 1368503 2310727 := bstep (se 1 (by rfl) ⟨1733045, by rfl⟩ : syracuseStep 2310727 = 3466091) B3466091
theorem B3080825 : Blo 1368503 3080825 := bstep (se 2 (by rfl) ⟨1155309, by rfl⟩ : syracuseStep 3080825 = 2310619) B2310619
theorem B3465899 : Blo 1368503 3465899 := bstep (se 1 (by rfl) ⟨2599424, by rfl⟩ : syracuseStep 3465899 = 5198849) B5198849
theorem B3080879 : Blo 1368503 3080879 := bstep (se 1 (by rfl) ⟨2310659, by rfl⟩ : syracuseStep 3080879 = 4621319) B4621319
theorem B16237259 : Blo 1368503 16237259 := bstep (se 1 (by rfl) ⟨12177944, by rfl⟩ : syracuseStep 16237259 = 24355889) B24355889
theorem B6578891 : Blo 1368503 6578891 := bstep (se 1 (by rfl) ⟨4934168, by rfl⟩ : syracuseStep 6578891 = 9868337) B9868337
theorem B5849815 : Blo 1368503 5849815 := bstep (se 1 (by rfl) ⟨4387361, by rfl⟩ : syracuseStep 5849815 = 8774723) B8774723
theorem B1368799 : Blo 1368503 1368799 := bstep (se 1 (by rfl) ⟨1026599, by rfl⟩ : syracuseStep 1368799 = 2053199) B2053199
theorem B1540831 : Blo 1368503 1540831 := bstep (se 1 (by rfl) ⟨1155623, by rfl⟩ : syracuseStep 1540831 = 2311247) B2311247
theorem B3080951 : Blo 1368503 3080951 := bstep (se 1 (by rfl) ⟨2310713, by rfl⟩ : syracuseStep 3080951 = 4621427) B4621427
theorem B1368879 : Blo 1368503 1368879 := bstep (se 1 (by rfl) ⟨1026659, by rfl⟩ : syracuseStep 1368879 = 2053319) B2053319
theorem B10396511 : Blo 1368503 10396511 := bstep (se 1 (by rfl) ⟨7797383, by rfl⟩ : syracuseStep 10396511 = 15594767) B15594767
theorem B1368987 : Blo 1368503 1368987 := bstep (se 1 (by rfl) ⟨1026740, by rfl⟩ : syracuseStep 1368987 = 2053481) B2053481
theorem B2466731 : Blo 1368503 2466731 := bstep (se 1 (by rfl) ⟨1850048, by rfl⟩ : syracuseStep 2466731 = 3700097) B3700097
theorem B3081131 : Blo 1368503 3081131 := bstep (se 1 (by rfl) ⟨2310848, by rfl⟩ : syracuseStep 3081131 = 4621697) B4621697
theorem B1369039 : Blo 1368503 1369039 := bstep (se 1 (by rfl) ⟨1026779, by rfl⟩ : syracuseStep 1369039 = 2053559) B2053559
theorem B33776605 : Blo 1368503 33776605 := bstep (se 3 (by rfl) ⟨6333113, by rfl⟩ : syracuseStep 33776605 = 12666227) B12666227
theorem B1369063 : Blo 1368503 1369063 := bstep (se 1 (by rfl) ⟨1026797, by rfl⟩ : syracuseStep 1369063 = 2053595) B2053595
theorem B2311159 : Blo 1368503 2311159 := bstep (se 1 (by rfl) ⟨1733369, by rfl⟩ : syracuseStep 2311159 = 3466739) B3466739
theorem B23708675 : Blo 1368503 23708675 := bstep (se 1 (by rfl) ⟨17781506, by rfl⟩ : syracuseStep 23708675 = 35563013) B35563013
theorem B6931655 : Blo 1368503 6931655 := bstep (se 1 (by rfl) ⟨5198741, by rfl⟩ : syracuseStep 6931655 = 10397483) B10397483
theorem B1369375 : Blo 1368503 1369375 := bstep (se 1 (by rfl) ⟨1027031, by rfl⟩ : syracuseStep 1369375 = 2054063) B2054063
theorem B1541407 : Blo 1368503 1541407 := bstep (se 1 (by rfl) ⟨1156055, by rfl⟩ : syracuseStep 1541407 = 2312111) B2312111
theorem B2311463 : Blo 1368503 2311463 := bstep (se 1 (by rfl) ⟨1733597, by rfl⟩ : syracuseStep 2311463 = 3467195) B3467195
theorem B1369435 : Blo 1368503 1369435 := bstep (se 1 (by rfl) ⟨1027076, by rfl⟩ : syracuseStep 1369435 = 2054153) B2054153
theorem B6931817 : Blo 1368503 6931817 := bstep (se 2 (by rfl) ⟨2599431, by rfl⟩ : syracuseStep 6931817 = 5198863) B5198863
theorem B1369455 : Blo 1368503 1369455 := bstep (se 1 (by rfl) ⟨1027091, by rfl⟩ : syracuseStep 1369455 = 2054183) B2054183
theorem B3900811 : Blo 1368503 3900811 := bstep (se 1 (by rfl) ⟨2925608, by rfl⟩ : syracuseStep 3900811 = 5851217) B5851217
theorem B1369511 : Blo 1368503 1369511 := bstep (se 1 (by rfl) ⟨1027133, by rfl⟩ : syracuseStep 1369511 = 2054267) B2054267
theorem B3081671 : Blo 1368503 3081671 := bstep (se 1 (by rfl) ⟨2311253, by rfl⟩ : syracuseStep 3081671 = 4622507) B4622507
theorem B1369595 : Blo 1368503 1369595 := bstep (se 1 (by rfl) ⟨1027196, by rfl⟩ : syracuseStep 1369595 = 2054393) B2054393
theorem B3466759 : Blo 1368503 3466759 := bstep (se 1 (by rfl) ⟨2600069, by rfl⟩ : syracuseStep 3466759 = 5200139) B5200139
theorem B4384313 : Blo 1368503 4384313 := bstep (se 2 (by rfl) ⟨1644117, by rfl⟩ : syracuseStep 4384313 = 3288235) B3288235
theorem B1369663 : Blo 1368503 1369663 := bstep (se 1 (by rfl) ⟨1027247, by rfl⟩ : syracuseStep 1369663 = 2054495) B2054495
theorem B1541695 : Blo 1368503 1541695 := bstep (se 1 (by rfl) ⟨1156271, by rfl⟩ : syracuseStep 1541695 = 2312543) B2312543
theorem B1369671 : Blo 1368503 1369671 := bstep (se 1 (by rfl) ⟨1027253, by rfl⟩ : syracuseStep 1369671 = 2054507) B2054507
theorem B3901085 : Blo 1368503 3901085 := bstep (se 3 (by rfl) ⟨731453, by rfl⟩ : syracuseStep 3901085 = 1462907) B1462907
theorem B1369823 : Blo 1368503 1369823 := bstep (se 1 (by rfl) ⟨1027367, by rfl⟩ : syracuseStep 1369823 = 2054735) B2054735
theorem B2598635 : Blo 1368503 2598635 := bstep (se 1 (by rfl) ⟨1948976, by rfl⟩ : syracuseStep 2598635 = 3897953) B3897953
theorem B2311915 : Blo 1368503 2311915 := bstep (se 1 (by rfl) ⟨1733936, by rfl⟩ : syracuseStep 2311915 = 3467873) B3467873
theorem B2926343 : Blo 1368503 2926343 := bstep (se 1 (by rfl) ⟨2194757, by rfl⟩ : syracuseStep 2926343 = 4389515) B4389515
theorem B3082031 : Blo 1368503 3082031 := bstep (se 1 (by rfl) ⟨2311523, by rfl⟩ : syracuseStep 3082031 = 4623047) B4623047
theorem B1369903 : Blo 1368503 1369903 := bstep (se 1 (by rfl) ⟨1027427, by rfl⟩ : syracuseStep 1369903 = 2054855) B2054855
theorem B3467063 : Blo 1368503 3467063 := bstep (se 1 (by rfl) ⟨2600297, by rfl⟩ : syracuseStep 3467063 = 5200595) B5200595
theorem B3336041 : Blo 1368503 3336041 := bstep (se 2 (by rfl) ⟨1251015, by rfl⟩ : syracuseStep 3336041 = 2502031) B2502031
theorem B1370011 : Blo 1368503 1370011 := bstep (se 1 (by rfl) ⟨1027508, by rfl⟩ : syracuseStep 1370011 = 2055017) B2055017
theorem B1370063 : Blo 1368503 1370063 := bstep (se 1 (by rfl) ⟨1027547, by rfl⟩ : syracuseStep 1370063 = 2055095) B2055095
theorem B1370087 : Blo 1368503 1370087 := bstep (se 1 (by rfl) ⟨1027565, by rfl⟩ : syracuseStep 1370087 = 2055131) B2055131
theorem B1370399 : Blo 1368503 1370399 := bstep (se 1 (by rfl) ⟨1027799, by rfl⟩ : syracuseStep 1370399 = 2055599) B2055599
theorem B1370459 : Blo 1368503 1370459 := bstep (se 1 (by rfl) ⟨1027844, by rfl⟩ : syracuseStep 1370459 = 2055689) B2055689
theorem B3082607 : Blo 1368503 3082607 := bstep (se 1 (by rfl) ⟨2311955, by rfl⟩ : syracuseStep 3082607 = 4623911) B4623911
theorem B1370479 : Blo 1368503 1370479 := bstep (se 1 (by rfl) ⟨1027859, by rfl⟩ : syracuseStep 1370479 = 2055719) B2055719
theorem B3082679 : Blo 1368503 3082679 := bstep (se 1 (by rfl) ⟨2312009, by rfl⟩ : syracuseStep 3082679 = 4624019) B4624019
theorem B3467731 : Blo 1368503 3467731 := bstep (se 1 (by rfl) ⟨2600798, by rfl⟩ : syracuseStep 3467731 = 5201597) B5201597
theorem B3082823 : Blo 1368503 3082823 := bstep (se 1 (by rfl) ⟨2312117, by rfl⟩ : syracuseStep 3082823 = 4624235) B4624235
theorem B3082859 : Blo 1368503 3082859 := bstep (se 1 (by rfl) ⟨2312144, by rfl⟩ : syracuseStep 3082859 = 4624289) B4624289
theorem B2599607 : Blo 1368503 2599607 := bstep (se 1 (by rfl) ⟨1949705, by rfl⟩ : syracuseStep 2599607 = 3899411) B3899411
theorem B56183543 : Blo 1368503 56183543 := bstep (se 1 (by rfl) ⟨42137657, by rfl⟩ : syracuseStep 56183543 = 84275315) B84275315
theorem B10398455 : Blo 1368503 10398455 := bstep (se 1 (by rfl) ⟨7798841, by rfl⟩ : syracuseStep 10398455 = 15597683) B15597683
theorem B7801667 : Blo 1368503 7801667 := bstep (se 1 (by rfl) ⟨5851250, by rfl⟩ : syracuseStep 7801667 = 11702501) B11702501
theorem B3083255 : Blo 1368503 3083255 := bstep (se 1 (by rfl) ⟨2312441, by rfl⟩ : syracuseStep 3083255 = 4624883) B4624883
theorem B3468521 : Blo 1368503 3468521 := bstep (se 2 (by rfl) ⟨1300695, by rfl⟩ : syracuseStep 3468521 = 2601391) B2601391
theorem B3083615 : Blo 1368503 3083615 := bstep (se 1 (by rfl) ⟨2312711, by rfl⟩ : syracuseStep 3083615 = 4625423) B4625423
theorem B77000033 : Blo 1368503 77000033 := bstep (se 2 (by rfl) ⟨28875012, by rfl⟩ : syracuseStep 77000033 = 57750025) B57750025
theorem B5270903 : Blo 1368503 5270903 := bstep (se 1 (by rfl) ⟨3953177, by rfl⟩ : syracuseStep 5270903 = 7906355) B7906355
theorem B5197193 : Blo 1368503 5197193 := bstep (se 2 (by rfl) ⟨1948947, by rfl⟩ : syracuseStep 5197193 = 3897895) B3897895
theorem B3468683 : Blo 1368503 3468683 := bstep (se 1 (by rfl) ⟨2601512, by rfl⟩ : syracuseStep 3468683 = 5203025) B5203025
theorem B4623803 : Blo 1368503 4623803 := bstep (se 1 (by rfl) ⟨3467852, by rfl⟩ : syracuseStep 4623803 = 6935705) B6935705
theorem B2600761 : Blo 1368503 2600761 := bstep (se 2 (by rfl) ⟨975285, by rfl⟩ : syracuseStep 2600761 = 1950571) B1950571
theorem B5926717 : Blo 1368503 5926717 := bstep (se 3 (by rfl) ⟨1111259, by rfl⟩ : syracuseStep 5926717 = 2222519) B2222519
theorem B4935581 : Blo 1368503 4935581 := bstep (se 3 (by rfl) ⟨925421, by rfl⟩ : syracuseStep 4935581 = 1850843) B1850843
theorem B14815133 : Blo 1368503 14815133 := bstep (se 3 (by rfl) ⟨2777837, by rfl⟩ : syracuseStep 14815133 = 5555675) B5555675
theorem B1667047 : Blo 1368503 1667047 := bstep (se 1 (by rfl) ⟨1250285, by rfl⟩ : syracuseStep 1667047 = 2500571) B2500571
theorem B2601065 : Blo 1368503 2601065 := bstep (se 2 (by rfl) ⟨975399, by rfl⟩ : syracuseStep 2601065 = 1950799) B1950799
theorem B10547471 : Blo 1368503 10547471 := bstep (se 1 (by rfl) ⟨7910603, by rfl⟩ : syracuseStep 10547471 = 15821207) B15821207
theorem B37482857 : Blo 1368503 37482857 := bstep (se 2 (by rfl) ⟨14056071, by rfl⟩ : syracuseStep 37482857 = 28112143) B28112143
theorem B1388911 : Blo 1368503 1388911 := bstep (se 1 (by rfl) ⟨1041683, by rfl⟩ : syracuseStep 1388911 = 2083367) B2083367
theorem B13160819 : Blo 1368503 13160819 := bstep (se 1 (by rfl) ⟨9870614, by rfl⟩ : syracuseStep 13160819 = 19741229) B19741229
theorem B3699155 : Blo 1368503 3699155 := bstep (se 1 (by rfl) ⟨2774366, by rfl⟩ : syracuseStep 3699155 = 5548733) B5548733
theorem B2601467 : Blo 1368503 2601467 := bstep (se 1 (by rfl) ⟨1951100, by rfl⟩ : syracuseStep 2601467 = 3902201) B3902201
theorem B3560009 : Blo 1368503 3560009 := bstep (se 2 (by rfl) ⟨1335003, by rfl⟩ : syracuseStep 3560009 = 2670007) B2670007
theorem B2052791 : Blo 1368503 2052791 := bstep (se 1 (by rfl) ⟨1539593, by rfl⟩ : syracuseStep 2052791 = 3079187) B3079187
theorem B2601695 : Blo 1368503 2601695 := bstep (se 1 (by rfl) ⟨1951271, by rfl⟩ : syracuseStep 2601695 = 3902543) B3902543
theorem B11260781 : Blo 1368503 11260781 := bstep (se 3 (by rfl) ⟨2111396, by rfl⟩ : syracuseStep 11260781 = 4222793) B4222793
theorem B2053019 : Blo 1368503 2053019 := bstep (se 1 (by rfl) ⟨1539764, by rfl⟩ : syracuseStep 2053019 = 3079529) B3079529
theorem B6935543 : Blo 1368503 6935543 := bstep (se 1 (by rfl) ⟨5201657, by rfl⟩ : syracuseStep 6935543 = 10403315) B10403315
theorem B3699751 : Blo 1368503 3699751 := bstep (se 1 (by rfl) ⟨2774813, by rfl⟩ : syracuseStep 3699751 = 5549627) B5549627
theorem B3290311 : Blo 1368503 3290311 := bstep (se 1 (by rfl) ⟨2467733, by rfl⟩ : syracuseStep 3290311 = 4935467) B4935467
theorem B2053415 : Blo 1368503 2053415 := bstep (se 1 (by rfl) ⟨1540061, by rfl⟩ : syracuseStep 2053415 = 3080123) B3080123
theorem B2053499 : Blo 1368503 2053499 := bstep (se 1 (by rfl) ⟨1540124, by rfl⟩ : syracuseStep 2053499 = 3080249) B3080249
theorem B9876869 : Blo 1368503 9876869 := bstep (se 4 (by rfl) ⟨925956, by rfl⟩ : syracuseStep 9876869 = 1851913) B1851913
theorem B18748865 : Blo 1368503 18748865 := bstep (se 2 (by rfl) ⟨7030824, by rfl⟩ : syracuseStep 18748865 = 14061649) B14061649
theorem B8779211 : Blo 1368503 8779211 := bstep (se 1 (by rfl) ⟨6584408, by rfl⟩ : syracuseStep 8779211 = 13168817) B13168817
theorem B3700217 : Blo 1368503 3700217 := bstep (se 2 (by rfl) ⟨1387581, by rfl⟩ : syracuseStep 3700217 = 2775163) B2775163
theorem B2053625 : Blo 1368503 2053625 := bstep (se 2 (by rfl) ⟨770109, by rfl⟩ : syracuseStep 2053625 = 1540219) B1540219
theorem B1734139 : Blo 1368503 1734139 := bstep (se 1 (by rfl) ⟨1300604, by rfl⟩ : syracuseStep 1734139 = 2601209) B2601209
theorem B2053727 : Blo 1368503 2053727 := bstep (se 1 (by rfl) ⟨1540295, by rfl⟩ : syracuseStep 2053727 = 3080591) B3080591
theorem B1734367 : Blo 1368503 1734367 := bstep (se 1 (by rfl) ⟨1300775, by rfl⟩ : syracuseStep 1734367 = 2601551) B2601551
theorem B2193131 : Blo 1368503 2193131 := bstep (se 1 (by rfl) ⟨1644848, by rfl⟩ : syracuseStep 2193131 = 3289697) B3289697
theorem B21075727 : Blo 1368503 21075727 := bstep (se 1 (by rfl) ⟨15806795, by rfl⟩ : syracuseStep 21075727 = 31613591) B31613591
theorem B3897143 : Blo 1368503 3897143 := bstep (se 1 (by rfl) ⟨2922857, by rfl⟩ : syracuseStep 3897143 = 5845715) B5845715
theorem B2053943 : Blo 1368503 2053943 := bstep (se 1 (by rfl) ⟨1540457, by rfl⟩ : syracuseStep 2053943 = 3080915) B3080915
theorem B7403501 : Blo 1368503 7403501 := bstep (se 3 (by rfl) ⟨1388156, by rfl⟩ : syracuseStep 7403501 = 2776313) B2776313
theorem B2054249 : Blo 1368503 2054249 := bstep (se 2 (by rfl) ⟨770343, by rfl⟩ : syracuseStep 2054249 = 1540687) B1540687
theorem B2054567 : Blo 1368503 2054567 := bstep (se 1 (by rfl) ⟨1540925, by rfl⟩ : syracuseStep 2054567 = 3081851) B3081851
theorem B2054651 : Blo 1368503 2054651 := bstep (se 1 (by rfl) ⟨1540988, by rfl⟩ : syracuseStep 2054651 = 3081977) B3081977
theorem B14817815 : Blo 1368503 14817815 := bstep (se 1 (by rfl) ⟨11113361, by rfl⟩ : syracuseStep 14817815 = 22226723) B22226723
theorem B11860505 : Blo 1368503 11860505 := bstep (se 2 (by rfl) ⟨4447689, by rfl⟩ : syracuseStep 11860505 = 8895379) B8895379
theorem B10402343 : Blo 1368503 10402343 := bstep (se 1 (by rfl) ⟨7801757, by rfl⟩ : syracuseStep 10402343 = 15603515) B15603515
theorem B2193983 : Blo 1368503 2193983 := bstep (se 1 (by rfl) ⟨1645487, by rfl⟩ : syracuseStep 2193983 = 3290975) B3290975
theorem B2054777 : Blo 1368503 2054777 := bstep (se 2 (by rfl) ⟨770541, by rfl⟩ : syracuseStep 2054777 = 1541083) B1541083
theorem B6576815 : Blo 1368503 6576815 := bstep (se 1 (by rfl) ⟨4932611, by rfl⟩ : syracuseStep 6576815 = 9865223) B9865223
theorem B2054831 : Blo 1368503 2054831 := bstep (se 1 (by rfl) ⟨1541123, by rfl⟩ : syracuseStep 2054831 = 3082247) B3082247
theorem B13155011 : Blo 1368503 13155011 := bstep (se 1 (by rfl) ⟨9866258, by rfl⟩ : syracuseStep 13155011 = 19732517) B19732517
theorem B2054879 : Blo 1368503 2054879 := bstep (se 1 (by rfl) ⟨1541159, by rfl⟩ : syracuseStep 2054879 = 3082319) B3082319
theorem B17554319 : Blo 1368503 17554319 := bstep (se 1 (by rfl) ⟨13165739, by rfl⟩ : syracuseStep 17554319 = 26331479) B26331479
theorem B6937487 : Blo 1368503 6937487 := bstep (se 1 (by rfl) ⟨5203115, by rfl⟩ : syracuseStep 6937487 = 10406231) B10406231
theorem B49978295 : Blo 1368503 49978295 := bstep (se 1 (by rfl) ⟨37483721, by rfl⟩ : syracuseStep 49978295 = 74967443) B74967443
theorem B3464167 : Blo 1368503 3464167 := bstep (se 1 (by rfl) ⟨2598125, by rfl⟩ : syracuseStep 3464167 = 5196251) B5196251
theorem B2055143 : Blo 1368503 2055143 := bstep (se 1 (by rfl) ⟨1541357, by rfl⟩ : syracuseStep 2055143 = 3082715) B3082715
theorem B3079367 : Blo 1368503 3079367 := bstep (se 1 (by rfl) ⟨2309525, by rfl⟩ : syracuseStep 3079367 = 4619051) B4619051
theorem B4619483 : Blo 1368503 4619483 := bstep (se 1 (by rfl) ⟨3464612, by rfl⟩ : syracuseStep 4619483 = 6929225) B6929225
theorem B2055401 : Blo 1368503 2055401 := bstep (se 2 (by rfl) ⟨770775, by rfl⟩ : syracuseStep 2055401 = 1541551) B1541551
theorem B3464441 : Blo 1368503 3464441 := bstep (se 2 (by rfl) ⟨1299165, by rfl⟩ : syracuseStep 3464441 = 2598331) B2598331
theorem B2055455 : Blo 1368503 2055455 := bstep (se 1 (by rfl) ⟨1541591, by rfl⟩ : syracuseStep 2055455 = 3083183) B3083183
theorem B4939127 : Blo 1368503 4939127 := bstep (se 1 (by rfl) ⟨3704345, by rfl⟩ : syracuseStep 4939127 = 7408691) B7408691
theorem B3079547 : Blo 1368503 3079547 := bstep (se 1 (by rfl) ⟨2309660, by rfl⟩ : syracuseStep 3079547 = 4619321) B4619321
theorem B2891207 : Blo 1368503 2891207 := bstep (se 1 (by rfl) ⟨2168405, by rfl⟩ : syracuseStep 2891207 = 4336811) B4336811
theorem B2055623 : Blo 1368503 2055623 := bstep (se 1 (by rfl) ⟨1541717, by rfl⟩ : syracuseStep 2055623 = 3083435) B3083435
theorem B3079673 : Blo 1368503 3079673 := bstep (se 2 (by rfl) ⟨1154877, by rfl⟩ : syracuseStep 3079673 = 2309755) B2309755
theorem B3079763 : Blo 1368503 3079763 := bstep (se 1 (by rfl) ⟨2309822, by rfl⟩ : syracuseStep 3079763 = 4619645) B4619645
theorem B1539679 : Blo 1368503 1539679 := bstep (se 1 (by rfl) ⟨1154759, by rfl⟩ : syracuseStep 1539679 = 2309519) B2309519
theorem B6930035 : Blo 1368503 6930035 := bstep (se 1 (by rfl) ⟨5197526, by rfl⟩ : syracuseStep 6930035 = 10395053) B10395053
theorem B3079943 : Blo 1368503 3079943 := bstep (se 1 (by rfl) ⟨2309957, by rfl⟩ : syracuseStep 3079943 = 4619915) B4619915
theorem B7405319 : Blo 1368503 7405319 := bstep (se 1 (by rfl) ⟨5553989, by rfl⟩ : syracuseStep 7405319 = 11107979) B11107979
theorem B3465089 : Blo 1368503 3465089 := bstep (se 2 (by rfl) ⟨1299408, by rfl⟩ : syracuseStep 3465089 = 2598817) B2598817
theorem B3080231 : Blo 1368503 3080231 := bstep (se 1 (by rfl) ⟨2310173, by rfl⟩ : syracuseStep 3080231 = 4620347) B4620347
theorem B3080411 : Blo 1368503 3080411 := bstep (se 1 (by rfl) ⟨2310308, by rfl⟩ : syracuseStep 3080411 = 4620617) B4620617
theorem B1540327 : Blo 1368503 1540327 := bstep (se 1 (by rfl) ⟨1155245, by rfl⟩ : syracuseStep 1540327 = 2310491) B2310491
theorem B8773879 : Blo 1368503 8773879 := bstep (se 1 (by rfl) ⟨6580409, by rfl⟩ : syracuseStep 8773879 = 13160819) B13160819
theorem B1950007 : Blo 1368503 1950007 := bstep (se 1 (by rfl) ⟨1462505, by rfl⟩ : syracuseStep 1950007 = 2925011) B2925011
theorem B2310599 : Blo 1368503 2310599 := bstep (se 1 (by rfl) ⟨1732949, by rfl⟩ : syracuseStep 2310599 = 3465899) B3465899
theorem B1368527 : Blo 1368503 1368527 := bstep (se 1 (by rfl) ⟨1026395, by rfl⟩ : syracuseStep 1368527 = 2052791) B2052791
theorem B3080681 : Blo 1368503 3080681 := bstep (se 2 (by rfl) ⟨1155255, by rfl⟩ : syracuseStep 3080681 = 2310511) B2310511
theorem B1851881 : Blo 1368503 1851881 := bstep (se 2 (by rfl) ⟨694455, by rfl⟩ : syracuseStep 1851881 = 1388911) B1388911
theorem B6931007 : Blo 1368503 6931007 := bstep (se 1 (by rfl) ⟨5198255, by rfl⟩ : syracuseStep 6931007 = 10396511) B10396511
theorem B1368679 : Blo 1368503 1368679 := bstep (se 1 (by rfl) ⟨1026509, by rfl⟩ : syracuseStep 1368679 = 2053019) B2053019
theorem B4752001 : Blo 1368503 4752001 := bstep (se 2 (by rfl) ⟨1782000, by rfl⟩ : syracuseStep 4752001 = 3564001) B3564001
theorem B3080969 : Blo 1368503 3080969 := bstep (se 2 (by rfl) ⟨1155363, by rfl⟩ : syracuseStep 3080969 = 2310727) B2310727
theorem B4621103 : Blo 1368503 4621103 := bstep (se 1 (by rfl) ⟨3465827, by rfl⟩ : syracuseStep 4621103 = 6931655) B6931655
theorem B1368943 : Blo 1368503 1368943 := bstep (se 1 (by rfl) ⟨1026707, by rfl⟩ : syracuseStep 1368943 = 2053415) B2053415
theorem B1540975 : Blo 1368503 1540975 := bstep (se 1 (by rfl) ⟨1155731, by rfl⟩ : syracuseStep 1540975 = 2311463) B2311463
theorem B4621211 : Blo 1368503 4621211 := bstep (se 1 (by rfl) ⟨3465908, by rfl⟩ : syracuseStep 4621211 = 6931817) B6931817
theorem B1368999 : Blo 1368503 1368999 := bstep (se 1 (by rfl) ⟨1026749, by rfl⟩ : syracuseStep 1368999 = 2053499) B2053499
theorem B7799753 : Blo 1368503 7799753 := bstep (se 2 (by rfl) ⟨2924907, by rfl⟩ : syracuseStep 7799753 = 5849815) B5849815
theorem B2466811 : Blo 1368503 2466811 := bstep (se 1 (by rfl) ⟨1850108, by rfl⟩ : syracuseStep 2466811 = 3700217) B3700217
theorem B1369083 : Blo 1368503 1369083 := bstep (se 1 (by rfl) ⟨1026812, by rfl⟩ : syracuseStep 1369083 = 2053625) B2053625
theorem B1369151 : Blo 1368503 1369151 := bstep (se 1 (by rfl) ⟨1026863, by rfl⟩ : syracuseStep 1369151 = 2053727) B2053727
theorem B49996973 : Blo 1368503 49996973 := bstep (se 3 (by rfl) ⟨9374432, by rfl⟩ : syracuseStep 49996973 = 18748865) B18748865
theorem B1950895 : Blo 1368503 1950895 := bstep (se 1 (by rfl) ⟨1463171, by rfl⟩ : syracuseStep 1950895 = 2926343) B2926343
theorem B2598095 : Blo 1368503 2598095 := bstep (se 1 (by rfl) ⟨1948571, by rfl⟩ : syracuseStep 2598095 = 3897143) B3897143
theorem B1369295 : Blo 1368503 1369295 := bstep (se 1 (by rfl) ⟨1026971, by rfl⟩ : syracuseStep 1369295 = 2053943) B2053943
theorem B2311375 : Blo 1368503 2311375 := bstep (se 1 (by rfl) ⟨1733531, by rfl⟩ : syracuseStep 2311375 = 3467063) B3467063
theorem B9864413 : Blo 1368503 9864413 := bstep (se 3 (by rfl) ⟨1849577, by rfl⟩ : syracuseStep 9864413 = 3699155) B3699155
theorem B3081545 : Blo 1368503 3081545 := bstep (se 2 (by rfl) ⟨1155579, by rfl⟩ : syracuseStep 3081545 = 2311159) B2311159
theorem B4933001 : Blo 1368503 4933001 := bstep (se 2 (by rfl) ⟨1849875, by rfl⟩ : syracuseStep 4933001 = 3699751) B3699751
theorem B1369499 : Blo 1368503 1369499 := bstep (se 1 (by rfl) ⟨1027124, by rfl⟩ : syracuseStep 1369499 = 2054249) B2054249
theorem B1369711 : Blo 1368503 1369711 := bstep (se 1 (by rfl) ⟨1027283, by rfl⟩ : syracuseStep 1369711 = 2054567) B2054567
theorem B1369767 : Blo 1368503 1369767 := bstep (se 1 (by rfl) ⟨1027325, by rfl⟩ : syracuseStep 1369767 = 2054651) B2054651
theorem B7907003 : Blo 1368503 7907003 := bstep (se 1 (by rfl) ⟨5930252, by rfl⟩ : syracuseStep 7907003 = 11860505) B11860505
theorem B1369851 : Blo 1368503 1369851 := bstep (se 1 (by rfl) ⟨1027388, by rfl⟩ : syracuseStep 1369851 = 2054777) B2054777
theorem B4384543 : Blo 1368503 4384543 := bstep (se 1 (by rfl) ⟨3288407, by rfl⟩ : syracuseStep 4384543 = 6576815) B6576815
theorem B1369887 : Blo 1368503 1369887 := bstep (se 1 (by rfl) ⟨1027415, by rfl⟩ : syracuseStep 1369887 = 2054831) B2054831
theorem B1369919 : Blo 1368503 1369919 := bstep (se 1 (by rfl) ⟨1027439, by rfl⟩ : syracuseStep 1369919 = 2054879) B2054879
theorem B37455695 : Blo 1368503 37455695 := bstep (se 1 (by rfl) ⟨28091771, by rfl⟩ : syracuseStep 37455695 = 56183543) B56183543
theorem B6932303 : Blo 1368503 6932303 := bstep (se 1 (by rfl) ⟨5199227, by rfl⟩ : syracuseStep 6932303 = 10398455) B10398455
theorem B33318863 : Blo 1368503 33318863 := bstep (se 1 (by rfl) ⟨24989147, by rfl⟩ : syracuseStep 33318863 = 49978295) B49978295
theorem B1370095 : Blo 1368503 1370095 := bstep (se 1 (by rfl) ⟨1027571, by rfl⟩ : syracuseStep 1370095 = 2055143) B2055143
theorem B2312185 : Blo 1368503 2312185 := bstep (se 2 (by rfl) ⟨867069, by rfl⟩ : syracuseStep 2312185 = 1734139) B1734139
theorem B4622345 : Blo 1368503 4622345 := bstep (se 2 (by rfl) ⟨1733379, by rfl⟩ : syracuseStep 4622345 = 3466759) B3466759
theorem B1370267 : Blo 1368503 1370267 := bstep (se 1 (by rfl) ⟨1027700, by rfl⟩ : syracuseStep 1370267 = 2055401) B2055401
theorem B2312347 : Blo 1368503 2312347 := bstep (se 1 (by rfl) ⟨1734260, by rfl⟩ : syracuseStep 2312347 = 3468521) B3468521
theorem B1370303 : Blo 1368503 1370303 := bstep (se 1 (by rfl) ⟨1027727, by rfl⟩ : syracuseStep 1370303 = 2055455) B2055455
theorem B51333355 : Blo 1368503 51333355 := bstep (se 1 (by rfl) ⟨38500016, by rfl⟩ : syracuseStep 51333355 = 77000033) B77000033
theorem B2312455 : Blo 1368503 2312455 := bstep (se 1 (by rfl) ⟨1734341, by rfl⟩ : syracuseStep 2312455 = 3468683) B3468683
theorem B3082535 : Blo 1368503 3082535 := bstep (se 1 (by rfl) ⟨2311901, by rfl⟩ : syracuseStep 3082535 = 4623803) B4623803
theorem B2312489 : Blo 1368503 2312489 := bstep (se 2 (by rfl) ⟨867183, by rfl⟩ : syracuseStep 2312489 = 1734367) B1734367
theorem B1927471 : Blo 1368503 1927471 := bstep (se 1 (by rfl) ⟨1445603, by rfl⟩ : syracuseStep 1927471 = 2891207) B2891207
theorem B1370415 : Blo 1368503 1370415 := bstep (se 1 (by rfl) ⟨1027811, by rfl⟩ : syracuseStep 1370415 = 2055623) B2055623
theorem B3082553 : Blo 1368503 3082553 := bstep (se 2 (by rfl) ⟨1155957, by rfl⟩ : syracuseStep 3082553 = 2311915) B2311915
theorem B28100969 : Blo 1368503 28100969 := bstep (se 2 (by rfl) ⟨10537863, by rfl⟩ : syracuseStep 28100969 = 21075727) B21075727
theorem B3467681 : Blo 1368503 3467681 := bstep (se 2 (by rfl) ⟨1300380, by rfl⟩ : syracuseStep 3467681 = 2600761) B2600761
theorem B2222729 : Blo 1368503 2222729 := bstep (se 2 (by rfl) ⟨833523, by rfl⟩ : syracuseStep 2222729 = 1667047) B1667047
theorem B7031647 : Blo 1368503 7031647 := bstep (se 1 (by rfl) ⟨5273735, by rfl⟩ : syracuseStep 7031647 = 10547471) B10547471
theorem B24988571 : Blo 1368503 24988571 := bstep (se 1 (by rfl) ⟨18741428, by rfl⟩ : syracuseStep 24988571 = 37482857) B37482857
theorem B19737539 : Blo 1368503 19737539 := bstep (se 1 (by rfl) ⟨14803154, by rfl⟩ : syracuseStep 19737539 = 29606309) B29606309
theorem B10824839 : Blo 1368503 10824839 := bstep (se 1 (by rfl) ⟨8118629, by rfl⟩ : syracuseStep 10824839 = 16237259) B16237259
theorem B4385927 : Blo 1368503 4385927 := bstep (se 1 (by rfl) ⟨3289445, by rfl⟩ : syracuseStep 4385927 = 6578891) B6578891
theorem B10398941 : Blo 1368503 10398941 := bstep (se 3 (by rfl) ⟨1949801, by rfl⟩ : syracuseStep 10398941 = 3899603) B3899603
theorem B7507187 : Blo 1368503 7507187 := bstep (se 1 (by rfl) ⟨5630390, by rfl⟩ : syracuseStep 7507187 = 11260781) B11260781
theorem B4623641 : Blo 1368503 4623641 := bstep (se 2 (by rfl) ⟨1733865, by rfl⟩ : syracuseStep 4623641 = 3467731) B3467731
theorem B4623695 : Blo 1368503 4623695 := bstep (se 1 (by rfl) ⟨3467771, by rfl⟩ : syracuseStep 4623695 = 6935543) B6935543
theorem B15805783 : Blo 1368503 15805783 := bstep (se 1 (by rfl) ⟨11854337, by rfl⟩ : syracuseStep 15805783 = 23708675) B23708675
theorem B5852807 : Blo 1368503 5852807 := bstep (se 1 (by rfl) ⟨4389605, by rfl⟩ : syracuseStep 5852807 = 8779211) B8779211
theorem B2600723 : Blo 1368503 2600723 := bstep (se 1 (by rfl) ⟨1950542, by rfl⟩ : syracuseStep 2600723 = 3901085) B3901085
theorem B1732423 : Blo 1368503 1732423 := bstep (se 1 (by rfl) ⟨1299317, by rfl⟩ : syracuseStep 1732423 = 2598635) B2598635
theorem B1462087 : Blo 1368503 1462087 := bstep (se 1 (by rfl) ⟨1096565, by rfl⟩ : syracuseStep 1462087 = 2193131) B2193131
theorem B2224027 : Blo 1368503 2224027 := bstep (se 1 (by rfl) ⟨1668020, by rfl⟩ : syracuseStep 2224027 = 3336041) B3336041
theorem B4935667 : Blo 1368503 4935667 := bstep (se 1 (by rfl) ⟨3701750, by rfl⟩ : syracuseStep 4935667 = 7403501) B7403501
theorem B4387081 : Blo 1368503 4387081 := bstep (se 2 (by rfl) ⟨1645155, by rfl⟩ : syracuseStep 4387081 = 3290311) B3290311
theorem B6934895 : Blo 1368503 6934895 := bstep (se 1 (by rfl) ⟨5201171, by rfl⟩ : syracuseStep 6934895 = 10402343) B10402343
theorem B1462655 : Blo 1368503 1462655 := bstep (se 1 (by rfl) ⟨1096991, by rfl⟩ : syracuseStep 1462655 = 2193983) B2193983
theorem B1733071 : Blo 1368503 1733071 := bstep (se 1 (by rfl) ⟨1299803, by rfl⟩ : syracuseStep 1733071 = 2599607) B2599607
theorem B8770007 : Blo 1368503 8770007 := bstep (se 1 (by rfl) ⟨6577505, by rfl⟩ : syracuseStep 8770007 = 13155011) B13155011
theorem B11702879 : Blo 1368503 11702879 := bstep (se 1 (by rfl) ⟨8777159, by rfl⟩ : syracuseStep 11702879 = 17554319) B17554319
theorem B4624991 : Blo 1368503 4624991 := bstep (se 1 (by rfl) ⟨3468743, by rfl⟩ : syracuseStep 4624991 = 6937487) B6937487
theorem B2052905 : Blo 1368503 2052905 := bstep (se 2 (by rfl) ⟨769839, by rfl⟩ : syracuseStep 2052905 = 1539679) B1539679
theorem B2052911 : Blo 1368503 2052911 := bstep (se 1 (by rfl) ⟨1539683, by rfl⟩ : syracuseStep 2052911 = 3079367) B3079367
theorem B2053031 : Blo 1368503 2053031 := bstep (se 1 (by rfl) ⟨1539773, by rfl⟩ : syracuseStep 2053031 = 3079547) B3079547
theorem B2053115 : Blo 1368503 2053115 := bstep (se 1 (by rfl) ⟨1539836, by rfl⟩ : syracuseStep 2053115 = 3079673) B3079673
theorem B2053175 : Blo 1368503 2053175 := bstep (se 1 (by rfl) ⟨1539881, by rfl⟩ : syracuseStep 2053175 = 3079763) B3079763
theorem B7902289 : Blo 1368503 7902289 := bstep (se 2 (by rfl) ⟨2963358, by rfl⟩ : syracuseStep 7902289 = 5926717) B5926717
theorem B2053295 : Blo 1368503 2053295 := bstep (se 1 (by rfl) ⟨1539971, by rfl⟩ : syracuseStep 2053295 = 3079943) B3079943
theorem B4936879 : Blo 1368503 4936879 := bstep (se 1 (by rfl) ⟨3702659, by rfl⟩ : syracuseStep 4936879 = 7405319) B7405319
theorem B3290387 : Blo 1368503 3290387 := bstep (se 1 (by rfl) ⟨2467790, by rfl⟩ : syracuseStep 3290387 = 4935581) B4935581
theorem B9876755 : Blo 1368503 9876755 := bstep (se 1 (by rfl) ⟨7407566, by rfl⟩ : syracuseStep 9876755 = 14815133) B14815133
theorem B1734043 : Blo 1368503 1734043 := bstep (se 1 (by rfl) ⟨1300532, by rfl⟩ : syracuseStep 1734043 = 2601065) B2601065
theorem B2053703 : Blo 1368503 2053703 := bstep (se 1 (by rfl) ⟨1540277, by rfl⟩ : syracuseStep 2053703 = 3080555) B3080555
theorem B2053799 : Blo 1368503 2053799 := bstep (se 1 (by rfl) ⟨1540349, by rfl⟩ : syracuseStep 2053799 = 3080699) B3080699
theorem B1734311 : Blo 1368503 1734311 := bstep (se 1 (by rfl) ⟨1300733, by rfl⟩ : syracuseStep 1734311 = 2601467) B2601467
theorem B2053883 : Blo 1368503 2053883 := bstep (se 1 (by rfl) ⟨1540412, by rfl⟩ : syracuseStep 2053883 = 3080825) B3080825
theorem B2053919 : Blo 1368503 2053919 := bstep (se 1 (by rfl) ⟨1540439, by rfl⟩ : syracuseStep 2053919 = 3080879) B3080879
theorem B1734463 : Blo 1368503 1734463 := bstep (se 1 (by rfl) ⟨1300847, by rfl⟩ : syracuseStep 1734463 = 2601695) B2601695
theorem B2053967 : Blo 1368503 2053967 := bstep (se 1 (by rfl) ⟨1540475, by rfl⟩ : syracuseStep 2053967 = 3080951) B3080951
theorem B2054087 : Blo 1368503 2054087 := bstep (se 1 (by rfl) ⟨1540565, by rfl⟩ : syracuseStep 2054087 = 3081131) B3081131
theorem B6584579 : Blo 1368503 6584579 := bstep (se 1 (by rfl) ⟨4938434, by rfl⟩ : syracuseStep 6584579 = 9876869) B9876869
theorem B2054441 : Blo 1368503 2054441 := bstep (se 2 (by rfl) ⟨770415, by rfl⟩ : syracuseStep 2054441 = 1540831) B1540831
theorem B2054447 : Blo 1368503 2054447 := bstep (se 1 (by rfl) ⟨1540835, by rfl⟩ : syracuseStep 2054447 = 3081671) B3081671
theorem B2922875 : Blo 1368503 2922875 := bstep (se 1 (by rfl) ⟨2192156, by rfl⟩ : syracuseStep 2922875 = 4384313) B4384313
theorem B2054687 : Blo 1368503 2054687 := bstep (se 1 (by rfl) ⟨1541015, by rfl⟩ : syracuseStep 2054687 = 3082031) B3082031
theorem B4618889 : Blo 1368503 4618889 := bstep (se 2 (by rfl) ⟨1732083, by rfl⟩ : syracuseStep 4618889 = 3464167) B3464167
theorem B9493357 : Blo 1368503 9493357 := bstep (se 3 (by rfl) ⟨1780004, by rfl⟩ : syracuseStep 9493357 = 3560009) B3560009
theorem B2055071 : Blo 1368503 2055071 := bstep (se 1 (by rfl) ⟨1541303, by rfl⟩ : syracuseStep 2055071 = 3082607) B3082607
theorem B2055119 : Blo 1368503 2055119 := bstep (se 1 (by rfl) ⟨1541339, by rfl⟩ : syracuseStep 2055119 = 3082679) B3082679
theorem B9878543 : Blo 1368503 9878543 := bstep (se 1 (by rfl) ⟨7408907, by rfl⟩ : syracuseStep 9878543 = 14817815) B14817815
theorem B2055209 : Blo 1368503 2055209 := bstep (se 2 (by rfl) ⟨770703, by rfl⟩ : syracuseStep 2055209 = 1541407) B1541407
theorem B2055215 : Blo 1368503 2055215 := bstep (se 1 (by rfl) ⟨1541411, by rfl⟩ : syracuseStep 2055215 = 3082823) B3082823
theorem B2055239 : Blo 1368503 2055239 := bstep (se 1 (by rfl) ⟨1541429, by rfl⟩ : syracuseStep 2055239 = 3082859) B3082859
theorem B5201081 : Blo 1368503 5201081 := bstep (se 2 (by rfl) ⟨1950405, by rfl⟩ : syracuseStep 5201081 = 3900811) B3900811
theorem B5201111 : Blo 1368503 5201111 := bstep (se 1 (by rfl) ⟨3900833, by rfl⟩ : syracuseStep 5201111 = 7801667) B7801667
theorem B2055503 : Blo 1368503 2055503 := bstep (se 1 (by rfl) ⟨1541627, by rfl⟩ : syracuseStep 2055503 = 3083255) B3083255
theorem B2055593 : Blo 1368503 2055593 := bstep (se 2 (by rfl) ⟨770847, by rfl⟩ : syracuseStep 2055593 = 1541695) B1541695
theorem B3079655 : Blo 1368503 3079655 := bstep (se 1 (by rfl) ⟨2309741, by rfl⟩ : syracuseStep 3079655 = 4619483) B4619483
theorem B2309627 : Blo 1368503 2309627 := bstep (se 1 (by rfl) ⟨1732220, by rfl⟩ : syracuseStep 2309627 = 3464441) B3464441
theorem B2055743 : Blo 1368503 2055743 := bstep (se 1 (by rfl) ⟨1541807, by rfl⟩ : syracuseStep 2055743 = 3083615) B3083615
theorem B3513935 : Blo 1368503 3513935 := bstep (se 1 (by rfl) ⟨2635451, by rfl⟩ : syracuseStep 3513935 = 5270903) B5270903
theorem B3292751 : Blo 1368503 3292751 := bstep (se 1 (by rfl) ⟨2469563, by rfl⟩ : syracuseStep 3292751 = 4939127) B4939127
theorem B3464795 : Blo 1368503 3464795 := bstep (se 1 (by rfl) ⟨2598596, by rfl⟩ : syracuseStep 3464795 = 5197193) B5197193
theorem B4620023 : Blo 1368503 4620023 := bstep (se 1 (by rfl) ⟨3465017, by rfl⟩ : syracuseStep 4620023 = 6930035) B6930035
theorem B6577949 : Blo 1368503 6577949 := bstep (se 3 (by rfl) ⟨1233365, by rfl⟩ : syracuseStep 6577949 = 2466731) B2466731
theorem B180141893 : Blo 1368503 180141893 := bstep (se 4 (by rfl) ⟨16888302, by rfl⟩ : syracuseStep 180141893 = 33776605) B33776605
theorem B2310059 : Blo 1368503 2310059 := bstep (se 1 (by rfl) ⟨1732544, by rfl⟩ : syracuseStep 2310059 = 3465089) B3465089
theorem B1540399 : Blo 1368503 1540399 := bstep (se 1 (by rfl) ⟨1155299, by rfl⟩ : syracuseStep 1540399 = 2310599) B2310599
theorem B68444473 : Blo 1368503 68444473 := bstep (se 2 (by rfl) ⟨25666677, by rfl⟩ : syracuseStep 68444473 = 51333355) B51333355
theorem B11698505 : Blo 1368503 11698505 := bstep (se 2 (by rfl) ⟨4386939, by rfl⟩ : syracuseStep 11698505 = 8773879) B8773879
theorem B5849441 : Blo 1368503 5849441 := bstep (se 2 (by rfl) ⟨2193540, by rfl⟩ : syracuseStep 5849441 = 4387081) B4387081
theorem B4620671 : Blo 1368503 4620671 := bstep (se 1 (by rfl) ⟨3465503, by rfl⟩ : syracuseStep 4620671 = 6931007) B6931007
theorem B133325261 : Blo 1368503 133325261 := bstep (se 3 (by rfl) ⟨24998486, by rfl⟩ : syracuseStep 133325261 = 49996973) B49996973
theorem B1368603 : Blo 1368503 1368603 := bstep (se 1 (by rfl) ⟨1026452, by rfl⟩ : syracuseStep 1368603 = 2052905) B2052905
theorem B1368607 : Blo 1368503 1368607 := bstep (se 1 (by rfl) ⟨1026455, by rfl⟩ : syracuseStep 1368607 = 2052911) B2052911
theorem B3080735 : Blo 1368503 3080735 := bstep (se 1 (by rfl) ⟨2310551, by rfl⟩ : syracuseStep 3080735 = 4621103) B4621103
theorem B3080807 : Blo 1368503 3080807 := bstep (se 1 (by rfl) ⟨2310605, by rfl⟩ : syracuseStep 3080807 = 4621211) B4621211
theorem B2310761 : Blo 1368503 2310761 := bstep (se 2 (by rfl) ⟨866535, by rfl⟩ : syracuseStep 2310761 = 1733071) B1733071
theorem B1368687 : Blo 1368503 1368687 := bstep (se 1 (by rfl) ⟨1026515, by rfl⟩ : syracuseStep 1368687 = 2053031) B2053031
theorem B1368743 : Blo 1368503 1368743 := bstep (se 1 (by rfl) ⟨1026557, by rfl⟩ : syracuseStep 1368743 = 2053115) B2053115
theorem B1368783 : Blo 1368503 1368783 := bstep (se 1 (by rfl) ⟨1026587, by rfl⟩ : syracuseStep 1368783 = 2053175) B2053175
theorem B8774365 : Blo 1368503 8774365 := bstep (se 3 (by rfl) ⟨1645193, by rfl⟩ : syracuseStep 8774365 = 3290387) B3290387
theorem B1368863 : Blo 1368503 1368863 := bstep (se 1 (by rfl) ⟨1026647, by rfl⟩ : syracuseStep 1368863 = 2053295) B2053295
theorem B10404773 : Blo 1368503 10404773 := bstep (se 4 (by rfl) ⟨975447, by rfl⟩ : syracuseStep 10404773 = 1950895) B1950895
theorem B3900413 : Blo 1368503 3900413 := bstep (se 3 (by rfl) ⟨731327, by rfl⟩ : syracuseStep 3900413 = 1462655) B1462655
theorem B1369135 : Blo 1368503 1369135 := bstep (se 1 (by rfl) ⟨1026851, by rfl⟩ : syracuseStep 1369135 = 2053703) B2053703
theorem B1369199 : Blo 1368503 1369199 := bstep (se 1 (by rfl) ⟨1026899, by rfl⟩ : syracuseStep 1369199 = 2053799) B2053799
theorem B12657809 : Blo 1368503 12657809 := bstep (se 2 (by rfl) ⟨4746678, by rfl⟩ : syracuseStep 12657809 = 9493357) B9493357
theorem B1369255 : Blo 1368503 1369255 := bstep (se 1 (by rfl) ⟨1026941, by rfl⟩ : syracuseStep 1369255 = 2053883) B2053883
theorem B1369279 : Blo 1368503 1369279 := bstep (se 1 (by rfl) ⟨1026959, by rfl⟩ : syracuseStep 1369279 = 2053919) B2053919
theorem B24970463 : Blo 1368503 24970463 := bstep (se 1 (by rfl) ⟨18727847, by rfl⟩ : syracuseStep 24970463 = 37455695) B37455695
theorem B1369311 : Blo 1368503 1369311 := bstep (se 1 (by rfl) ⟨1026983, by rfl⟩ : syracuseStep 1369311 = 2053967) B2053967
theorem B4621535 : Blo 1368503 4621535 := bstep (se 1 (by rfl) ⟨3466151, by rfl⟩ : syracuseStep 4621535 = 6932303) B6932303
theorem B1369391 : Blo 1368503 1369391 := bstep (se 1 (by rfl) ⟨1027043, by rfl⟩ : syracuseStep 1369391 = 2054087) B2054087
theorem B3081563 : Blo 1368503 3081563 := bstep (se 1 (by rfl) ⟨2311172, by rfl⟩ : syracuseStep 3081563 = 4622345) B4622345
theorem B1369627 : Blo 1368503 1369627 := bstep (se 1 (by rfl) ⟨1027220, by rfl⟩ : syracuseStep 1369627 = 2054441) B2054441
theorem B1541659 : Blo 1368503 1541659 := bstep (se 1 (by rfl) ⟨1156244, by rfl⟩ : syracuseStep 1541659 = 2312489) B2312489
theorem B1369631 : Blo 1368503 1369631 := bstep (se 1 (by rfl) ⟨1027223, by rfl⟩ : syracuseStep 1369631 = 2054447) B2054447
theorem B3081833 : Blo 1368503 3081833 := bstep (se 2 (by rfl) ⟨1155687, by rfl⟩ : syracuseStep 3081833 = 2311375) B2311375
theorem B2311787 : Blo 1368503 2311787 := bstep (se 1 (by rfl) ⟨1733840, by rfl⟩ : syracuseStep 2311787 = 3467681) B3467681
theorem B1369791 : Blo 1368503 1369791 := bstep (se 1 (by rfl) ⟨1027343, by rfl⟩ : syracuseStep 1369791 = 2054687) B2054687
theorem B2312057 : Blo 1368503 2312057 := bstep (se 2 (by rfl) ⟨867021, by rfl⟩ : syracuseStep 2312057 = 1734043) B1734043
theorem B1370047 : Blo 1368503 1370047 := bstep (se 1 (by rfl) ⟨1027535, by rfl⟩ : syracuseStep 1370047 = 2055071) B2055071
theorem B13158359 : Blo 1368503 13158359 := bstep (se 1 (by rfl) ⟨9868769, by rfl⟩ : syracuseStep 13158359 = 19737539) B19737539
theorem B1370079 : Blo 1368503 1370079 := bstep (se 1 (by rfl) ⟨1027559, by rfl⟩ : syracuseStep 1370079 = 2055119) B2055119
theorem B1370139 : Blo 1368503 1370139 := bstep (se 1 (by rfl) ⟨1027604, by rfl⟩ : syracuseStep 1370139 = 2055209) B2055209
theorem B1370143 : Blo 1368503 1370143 := bstep (se 1 (by rfl) ⟨1027607, by rfl⟩ : syracuseStep 1370143 = 2055215) B2055215
theorem B1370159 : Blo 1368503 1370159 := bstep (se 1 (by rfl) ⟨1027619, by rfl⟩ : syracuseStep 1370159 = 2055239) B2055239
theorem B17541197 : Blo 1368503 17541197 := bstep (se 3 (by rfl) ⟨3288974, by rfl⟩ : syracuseStep 17541197 = 6577949) B6577949
theorem B3467387 : Blo 1368503 3467387 := bstep (se 1 (by rfl) ⟨2600540, by rfl⟩ : syracuseStep 3467387 = 5201081) B5201081
theorem B3467407 : Blo 1368503 3467407 := bstep (se 1 (by rfl) ⟨2600555, by rfl⟩ : syracuseStep 3467407 = 5201111) B5201111
theorem B6932627 : Blo 1368503 6932627 := bstep (se 1 (by rfl) ⟨5199470, by rfl⟩ : syracuseStep 6932627 = 10398941) B10398941
theorem B3082427 : Blo 1368503 3082427 := bstep (se 1 (by rfl) ⟨2311820, by rfl⟩ : syracuseStep 3082427 = 4623641) B4623641
theorem B3082463 : Blo 1368503 3082463 := bstep (se 1 (by rfl) ⟨2311847, by rfl⟩ : syracuseStep 3082463 = 4623695) B4623695
theorem B1370335 : Blo 1368503 1370335 := bstep (se 1 (by rfl) ⟨1027751, by rfl⟩ : syracuseStep 1370335 = 2055503) B2055503
theorem B1370395 : Blo 1368503 1370395 := bstep (se 1 (by rfl) ⟨1027796, by rfl⟩ : syracuseStep 1370395 = 2055593) B2055593
theorem B1370495 : Blo 1368503 1370495 := bstep (se 1 (by rfl) ⟨1027871, by rfl⟩ : syracuseStep 1370495 = 2055743) B2055743
theorem B2312617 : Blo 1368503 2312617 := bstep (se 2 (by rfl) ⟨867231, by rfl⟩ : syracuseStep 2312617 = 1734463) B1734463
theorem B3901871 : Blo 1368503 3901871 := bstep (se 1 (by rfl) ⟨2926403, by rfl⟩ : syracuseStep 3901871 = 5852807) B5852807
theorem B6580889 : Blo 1368503 6580889 := bstep (se 2 (by rfl) ⟨2467833, by rfl⟩ : syracuseStep 6580889 = 4935667) B4935667
theorem B3082913 : Blo 1368503 3082913 := bstep (se 2 (by rfl) ⟨1156092, by rfl⟩ : syracuseStep 3082913 = 2312185) B2312185
theorem B3083129 : Blo 1368503 3083129 := bstep (se 2 (by rfl) ⟨1156173, by rfl⟩ : syracuseStep 3083129 = 2312347) B2312347
theorem B4623263 : Blo 1368503 4623263 := bstep (se 1 (by rfl) ⟨3467447, by rfl⟩ : syracuseStep 4623263 = 6934895) B6934895
theorem B3083273 : Blo 1368503 3083273 := bstep (se 2 (by rfl) ⟨1156227, by rfl⟩ : syracuseStep 3083273 = 2312455) B2312455
theorem B7801919 : Blo 1368503 7801919 := bstep (se 1 (by rfl) ⟨5851439, by rfl⟩ : syracuseStep 7801919 = 11702879) B11702879
theorem B3083327 : Blo 1368503 3083327 := bstep (se 1 (by rfl) ⟨2312495, by rfl⟩ : syracuseStep 3083327 = 4624991) B4624991
theorem B2600009 : Blo 1368503 2600009 := bstep (se 2 (by rfl) ⟨975003, by rfl⟩ : syracuseStep 2600009 = 1950007) B1950007
theorem B6336001 : Blo 1368503 6336001 := bstep (se 2 (by rfl) ⟨2376000, by rfl⟩ : syracuseStep 6336001 = 4752001) B4752001
theorem B5271335 : Blo 1368503 5271335 := bstep (se 1 (by rfl) ⟨3953501, by rfl⟩ : syracuseStep 5271335 = 7907003) B7907003
theorem B9375529 : Blo 1368503 9375529 := bstep (se 2 (by rfl) ⟨3515823, by rfl⟩ : syracuseStep 9375529 = 7031647) B7031647
theorem B22212575 : Blo 1368503 22212575 := bstep (se 1 (by rfl) ⟨16659431, by rfl⟩ : syracuseStep 22212575 = 33318863) B33318863
theorem B3289081 : Blo 1368503 3289081 := bstep (se 2 (by rfl) ⟨1233405, by rfl⟩ : syracuseStep 3289081 = 2466811) B2466811
theorem B6582505 : Blo 1368503 6582505 := bstep (se 2 (by rfl) ⟨2468439, by rfl⟩ : syracuseStep 6582505 = 4936879) B4936879
theorem B4624829 : Blo 1368503 4624829 := bstep (se 3 (by rfl) ⟨867155, by rfl⟩ : syracuseStep 4624829 = 1734311) B1734311
theorem B21074377 : Blo 1368503 21074377 := bstep (se 2 (by rfl) ⟨7902891, by rfl⟩ : syracuseStep 21074377 = 15805783) B15805783
theorem B16659047 : Blo 1368503 16659047 := bstep (se 1 (by rfl) ⟨12494285, by rfl⟩ : syracuseStep 16659047 = 24988571) B24988571
theorem B2053103 : Blo 1368503 2053103 := bstep (se 1 (by rfl) ⟨1539827, by rfl⟩ : syracuseStep 2053103 = 3079655) B3079655
theorem B5846057 : Blo 1368503 5846057 := bstep (se 2 (by rfl) ⟨2192271, by rfl⟩ : syracuseStep 5846057 = 4384543) B4384543
theorem B1733815 : Blo 1368503 1733815 := bstep (se 1 (by rfl) ⟨1300361, by rfl⟩ : syracuseStep 1733815 = 2600723) B2600723
theorem B2053487 : Blo 1368503 2053487 := bstep (se 1 (by rfl) ⟨1540115, by rfl⟩ : syracuseStep 2053487 = 3080231) B3080231
theorem B2053607 : Blo 1368503 2053607 := bstep (se 1 (by rfl) ⟨1540205, by rfl⟩ : syracuseStep 2053607 = 3080411) B3080411
theorem B2053769 : Blo 1368503 2053769 := bstep (se 2 (by rfl) ⟨770163, by rfl⟩ : syracuseStep 2053769 = 1540327) B1540327
theorem B5846671 : Blo 1368503 5846671 := bstep (se 1 (by rfl) ⟨4385003, by rfl⟩ : syracuseStep 5846671 = 8770007) B8770007
theorem B2053787 : Blo 1368503 2053787 := bstep (se 1 (by rfl) ⟨1540340, by rfl⟩ : syracuseStep 2053787 = 3080681) B3080681
theorem B2569961 : Blo 1368503 2569961 := bstep (se 2 (by rfl) ⟨963735, by rfl⟩ : syracuseStep 2569961 = 1927471) B1927471
theorem B42145541 : Blo 1368503 42145541 := bstep (se 4 (by rfl) ⟨3951144, by rfl⟩ : syracuseStep 42145541 = 7902289) B7902289
theorem B2053979 : Blo 1368503 2053979 := bstep (se 1 (by rfl) ⟨1540484, by rfl⟩ : syracuseStep 2053979 = 3080969) B3080969
theorem B6928253 : Blo 1368503 6928253 := bstep (se 3 (by rfl) ⟨1299047, by rfl⟩ : syracuseStep 6928253 = 2598095) B2598095
theorem B5199835 : Blo 1368503 5199835 := bstep (se 1 (by rfl) ⟨3899876, by rfl⟩ : syracuseStep 5199835 = 7799753) B7799753
theorem B6576275 : Blo 1368503 6576275 := bstep (se 1 (by rfl) ⟨4932206, by rfl⟩ : syracuseStep 6576275 = 9864413) B9864413
theorem B6584503 : Blo 1368503 6584503 := bstep (se 1 (by rfl) ⟨4938377, by rfl⟩ : syracuseStep 6584503 = 9876755) B9876755
theorem B2054363 : Blo 1368503 2054363 := bstep (se 1 (by rfl) ⟨1540772, by rfl⟩ : syracuseStep 2054363 = 3081545) B3081545
theorem B13154669 : Blo 1368503 13154669 := bstep (se 3 (by rfl) ⟨2466500, by rfl⟩ : syracuseStep 13154669 = 4933001) B4933001
theorem B2054633 : Blo 1368503 2054633 := bstep (se 2 (by rfl) ⟨770487, by rfl⟩ : syracuseStep 2054633 = 1540975) B1540975
theorem B4938349 : Blo 1368503 4938349 := bstep (se 3 (by rfl) ⟨925940, by rfl⟩ : syracuseStep 4938349 = 1851881) B1851881
theorem B4389719 : Blo 1368503 4389719 := bstep (se 1 (by rfl) ⟨3292289, by rfl⟩ : syracuseStep 4389719 = 6584579) B6584579
theorem B2055023 : Blo 1368503 2055023 := bstep (se 1 (by rfl) ⟨1541267, by rfl⟩ : syracuseStep 2055023 = 3082535) B3082535
theorem B2055035 : Blo 1368503 2055035 := bstep (se 1 (by rfl) ⟨1541276, by rfl⟩ : syracuseStep 2055035 = 3082553) B3082553
theorem B8780669 : Blo 1368503 8780669 := bstep (se 3 (by rfl) ⟨1646375, by rfl⟩ : syracuseStep 8780669 = 3292751) B3292751
theorem B18733979 : Blo 1368503 18733979 := bstep (se 1 (by rfl) ⟨14050484, by rfl⟩ : syracuseStep 18733979 = 28100969) B28100969
theorem B1948583 : Blo 1368503 1948583 := bstep (se 1 (by rfl) ⟨1461437, by rfl⟩ : syracuseStep 1948583 = 2922875) B2922875
theorem B3079259 : Blo 1368503 3079259 := bstep (se 1 (by rfl) ⟨2309444, by rfl⟩ : syracuseStep 3079259 = 4618889) B4618889
theorem B1481819 : Blo 1368503 1481819 := bstep (se 1 (by rfl) ⟨1111364, by rfl⟩ : syracuseStep 1481819 = 2222729) B2222729
theorem B6585695 : Blo 1368503 6585695 := bstep (se 1 (by rfl) ⟨4939271, by rfl⟩ : syracuseStep 6585695 = 9878543) B9878543
theorem B7216559 : Blo 1368503 7216559 := bstep (se 1 (by rfl) ⟨5412419, by rfl⟩ : syracuseStep 7216559 = 10824839) B10824839
theorem B2923951 : Blo 1368503 2923951 := bstep (se 1 (by rfl) ⟨2192963, by rfl⟩ : syracuseStep 2923951 = 4385927) B4385927
theorem B11861477 : Blo 1368503 11861477 := bstep (se 4 (by rfl) ⟨1112013, by rfl⟩ : syracuseStep 11861477 = 2224027) B2224027
theorem B5004791 : Blo 1368503 5004791 := bstep (se 1 (by rfl) ⟨3753593, by rfl⟩ : syracuseStep 5004791 = 7507187) B7507187
theorem B1539751 : Blo 1368503 1539751 := bstep (se 1 (by rfl) ⟨1154813, by rfl⟩ : syracuseStep 1539751 = 2309627) B2309627
theorem B2342623 : Blo 1368503 2342623 := bstep (se 1 (by rfl) ⟨1756967, by rfl⟩ : syracuseStep 2342623 = 3513935) B3513935
theorem B2309863 : Blo 1368503 2309863 := bstep (se 1 (by rfl) ⟨1732397, by rfl⟩ : syracuseStep 2309863 = 3464795) B3464795
theorem B2309897 : Blo 1368503 2309897 := bstep (se 2 (by rfl) ⟨866211, by rfl⟩ : syracuseStep 2309897 = 1732423) B1732423
theorem B1949449 : Blo 1368503 1949449 := bstep (se 2 (by rfl) ⟨731043, by rfl⟩ : syracuseStep 1949449 = 1462087) B1462087
theorem B3080015 : Blo 1368503 3080015 := bstep (se 1 (by rfl) ⟨2310011, by rfl⟩ : syracuseStep 3080015 = 4620023) B4620023
theorem B120094595 : Blo 1368503 120094595 := bstep (se 1 (by rfl) ⟨90070946, by rfl⟩ : syracuseStep 120094595 = 180141893) B180141893
theorem B1540039 : Blo 1368503 1540039 := bstep (se 1 (by rfl) ⟨1155029, by rfl⟩ : syracuseStep 1540039 = 2310059) B2310059
theorem B33792005 : Blo 1368503 33792005 := bstep (se 4 (by rfl) ⟨3168000, by rfl⟩ : syracuseStep 33792005 = 6336001) B6336001
theorem B7799003 : Blo 1368503 7799003 := bstep (se 1 (by rfl) ⟨5849252, by rfl⟩ : syracuseStep 7799003 = 11698505) B11698505
theorem B3899627 : Blo 1368503 3899627 := bstep (se 1 (by rfl) ⟨2924720, by rfl⟩ : syracuseStep 3899627 = 5849441) B5849441
theorem B3080447 : Blo 1368503 3080447 := bstep (se 1 (by rfl) ⟨2310335, by rfl⟩ : syracuseStep 3080447 = 4620671) B4620671
theorem B88883507 : Blo 1368503 88883507 := bstep (se 1 (by rfl) ⟨66662630, by rfl⟩ : syracuseStep 88883507 = 133325261) B133325261
theorem B1540507 : Blo 1368503 1540507 := bstep (se 1 (by rfl) ⟨1155380, by rfl⟩ : syracuseStep 1540507 = 2310761) B2310761
theorem B91259297 : Blo 1368503 91259297 := bstep (se 2 (by rfl) ⟨34222236, by rfl⟩ : syracuseStep 91259297 = 68444473) B68444473
theorem B28099169 : Blo 1368503 28099169 := bstep (se 2 (by rfl) ⟨10537188, by rfl⟩ : syracuseStep 28099169 = 21074377) B21074377
theorem B1368735 : Blo 1368503 1368735 := bstep (se 1 (by rfl) ⟨1026551, by rfl⟩ : syracuseStep 1368735 = 2053103) B2053103
theorem B8438539 : Blo 1368503 8438539 := bstep (se 1 (by rfl) ⟨6328904, by rfl⟩ : syracuseStep 8438539 = 12657809) B12657809
theorem B16646975 : Blo 1368503 16646975 := bstep (se 1 (by rfl) ⟨12485231, by rfl⟩ : syracuseStep 16646975 = 24970463) B24970463
theorem B3081023 : Blo 1368503 3081023 := bstep (se 1 (by rfl) ⟨2310767, by rfl⟩ : syracuseStep 3081023 = 4621535) B4621535
theorem B1368991 : Blo 1368503 1368991 := bstep (se 1 (by rfl) ⟨1026743, by rfl⟩ : syracuseStep 1368991 = 2053487) B2053487
theorem B11699153 : Blo 1368503 11699153 := bstep (se 2 (by rfl) ⟨4387182, by rfl⟩ : syracuseStep 11699153 = 8774365) B8774365
theorem B1369071 : Blo 1368503 1369071 := bstep (se 1 (by rfl) ⟨1026803, by rfl⟩ : syracuseStep 1369071 = 2053607) B2053607
theorem B1541191 : Blo 1368503 1541191 := bstep (se 1 (by rfl) ⟨1155893, by rfl⟩ : syracuseStep 1541191 = 2311787) B2311787
theorem B1369179 : Blo 1368503 1369179 := bstep (se 1 (by rfl) ⟨1026884, by rfl⟩ : syracuseStep 1369179 = 2053769) B2053769
theorem B1369191 : Blo 1368503 1369191 := bstep (se 1 (by rfl) ⟨1026893, by rfl⟩ : syracuseStep 1369191 = 2053787) B2053787
theorem B1713307 : Blo 1368503 1713307 := bstep (se 1 (by rfl) ⟨1284980, by rfl⟩ : syracuseStep 1713307 = 2569961) B2569961
theorem B1369319 : Blo 1368503 1369319 := bstep (se 1 (by rfl) ⟨1026989, by rfl⟩ : syracuseStep 1369319 = 2053979) B2053979
theorem B1541371 : Blo 1368503 1541371 := bstep (se 1 (by rfl) ⟨1156028, by rfl⟩ : syracuseStep 1541371 = 2312057) B2312057
theorem B2311591 : Blo 1368503 2311591 := bstep (se 1 (by rfl) ⟨1733693, by rfl⟩ : syracuseStep 2311591 = 3467387) B3467387
theorem B4621751 : Blo 1368503 4621751 := bstep (se 1 (by rfl) ⟨3466313, by rfl⟩ : syracuseStep 4621751 = 6932627) B6932627
theorem B1369575 : Blo 1368503 1369575 := bstep (se 1 (by rfl) ⟨1027181, by rfl⟩ : syracuseStep 1369575 = 2054363) B2054363
theorem B2311753 : Blo 1368503 2311753 := bstep (se 2 (by rfl) ⟨866907, by rfl⟩ : syracuseStep 2311753 = 1733815) B1733815
theorem B1369755 : Blo 1368503 1369755 := bstep (se 1 (by rfl) ⟨1027316, by rfl⟩ : syracuseStep 1369755 = 2054633) B2054633
theorem B1370015 : Blo 1368503 1370015 := bstep (se 1 (by rfl) ⟨1027511, by rfl⟩ : syracuseStep 1370015 = 2055023) B2055023
theorem B1370023 : Blo 1368503 1370023 := bstep (se 1 (by rfl) ⟨1027517, by rfl⟩ : syracuseStep 1370023 = 2055035) B2055035
theorem B3082175 : Blo 1368503 3082175 := bstep (se 1 (by rfl) ⟨2311631, by rfl⟩ : syracuseStep 3082175 = 4623263) B4623263
theorem B4811039 : Blo 1368503 4811039 := bstep (se 1 (by rfl) ⟨3608279, by rfl⟩ : syracuseStep 4811039 = 7216559) B7216559
theorem B7907651 : Blo 1368503 7907651 := bstep (se 1 (by rfl) ⟨5930738, by rfl⟩ : syracuseStep 7907651 = 11861477) B11861477
theorem B3336527 : Blo 1368503 3336527 := bstep (se 1 (by rfl) ⟨2502395, by rfl⟩ : syracuseStep 3336527 = 5004791) B5004791
theorem B2599265 : Blo 1368503 2599265 := bstep (se 2 (by rfl) ⟨974724, by rfl⟩ : syracuseStep 2599265 = 1949449) B1949449
theorem B5196221 : Blo 1368503 5196221 := bstep (se 3 (by rfl) ⟨974291, by rfl⟩ : syracuseStep 5196221 = 1948583) B1948583
theorem B80063063 : Blo 1368503 80063063 := bstep (se 1 (by rfl) ⟨60047297, by rfl⟩ : syracuseStep 80063063 = 120094595) B120094595
theorem B6933113 : Blo 1368503 6933113 := bstep (se 2 (by rfl) ⟨2599917, by rfl⟩ : syracuseStep 6933113 = 5199835) B5199835
theorem B4385441 : Blo 1368503 4385441 := bstep (se 2 (by rfl) ⟨1644540, by rfl⟩ : syracuseStep 4385441 = 3289081) B3289081
theorem B4623209 : Blo 1368503 4623209 := bstep (se 2 (by rfl) ⟨1733703, by rfl⟩ : syracuseStep 4623209 = 3467407) B3467407
theorem B3951517 : Blo 1368503 3951517 := bstep (se 3 (by rfl) ⟨740909, by rfl⟩ : syracuseStep 3951517 = 1481819) B1481819
theorem B3083219 : Blo 1368503 3083219 := bstep (se 1 (by rfl) ⟨2312414, by rfl⟩ : syracuseStep 3083219 = 4624829) B4624829
theorem B8776673 : Blo 1368503 8776673 := bstep (se 2 (by rfl) ⟨3291252, by rfl⟩ : syracuseStep 8776673 = 6582505) B6582505
theorem B3083489 : Blo 1368503 3083489 := bstep (se 2 (by rfl) ⟨1156308, by rfl⟩ : syracuseStep 3083489 = 2312617) B2312617
theorem B2600275 : Blo 1368503 2600275 := bstep (se 1 (by rfl) ⟨1950206, by rfl⟩ : syracuseStep 2600275 = 3900413) B3900413
theorem B11694131 : Blo 1368503 11694131 := bstep (se 1 (by rfl) ⟨8770598, by rfl⟩ : syracuseStep 11694131 = 17541197) B17541197
theorem B8769779 : Blo 1368503 8769779 := bstep (se 1 (by rfl) ⟨6577334, by rfl⟩ : syracuseStep 8769779 = 13154669) B13154669
theorem B2601247 : Blo 1368503 2601247 := bstep (se 1 (by rfl) ⟨1950935, by rfl⟩ : syracuseStep 2601247 = 3901871) B3901871
theorem B4387259 : Blo 1368503 4387259 := bstep (se 1 (by rfl) ⟨3290444, by rfl⟩ : syracuseStep 4387259 = 6580889) B6580889
theorem B5853779 : Blo 1368503 5853779 := bstep (se 1 (by rfl) ⟨4390334, by rfl⟩ : syracuseStep 5853779 = 8780669) B8780669
theorem B12489319 : Blo 1368503 12489319 := bstep (se 1 (by rfl) ⟨9366989, by rfl⟩ : syracuseStep 12489319 = 18733979) B18733979
theorem B49975957 : Blo 1368503 49975957 := bstep (se 6 (by rfl) ⟨1171311, by rfl⟩ : syracuseStep 49975957 = 2342623) B2342623
theorem B1733339 : Blo 1368503 1733339 := bstep (se 1 (by rfl) ⟨1300004, by rfl⟩ : syracuseStep 1733339 = 2600009) B2600009
theorem B2052839 : Blo 1368503 2052839 := bstep (se 1 (by rfl) ⟨1539629, by rfl⟩ : syracuseStep 2052839 = 3079259) B3079259
theorem B7795561 : Blo 1368503 7795561 := bstep (se 2 (by rfl) ⟨2923335, by rfl⟩ : syracuseStep 7795561 = 5846671) B5846671
theorem B2053001 : Blo 1368503 2053001 := bstep (se 2 (by rfl) ⟨769875, by rfl⟩ : syracuseStep 2053001 = 1539751) B1539751
theorem B2053343 : Blo 1368503 2053343 := bstep (se 1 (by rfl) ⟨1540007, by rfl⟩ : syracuseStep 2053343 = 3080015) B3080015
theorem B2053385 : Blo 1368503 2053385 := bstep (se 2 (by rfl) ⟨770019, by rfl⟩ : syracuseStep 2053385 = 1540039) B1540039
theorem B14808383 : Blo 1368503 14808383 := bstep (se 1 (by rfl) ⟨11106287, by rfl⟩ : syracuseStep 14808383 = 22212575) B22212575
theorem B8779337 : Blo 1368503 8779337 := bstep (se 2 (by rfl) ⟨3292251, by rfl⟩ : syracuseStep 8779337 = 6584503) B6584503
theorem B2053823 : Blo 1368503 2053823 := bstep (se 1 (by rfl) ⟨1540367, by rfl⟩ : syracuseStep 2053823 = 3080735) B3080735
theorem B17536733 : Blo 1368503 17536733 := bstep (se 3 (by rfl) ⟨3288137, by rfl⟩ : syracuseStep 17536733 = 6576275) B6576275
theorem B2053865 : Blo 1368503 2053865 := bstep (se 2 (by rfl) ⟨770199, by rfl⟩ : syracuseStep 2053865 = 1540399) B1540399
theorem B2053871 : Blo 1368503 2053871 := bstep (se 1 (by rfl) ⟨1540403, by rfl⟩ : syracuseStep 2053871 = 3080807) B3080807
theorem B11106031 : Blo 1368503 11106031 := bstep (se 1 (by rfl) ⟨8329523, by rfl⟩ : syracuseStep 11106031 = 16659047) B16659047
theorem B6936515 : Blo 1368503 6936515 := bstep (se 1 (by rfl) ⟨5202386, by rfl⟩ : syracuseStep 6936515 = 10404773) B10404773
theorem B3897371 : Blo 1368503 3897371 := bstep (se 1 (by rfl) ⟨2923028, by rfl⟩ : syracuseStep 3897371 = 5846057) B5846057
theorem B6584465 : Blo 1368503 6584465 := bstep (se 2 (by rfl) ⟨2469174, by rfl⟩ : syracuseStep 6584465 = 4938349) B4938349
theorem B2054375 : Blo 1368503 2054375 := bstep (se 1 (by rfl) ⟨1540781, by rfl⟩ : syracuseStep 2054375 = 3081563) B3081563
theorem B2054555 : Blo 1368503 2054555 := bstep (se 1 (by rfl) ⟨1540916, by rfl⟩ : syracuseStep 2054555 = 3081833) B3081833
theorem B28097027 : Blo 1368503 28097027 := bstep (se 1 (by rfl) ⟨21072770, by rfl⟩ : syracuseStep 28097027 = 42145541) B42145541
theorem B4618835 : Blo 1368503 4618835 := bstep (se 1 (by rfl) ⟨3464126, by rfl⟩ : syracuseStep 4618835 = 6928253) B6928253
theorem B8772239 : Blo 1368503 8772239 := bstep (se 1 (by rfl) ⟨6579179, by rfl⟩ : syracuseStep 8772239 = 13158359) B13158359
theorem B2054951 : Blo 1368503 2054951 := bstep (se 1 (by rfl) ⟨1541213, by rfl⟩ : syracuseStep 2054951 = 3082427) B3082427
theorem B2054975 : Blo 1368503 2054975 := bstep (se 1 (by rfl) ⟨1541231, by rfl⟩ : syracuseStep 2054975 = 3082463) B3082463
theorem B2055275 : Blo 1368503 2055275 := bstep (se 1 (by rfl) ⟨1541456, by rfl⟩ : syracuseStep 2055275 = 3082913) B3082913
theorem B3898601 : Blo 1368503 3898601 := bstep (se 2 (by rfl) ⟨1461975, by rfl⟩ : syracuseStep 3898601 = 2923951) B2923951
theorem B2055419 : Blo 1368503 2055419 := bstep (se 1 (by rfl) ⟨1541564, by rfl⟩ : syracuseStep 2055419 = 3083129) B3083129
theorem B2055515 : Blo 1368503 2055515 := bstep (se 1 (by rfl) ⟨1541636, by rfl⟩ : syracuseStep 2055515 = 3083273) B3083273
theorem B2055545 : Blo 1368503 2055545 := bstep (se 2 (by rfl) ⟨770829, by rfl⟩ : syracuseStep 2055545 = 1541659) B1541659
theorem B5201279 : Blo 1368503 5201279 := bstep (se 1 (by rfl) ⟨3900959, by rfl⟩ : syracuseStep 5201279 = 7801919) B7801919
theorem B2055551 : Blo 1368503 2055551 := bstep (se 1 (by rfl) ⟨1541663, by rfl⟩ : syracuseStep 2055551 = 3083327) B3083327
theorem B11705917 : Blo 1368503 11705917 := bstep (se 3 (by rfl) ⟨2194859, by rfl⟩ : syracuseStep 11705917 = 4389719) B4389719
theorem B4390463 : Blo 1368503 4390463 := bstep (se 1 (by rfl) ⟨3292847, by rfl⟩ : syracuseStep 4390463 = 6585695) B6585695
theorem B3079817 : Blo 1368503 3079817 := bstep (se 2 (by rfl) ⟨1154931, by rfl⟩ : syracuseStep 3079817 = 2309863) B2309863
theorem B12500705 : Blo 1368503 12500705 := bstep (se 2 (by rfl) ⟨4687764, by rfl⟩ : syracuseStep 12500705 = 9375529) B9375529
theorem B1539931 : Blo 1368503 1539931 := bstep (se 1 (by rfl) ⟨1154948, by rfl⟩ : syracuseStep 1539931 = 2309897) B2309897
theorem B3514223 : Blo 1368503 3514223 := bstep (se 1 (by rfl) ⟨2635667, by rfl⟩ : syracuseStep 3514223 = 5271335) B5271335
theorem B22528003 : Blo 1368503 22528003 := bstep (se 1 (by rfl) ⟨16896002, by rfl⟩ : syracuseStep 22528003 = 33792005) B33792005
theorem B2924839 : Blo 1368503 2924839 := bstep (se 1 (by rfl) ⟨2193629, by rfl⟩ : syracuseStep 2924839 = 4387259) B4387259
theorem B1368559 : Blo 1368503 1368559 := bstep (se 1 (by rfl) ⟨1026419, by rfl⟩ : syracuseStep 1368559 = 2052839) B2052839
theorem B66609701 : Blo 1368503 66609701 := bstep (se 4 (by rfl) ⟨6244659, by rfl⟩ : syracuseStep 66609701 = 12489319) B12489319
theorem B1368667 : Blo 1368503 1368667 := bstep (se 1 (by rfl) ⟨1026500, by rfl⟩ : syracuseStep 1368667 = 2053001) B2053001
theorem B7799435 : Blo 1368503 7799435 := bstep (se 1 (by rfl) ⟨5849576, by rfl⟩ : syracuseStep 7799435 = 11699153) B11699153
theorem B1368895 : Blo 1368503 1368895 := bstep (se 1 (by rfl) ⟨1026671, by rfl⟩ : syracuseStep 1368895 = 2053343) B2053343
theorem B1368923 : Blo 1368503 1368923 := bstep (se 1 (by rfl) ⟨1026692, by rfl⟩ : syracuseStep 1368923 = 2053385) B2053385
theorem B66634609 : Blo 1368503 66634609 := bstep (se 2 (by rfl) ⟨24987978, by rfl⟩ : syracuseStep 66634609 = 49975957) B49975957
theorem B9872255 : Blo 1368503 9872255 := bstep (se 1 (by rfl) ⟨7404191, by rfl⟩ : syracuseStep 9872255 = 14808383) B14808383
theorem B3081167 : Blo 1368503 3081167 := bstep (se 1 (by rfl) ⟨2310875, by rfl⟩ : syracuseStep 3081167 = 4621751) B4621751
theorem B1369215 : Blo 1368503 1369215 := bstep (se 1 (by rfl) ⟨1026911, by rfl⟩ : syracuseStep 1369215 = 2053823) B2053823
theorem B11691155 : Blo 1368503 11691155 := bstep (se 1 (by rfl) ⟨8768366, by rfl⟩ : syracuseStep 11691155 = 17536733) B17536733
theorem B1369243 : Blo 1368503 1369243 := bstep (se 1 (by rfl) ⟨1026932, by rfl⟩ : syracuseStep 1369243 = 2053865) B2053865
theorem B1369247 : Blo 1368503 1369247 := bstep (se 1 (by rfl) ⟨1026935, by rfl⟩ : syracuseStep 1369247 = 2053871) B2053871
theorem B5268689 : Blo 1368503 5268689 := bstep (se 2 (by rfl) ⟨1975758, by rfl⟩ : syracuseStep 5268689 = 3951517) B3951517
theorem B2598247 : Blo 1368503 2598247 := bstep (se 1 (by rfl) ⟨1948685, by rfl⟩ : syracuseStep 2598247 = 3897371) B3897371
theorem B1369583 : Blo 1368503 1369583 := bstep (se 1 (by rfl) ⟨1027187, by rfl⟩ : syracuseStep 1369583 = 2054375) B2054375
theorem B11707901 : Blo 1368503 11707901 := bstep (se 3 (by rfl) ⟨2195231, by rfl⟩ : syracuseStep 11707901 = 4390463) B4390463
theorem B1369703 : Blo 1368503 1369703 := bstep (se 1 (by rfl) ⟨1027277, by rfl⟩ : syracuseStep 1369703 = 2054555) B2054555
theorem B4622075 : Blo 1368503 4622075 := bstep (se 1 (by rfl) ⟨3466556, by rfl⟩ : syracuseStep 4622075 = 6933113) B6933113
theorem B3467033 : Blo 1368503 3467033 := bstep (se 2 (by rfl) ⟨1300137, by rfl⟩ : syracuseStep 3467033 = 2600275) B2600275
theorem B1369967 : Blo 1368503 1369967 := bstep (se 1 (by rfl) ⟨1027475, by rfl⟩ : syracuseStep 1369967 = 2054951) B2054951
theorem B1369983 : Blo 1368503 1369983 := bstep (se 1 (by rfl) ⟨1027487, by rfl⟩ : syracuseStep 1369983 = 2054975) B2054975
theorem B3082121 : Blo 1368503 3082121 := bstep (se 2 (by rfl) ⟨1155795, by rfl⟩ : syracuseStep 3082121 = 2311591) B2311591
theorem B3082139 : Blo 1368503 3082139 := bstep (se 1 (by rfl) ⟨2311604, by rfl⟩ : syracuseStep 3082139 = 4623209) B4623209
theorem B4622237 : Blo 1368503 4622237 := bstep (se 3 (by rfl) ⟨866669, by rfl⟩ : syracuseStep 4622237 = 1733339) B1733339
theorem B5851115 : Blo 1368503 5851115 := bstep (se 1 (by rfl) ⟨4388336, by rfl⟩ : syracuseStep 5851115 = 8776673) B8776673
theorem B1370183 : Blo 1368503 1370183 := bstep (se 1 (by rfl) ⟨1027637, by rfl⟩ : syracuseStep 1370183 = 2055275) B2055275
theorem B15607889 : Blo 1368503 15607889 := bstep (se 2 (by rfl) ⟨5852958, by rfl⟩ : syracuseStep 15607889 = 11705917) B11705917
theorem B3082337 : Blo 1368503 3082337 := bstep (se 2 (by rfl) ⟨1155876, by rfl⟩ : syracuseStep 3082337 = 2311753) B2311753
theorem B2599067 : Blo 1368503 2599067 := bstep (se 1 (by rfl) ⟨1949300, by rfl⟩ : syracuseStep 2599067 = 3898601) B3898601
theorem B1370279 : Blo 1368503 1370279 := bstep (se 1 (by rfl) ⟨1027709, by rfl⟩ : syracuseStep 1370279 = 2055419) B2055419
theorem B1370343 : Blo 1368503 1370343 := bstep (se 1 (by rfl) ⟨1027757, by rfl⟩ : syracuseStep 1370343 = 2055515) B2055515
theorem B1370363 : Blo 1368503 1370363 := bstep (se 1 (by rfl) ⟨1027772, by rfl⟩ : syracuseStep 1370363 = 2055545) B2055545
theorem B3467519 : Blo 1368503 3467519 := bstep (se 1 (by rfl) ⟨2600639, by rfl⟩ : syracuseStep 3467519 = 5201279) B5201279
theorem B1370367 : Blo 1368503 1370367 := bstep (se 1 (by rfl) ⟨1027775, by rfl⟩ : syracuseStep 1370367 = 2055551) B2055551
theorem B8333803 : Blo 1368503 8333803 := bstep (se 1 (by rfl) ⟨6250352, by rfl⟩ : syracuseStep 8333803 = 12500705) B12500705
theorem B2599751 : Blo 1368503 2599751 := bstep (se 1 (by rfl) ⟨1949813, by rfl⟩ : syracuseStep 2599751 = 3899627) B3899627
theorem B59255671 : Blo 1368503 59255671 := bstep (se 1 (by rfl) ⟨44441753, by rfl⟩ : syracuseStep 59255671 = 88883507) B88883507
theorem B3468329 : Blo 1368503 3468329 := bstep (se 2 (by rfl) ⟨1300623, by rfl⟩ : syracuseStep 3468329 = 2601247) B2601247
theorem B3902519 : Blo 1368503 3902519 := bstep (se 1 (by rfl) ⟨2926889, by rfl⟩ : syracuseStep 3902519 = 5853779) B5853779
theorem B11251385 : Blo 1368503 11251385 := bstep (se 2 (by rfl) ⟨4219269, by rfl⟩ : syracuseStep 11251385 = 8438539) B8438539
theorem B5852891 : Blo 1368503 5852891 := bstep (se 1 (by rfl) ⟨4389668, by rfl⟩ : syracuseStep 5852891 = 8779337) B8779337
theorem B4624343 : Blo 1368503 4624343 := bstep (se 1 (by rfl) ⟨3468257, by rfl⟩ : syracuseStep 4624343 = 6936515) B6936515
theorem B3207359 : Blo 1368503 3207359 := bstep (se 1 (by rfl) ⟨2405519, by rfl⟩ : syracuseStep 3207359 = 4811039) B4811039
theorem B5271767 : Blo 1368503 5271767 := bstep (se 1 (by rfl) ⟨3953825, by rfl⟩ : syracuseStep 5271767 = 7907651) B7907651
theorem B2224351 : Blo 1368503 2224351 := bstep (se 1 (by rfl) ⟨1668263, by rfl⟩ : syracuseStep 2224351 = 3336527) B3336527
theorem B1732843 : Blo 1368503 1732843 := bstep (se 1 (by rfl) ⟨1299632, by rfl⟩ : syracuseStep 1732843 = 2599265) B2599265
theorem B18731351 : Blo 1368503 18731351 := bstep (se 1 (by rfl) ⟨14048513, by rfl⟩ : syracuseStep 18731351 = 28097027) B28097027
theorem B53375375 : Blo 1368503 53375375 := bstep (se 1 (by rfl) ⟨40031531, by rfl⟩ : syracuseStep 53375375 = 80063063) B80063063
theorem B14808041 : Blo 1368503 14808041 := bstep (se 2 (by rfl) ⟨5553015, by rfl⟩ : syracuseStep 14808041 = 11106031) B11106031
theorem B2053211 : Blo 1368503 2053211 := bstep (se 1 (by rfl) ⟨1539908, by rfl⟩ : syracuseStep 2053211 = 3079817) B3079817
theorem B2053241 : Blo 1368503 2053241 := bstep (se 2 (by rfl) ⟨769965, by rfl⟩ : syracuseStep 2053241 = 1539931) B1539931
theorem B7796087 : Blo 1368503 7796087 := bstep (se 1 (by rfl) ⟨5847065, by rfl⟩ : syracuseStep 7796087 = 11694131) B11694131
theorem B5199335 : Blo 1368503 5199335 := bstep (se 1 (by rfl) ⟨3899501, by rfl⟩ : syracuseStep 5199335 = 7799003) B7799003
theorem B5846519 : Blo 1368503 5846519 := bstep (se 1 (by rfl) ⟨4384889, by rfl⟩ : syracuseStep 5846519 = 8769779) B8769779
theorem B2053631 : Blo 1368503 2053631 := bstep (se 1 (by rfl) ⟨1540223, by rfl⟩ : syracuseStep 2053631 = 3080447) B3080447
theorem B60839531 : Blo 1368503 60839531 := bstep (se 1 (by rfl) ⟨45629648, by rfl⟩ : syracuseStep 60839531 = 91259297) B91259297
theorem B18732779 : Blo 1368503 18732779 := bstep (se 1 (by rfl) ⟨14049584, by rfl⟩ : syracuseStep 18732779 = 28099169) B28099169
theorem B2054009 : Blo 1368503 2054009 := bstep (se 2 (by rfl) ⟨770253, by rfl⟩ : syracuseStep 2054009 = 1540507) B1540507
theorem B11097983 : Blo 1368503 11097983 := bstep (se 1 (by rfl) ⟨8323487, by rfl⟩ : syracuseStep 11097983 = 16646975) B16646975
theorem B2054015 : Blo 1368503 2054015 := bstep (se 1 (by rfl) ⟨1540511, by rfl⟩ : syracuseStep 2054015 = 3081023) B3081023
theorem B10394081 : Blo 1368503 10394081 := bstep (se 2 (by rfl) ⟨3897780, by rfl⟩ : syracuseStep 10394081 = 7795561) B7795561
theorem B2054783 : Blo 1368503 2054783 := bstep (se 1 (by rfl) ⟨1541087, by rfl⟩ : syracuseStep 2054783 = 3082175) B3082175
theorem B2054921 : Blo 1368503 2054921 := bstep (se 2 (by rfl) ⟨770595, by rfl⟩ : syracuseStep 2054921 = 1541191) B1541191
theorem B4389643 : Blo 1368503 4389643 := bstep (se 1 (by rfl) ⟨3292232, by rfl⟩ : syracuseStep 4389643 = 6584465) B6584465
theorem B2284409 : Blo 1368503 2284409 := bstep (se 2 (by rfl) ⟨856653, by rfl⟩ : syracuseStep 2284409 = 1713307) B1713307
theorem B3464147 : Blo 1368503 3464147 := bstep (se 1 (by rfl) ⟨2598110, by rfl⟩ : syracuseStep 3464147 = 5196221) B5196221
theorem B2055161 : Blo 1368503 2055161 := bstep (se 2 (by rfl) ⟨770685, by rfl⟩ : syracuseStep 2055161 = 1541371) B1541371
theorem B3079223 : Blo 1368503 3079223 := bstep (se 1 (by rfl) ⟨2309417, by rfl⟩ : syracuseStep 3079223 = 4618835) B4618835
theorem B5848159 : Blo 1368503 5848159 := bstep (se 1 (by rfl) ⟨4386119, by rfl⟩ : syracuseStep 5848159 = 8772239) B8772239
theorem B2923627 : Blo 1368503 2923627 := bstep (se 1 (by rfl) ⟨2192720, by rfl⟩ : syracuseStep 2923627 = 4385441) B4385441
theorem B2055479 : Blo 1368503 2055479 := bstep (se 1 (by rfl) ⟨1541609, by rfl⟩ : syracuseStep 2055479 = 3083219) B3083219
theorem B2055659 : Blo 1368503 2055659 := bstep (se 1 (by rfl) ⟨1541744, by rfl⟩ : syracuseStep 2055659 = 3083489) B3083489
theorem B9371261 : Blo 1368503 9371261 := bstep (se 3 (by rfl) ⟨1757111, by rfl⟩ : syracuseStep 9371261 = 3514223) B3514223
theorem B3514511 : Blo 1368503 3514511 := bstep (se 1 (by rfl) ⟨2635883, by rfl⟩ : syracuseStep 3514511 = 5271767) B5271767
theorem B2965801 : Blo 1368503 2965801 := bstep (se 2 (by rfl) ⟨1112175, by rfl⟩ : syracuseStep 2965801 = 2224351) B2224351
theorem B2310457 : Blo 1368503 2310457 := bstep (se 2 (by rfl) ⟨866421, by rfl⟩ : syracuseStep 2310457 = 1732843) B1732843
theorem B6930845 : Blo 1368503 6930845 := bstep (se 3 (by rfl) ⟨1299533, by rfl⟩ : syracuseStep 6930845 = 2599067) B2599067
theorem B8552957 : Blo 1368503 8552957 := bstep (se 3 (by rfl) ⟨1603679, by rfl⟩ : syracuseStep 8552957 = 3207359) B3207359
theorem B9872027 : Blo 1368503 9872027 := bstep (se 1 (by rfl) ⟨7404020, by rfl⟩ : syracuseStep 9872027 = 14808041) B14808041
theorem B1368807 : Blo 1368503 1368807 := bstep (se 1 (by rfl) ⟨1026605, by rfl⟩ : syracuseStep 1368807 = 2053211) B2053211
theorem B1368827 : Blo 1368503 1368827 := bstep (se 1 (by rfl) ⟨1026620, by rfl⟩ : syracuseStep 1368827 = 2053241) B2053241
theorem B3466223 : Blo 1368503 3466223 := bstep (se 1 (by rfl) ⟨2599667, by rfl⟩ : syracuseStep 3466223 = 5199335) B5199335
theorem B1369087 : Blo 1368503 1369087 := bstep (se 1 (by rfl) ⟨1026815, by rfl⟩ : syracuseStep 1369087 = 2053631) B2053631
theorem B40559687 : Blo 1368503 40559687 := bstep (se 1 (by rfl) ⟨30419765, by rfl⟩ : syracuseStep 40559687 = 60839531) B60839531
theorem B3081383 : Blo 1368503 3081383 := bstep (se 1 (by rfl) ⟨2311037, by rfl⟩ : syracuseStep 3081383 = 4622075) B4622075
theorem B2311355 : Blo 1368503 2311355 := bstep (se 1 (by rfl) ⟨1733516, by rfl⟩ : syracuseStep 2311355 = 3467033) B3467033
theorem B1369339 : Blo 1368503 1369339 := bstep (se 1 (by rfl) ⟨1027004, by rfl⟩ : syracuseStep 1369339 = 2054009) B2054009
theorem B1369343 : Blo 1368503 1369343 := bstep (se 1 (by rfl) ⟨1027007, by rfl⟩ : syracuseStep 1369343 = 2054015) B2054015
theorem B3081491 : Blo 1368503 3081491 := bstep (se 1 (by rfl) ⟨2311118, by rfl⟩ : syracuseStep 3081491 = 4622237) B4622237
theorem B3900743 : Blo 1368503 3900743 := bstep (se 1 (by rfl) ⟨2925557, by rfl⟩ : syracuseStep 3900743 = 5851115) B5851115
theorem B10405259 : Blo 1368503 10405259 := bstep (se 1 (by rfl) ⟨7803944, by rfl⟩ : syracuseStep 10405259 = 15607889) B15607889
theorem B2311679 : Blo 1368503 2311679 := bstep (se 1 (by rfl) ⟨1733759, by rfl⟩ : syracuseStep 2311679 = 3467519) B3467519
theorem B15599141 : Blo 1368503 15599141 := bstep (se 4 (by rfl) ⟨1462419, by rfl⟩ : syracuseStep 15599141 = 2924839) B2924839
theorem B1369855 : Blo 1368503 1369855 := bstep (se 1 (by rfl) ⟨1027391, by rfl⟩ : syracuseStep 1369855 = 2054783) B2054783
theorem B1369947 : Blo 1368503 1369947 := bstep (se 1 (by rfl) ⟨1027460, by rfl⟩ : syracuseStep 1369947 = 2054921) B2054921
theorem B1370107 : Blo 1368503 1370107 := bstep (se 1 (by rfl) ⟨1027580, by rfl⟩ : syracuseStep 1370107 = 2055161) B2055161
theorem B2312219 : Blo 1368503 2312219 := bstep (se 1 (by rfl) ⟨1734164, by rfl⟩ : syracuseStep 2312219 = 3468329) B3468329
theorem B1370319 : Blo 1368503 1370319 := bstep (se 1 (by rfl) ⟨1027739, by rfl⟩ : syracuseStep 1370319 = 2055479) B2055479
theorem B1370439 : Blo 1368503 1370439 := bstep (se 1 (by rfl) ⟨1027829, by rfl⟩ : syracuseStep 1370439 = 2055659) B2055659
theorem B3901927 : Blo 1368503 3901927 := bstep (se 1 (by rfl) ⟨2926445, by rfl⟩ : syracuseStep 3901927 = 5852891) B5852891
theorem B3082895 : Blo 1368503 3082895 := bstep (se 1 (by rfl) ⟨2312171, by rfl⟩ : syracuseStep 3082895 = 4624343) B4624343
theorem B10406717 : Blo 1368503 10406717 := bstep (se 3 (by rfl) ⟨1951259, by rfl⟩ : syracuseStep 10406717 = 3902519) B3902519
theorem B6581503 : Blo 1368503 6581503 := bstep (se 1 (by rfl) ⟨4936127, by rfl⟩ : syracuseStep 6581503 = 9872255) B9872255
theorem B11111737 : Blo 1368503 11111737 := bstep (se 2 (by rfl) ⟨4166901, by rfl⟩ : syracuseStep 11111737 = 8333803) B8333803
theorem B7794103 : Blo 1368503 7794103 := bstep (se 1 (by rfl) ⟨5845577, by rfl⟩ : syracuseStep 7794103 = 11691155) B11691155
theorem B49950269 : Blo 1368503 49950269 := bstep (se 3 (by rfl) ⟨9365675, by rfl⟩ : syracuseStep 49950269 = 18731351) B18731351
theorem B5197391 : Blo 1368503 5197391 := bstep (se 1 (by rfl) ⟨3898043, by rfl⟩ : syracuseStep 5197391 = 7796087) B7796087
theorem B5852857 : Blo 1368503 5852857 := bstep (se 2 (by rfl) ⟨2194821, by rfl⟩ : syracuseStep 5852857 = 4389643) B4389643
theorem B88846145 : Blo 1368503 88846145 := bstep (se 2 (by rfl) ⟨33317304, by rfl⟩ : syracuseStep 88846145 = 66634609) B66634609
theorem B12488519 : Blo 1368503 12488519 := bstep (se 1 (by rfl) ⟨9366389, by rfl⟩ : syracuseStep 12488519 = 18732779) B18732779
theorem B79007561 : Blo 1368503 79007561 := bstep (se 2 (by rfl) ⟨29627835, by rfl⟩ : syracuseStep 79007561 = 59255671) B59255671
theorem B24990029 : Blo 1368503 24990029 := bstep (se 3 (by rfl) ⟨4685630, by rfl⟩ : syracuseStep 24990029 = 9371261) B9371261
theorem B1733167 : Blo 1368503 1733167 := bstep (se 1 (by rfl) ⟨1299875, by rfl⟩ : syracuseStep 1733167 = 2599751) B2599751
theorem B2052815 : Blo 1368503 2052815 := bstep (se 1 (by rfl) ⟨1539611, by rfl⟩ : syracuseStep 2052815 = 3079223) B3079223
theorem B6091757 : Blo 1368503 6091757 := bstep (se 3 (by rfl) ⟨1142204, by rfl⟩ : syracuseStep 6091757 = 2284409) B2284409
theorem B29594621 : Blo 1368503 29594621 := bstep (se 3 (by rfl) ⟨5548991, by rfl⟩ : syracuseStep 29594621 = 11097983) B11097983
theorem B7500923 : Blo 1368503 7500923 := bstep (se 1 (by rfl) ⟨5625692, by rfl⟩ : syracuseStep 7500923 = 11251385) B11251385
theorem B30037337 : Blo 1368503 30037337 := bstep (se 2 (by rfl) ⟨11264001, by rfl⟩ : syracuseStep 30037337 = 22528003) B22528003
theorem B35583583 : Blo 1368503 35583583 := bstep (se 1 (by rfl) ⟨26687687, by rfl⟩ : syracuseStep 35583583 = 53375375) B53375375
theorem B44406467 : Blo 1368503 44406467 := bstep (se 1 (by rfl) ⟨33304850, by rfl⟩ : syracuseStep 44406467 = 66609701) B66609701
theorem B5199623 : Blo 1368503 5199623 := bstep (se 1 (by rfl) ⟨3899717, by rfl⟩ : syracuseStep 5199623 = 7799435) B7799435
theorem B2054111 : Blo 1368503 2054111 := bstep (se 1 (by rfl) ⟨1540583, by rfl⟩ : syracuseStep 2054111 = 3081167) B3081167
theorem B3512459 : Blo 1368503 3512459 := bstep (se 1 (by rfl) ⟨2634344, by rfl⟩ : syracuseStep 3512459 = 5268689) B5268689
theorem B3897679 : Blo 1368503 3897679 := bstep (se 1 (by rfl) ⟨2923259, by rfl⟩ : syracuseStep 3897679 = 5846519) B5846519
theorem B7805267 : Blo 1368503 7805267 := bstep (se 1 (by rfl) ⟨5853950, by rfl⟩ : syracuseStep 7805267 = 11707901) B11707901
theorem B2054747 : Blo 1368503 2054747 := bstep (se 1 (by rfl) ⟨1541060, by rfl⟩ : syracuseStep 2054747 = 3082121) B3082121
theorem B2054759 : Blo 1368503 2054759 := bstep (se 1 (by rfl) ⟨1541069, by rfl⟩ : syracuseStep 2054759 = 3082139) B3082139
theorem B2054891 : Blo 1368503 2054891 := bstep (se 1 (by rfl) ⟨1541168, by rfl⟩ : syracuseStep 2054891 = 3082337) B3082337
theorem B7797545 : Blo 1368503 7797545 := bstep (se 2 (by rfl) ⟨2924079, by rfl⟩ : syracuseStep 7797545 = 5848159) B5848159
theorem B3898169 : Blo 1368503 3898169 := bstep (se 2 (by rfl) ⟨1461813, by rfl⟩ : syracuseStep 3898169 = 2923627) B2923627
theorem B6929387 : Blo 1368503 6929387 := bstep (se 1 (by rfl) ⟨5197040, by rfl⟩ : syracuseStep 6929387 = 10394081) B10394081
theorem B3464329 : Blo 1368503 3464329 := bstep (se 2 (by rfl) ⟨1299123, by rfl⟩ : syracuseStep 3464329 = 2598247) B2598247
theorem B2309431 : Blo 1368503 2309431 := bstep (se 1 (by rfl) ⟨1732073, by rfl⟩ : syracuseStep 2309431 = 3464147) B3464147
theorem B2343007 : Blo 1368503 2343007 := bstep (se 1 (by rfl) ⟨1757255, by rfl⟩ : syracuseStep 2343007 = 3514511) B3514511
theorem B4620563 : Blo 1368503 4620563 := bstep (se 1 (by rfl) ⟨3465422, by rfl⟩ : syracuseStep 4620563 = 6930845) B6930845
theorem B3080609 : Blo 1368503 3080609 := bstep (se 2 (by rfl) ⟨1155228, by rfl⟩ : syracuseStep 3080609 = 2310457) B2310457
theorem B1368543 : Blo 1368503 1368543 := bstep (se 1 (by rfl) ⟨1026407, by rfl⟩ : syracuseStep 1368543 = 2052815) B2052815
theorem B5202569 : Blo 1368503 5202569 := bstep (se 2 (by rfl) ⟨1950963, by rfl⟩ : syracuseStep 5202569 = 3901927) B3901927
theorem B2310815 : Blo 1368503 2310815 := bstep (se 1 (by rfl) ⟨1733111, by rfl⟩ : syracuseStep 2310815 = 3466223) B3466223
theorem B2310889 : Blo 1368503 2310889 := bstep (se 2 (by rfl) ⟨866583, by rfl⟩ : syracuseStep 2310889 = 1733167) B1733167
theorem B1540903 : Blo 1368503 1540903 := bstep (se 1 (by rfl) ⟨1155677, by rfl⟩ : syracuseStep 1540903 = 2311355) B2311355
theorem B1541119 : Blo 1368503 1541119 := bstep (se 1 (by rfl) ⟨1155839, by rfl⟩ : syracuseStep 1541119 = 2311679) B2311679
theorem B3466415 : Blo 1368503 3466415 := bstep (se 1 (by rfl) ⟨2599811, by rfl⟩ : syracuseStep 3466415 = 5199623) B5199623
theorem B1369407 : Blo 1368503 1369407 := bstep (se 1 (by rfl) ⟨1027055, by rfl⟩ : syracuseStep 1369407 = 2054111) B2054111
theorem B1541479 : Blo 1368503 1541479 := bstep (se 1 (by rfl) ⟨1156109, by rfl⟩ : syracuseStep 1541479 = 2312219) B2312219
theorem B5203511 : Blo 1368503 5203511 := bstep (se 1 (by rfl) ⟨3902633, by rfl⟩ : syracuseStep 5203511 = 7805267) B7805267
theorem B1369831 : Blo 1368503 1369831 := bstep (se 1 (by rfl) ⟨1027373, by rfl⟩ : syracuseStep 1369831 = 2054747) B2054747
theorem B1369839 : Blo 1368503 1369839 := bstep (se 1 (by rfl) ⟨1027379, by rfl⟩ : syracuseStep 1369839 = 2054759) B2054759
theorem B1369927 : Blo 1368503 1369927 := bstep (se 1 (by rfl) ⟨1027445, by rfl⟩ : syracuseStep 1369927 = 2054891) B2054891
theorem B2598779 : Blo 1368503 2598779 := bstep (se 1 (by rfl) ⟨1949084, by rfl⟩ : syracuseStep 2598779 = 3898169) B3898169
theorem B59230763 : Blo 1368503 59230763 := bstep (se 1 (by rfl) ⟨44423072, by rfl⟩ : syracuseStep 59230763 = 88846145) B88846145
theorem B8325679 : Blo 1368503 8325679 := bstep (se 1 (by rfl) ⟨6244259, by rfl⟩ : syracuseStep 8325679 = 12488519) B12488519
theorem B6581351 : Blo 1368503 6581351 := bstep (se 1 (by rfl) ⟨4936013, by rfl⟩ : syracuseStep 6581351 = 9872027) B9872027
theorem B5196905 : Blo 1368503 5196905 := bstep (se 2 (by rfl) ⟨1948839, by rfl⟩ : syracuseStep 5196905 = 3897679) B3897679
theorem B19729747 : Blo 1368503 19729747 := bstep (se 1 (by rfl) ⟨14797310, by rfl⟩ : syracuseStep 19729747 = 29594621) B29594621
theorem B5000615 : Blo 1368503 5000615 := bstep (se 1 (by rfl) ⟨3750461, by rfl⟩ : syracuseStep 5000615 = 7500923) B7500923
theorem B2600495 : Blo 1368503 2600495 := bstep (se 1 (by rfl) ⟨1950371, by rfl⟩ : syracuseStep 2600495 = 3900743) B3900743
theorem B20024891 : Blo 1368503 20024891 := bstep (se 1 (by rfl) ⟨15018668, by rfl⟩ : syracuseStep 20024891 = 30037337) B30037337
theorem B10399427 : Blo 1368503 10399427 := bstep (se 1 (by rfl) ⟨7799570, by rfl⟩ : syracuseStep 10399427 = 15599141) B15599141
theorem B14815649 : Blo 1368503 14815649 := bstep (se 2 (by rfl) ⟨5555868, by rfl⟩ : syracuseStep 14815649 = 11111737) B11111737
theorem B5198363 : Blo 1368503 5198363 := bstep (se 1 (by rfl) ⟨3898772, by rfl⟩ : syracuseStep 5198363 = 7797545) B7797545
theorem B10392137 : Blo 1368503 10392137 := bstep (se 2 (by rfl) ⟨3897051, by rfl⟩ : syracuseStep 10392137 = 7794103) B7794103
theorem B47444777 : Blo 1368503 47444777 := bstep (se 2 (by rfl) ⟨17791791, by rfl⟩ : syracuseStep 47444777 = 35583583) B35583583
theorem B7803809 : Blo 1368503 7803809 := bstep (se 2 (by rfl) ⟨2926428, by rfl⟩ : syracuseStep 7803809 = 5852857) B5852857
theorem B52671707 : Blo 1368503 52671707 := bstep (se 1 (by rfl) ⟨39503780, by rfl⟩ : syracuseStep 52671707 = 79007561) B79007561
theorem B91231541 : Blo 1368503 91231541 := bstep (se 5 (by rfl) ⟨4276478, by rfl⟩ : syracuseStep 91231541 = 8552957) B8552957
theorem B16660019 : Blo 1368503 16660019 := bstep (se 1 (by rfl) ⟨12495014, by rfl⟩ : syracuseStep 16660019 = 24990029) B24990029
theorem B3954401 : Blo 1368503 3954401 := bstep (se 2 (by rfl) ⟨1482900, by rfl⟩ : syracuseStep 3954401 = 2965801) B2965801
theorem B4061171 : Blo 1368503 4061171 := bstep (se 1 (by rfl) ⟨3045878, by rfl⟩ : syracuseStep 4061171 = 6091757) B6091757
theorem B27039791 : Blo 1368503 27039791 := bstep (se 1 (by rfl) ⟨20279843, by rfl⟩ : syracuseStep 27039791 = 40559687) B40559687
theorem B2054255 : Blo 1368503 2054255 := bstep (se 1 (by rfl) ⟨1540691, by rfl⟩ : syracuseStep 2054255 = 3081383) B3081383
theorem B2054327 : Blo 1368503 2054327 := bstep (se 1 (by rfl) ⟨1540745, by rfl⟩ : syracuseStep 2054327 = 3081491) B3081491
theorem B6936839 : Blo 1368503 6936839 := bstep (se 1 (by rfl) ⟨5202629, by rfl⟩ : syracuseStep 6936839 = 10405259) B10405259
theorem B29604311 : Blo 1368503 29604311 := bstep (se 1 (by rfl) ⟨22203233, by rfl⟩ : syracuseStep 29604311 = 44406467) B44406467
theorem B35101349 : Blo 1368503 35101349 := bstep (se 4 (by rfl) ⟨3290751, by rfl⟩ : syracuseStep 35101349 = 6581503) B6581503
theorem B2341639 : Blo 1368503 2341639 := bstep (se 1 (by rfl) ⟨1756229, by rfl⟩ : syracuseStep 2341639 = 3512459) B3512459
theorem B4619105 : Blo 1368503 4619105 := bstep (se 2 (by rfl) ⟨1732164, by rfl⟩ : syracuseStep 4619105 = 3464329) B3464329
theorem B3079241 : Blo 1368503 3079241 := bstep (se 2 (by rfl) ⟨1154715, by rfl⟩ : syracuseStep 3079241 = 2309431) B2309431
theorem B2055263 : Blo 1368503 2055263 := bstep (se 1 (by rfl) ⟨1541447, by rfl⟩ : syracuseStep 2055263 = 3082895) B3082895
theorem B6937811 : Blo 1368503 6937811 := bstep (se 1 (by rfl) ⟨5203358, by rfl⟩ : syracuseStep 6937811 = 10406717) B10406717
theorem B4619591 : Blo 1368503 4619591 := bstep (se 1 (by rfl) ⟨3464693, by rfl⟩ : syracuseStep 4619591 = 6929387) B6929387
theorem B33300179 : Blo 1368503 33300179 := bstep (se 1 (by rfl) ⟨24975134, by rfl⟩ : syracuseStep 33300179 = 49950269) B49950269
theorem B3464927 : Blo 1368503 3464927 := bstep (se 1 (by rfl) ⟨2598695, by rfl⟩ : syracuseStep 3464927 = 5197391) B5197391
theorem B72106109 : Blo 1368503 72106109 := bstep (se 3 (by rfl) ⟨13519895, by rfl⟩ : syracuseStep 72106109 = 27039791) B27039791
theorem B3080375 : Blo 1368503 3080375 := bstep (se 1 (by rfl) ⟨2310281, by rfl⟩ : syracuseStep 3080375 = 4620563) B4620563
theorem B3465575 : Blo 1368503 3465575 := bstep (se 1 (by rfl) ⟨2599181, by rfl⟩ : syracuseStep 3465575 = 5198363) B5198363
theorem B1540543 : Blo 1368503 1540543 := bstep (se 1 (by rfl) ⟨1155407, by rfl⟩ : syracuseStep 1540543 = 2310815) B2310815
theorem B31629851 : Blo 1368503 31629851 := bstep (se 1 (by rfl) ⟨23722388, by rfl⟩ : syracuseStep 31629851 = 47444777) B47444777
theorem B5202539 : Blo 1368503 5202539 := bstep (se 1 (by rfl) ⟨3901904, by rfl⟩ : syracuseStep 5202539 = 7803809) B7803809
theorem B11100905 : Blo 1368503 11100905 := bstep (se 2 (by rfl) ⟨4162839, by rfl⟩ : syracuseStep 11100905 = 8325679) B8325679
theorem B2310943 : Blo 1368503 2310943 := bstep (se 1 (by rfl) ⟨1733207, by rfl⟩ : syracuseStep 2310943 = 3466415) B3466415
theorem B3081185 : Blo 1368503 3081185 := bstep (se 2 (by rfl) ⟨1155444, by rfl⟩ : syracuseStep 3081185 = 2310889) B2310889
theorem B1369503 : Blo 1368503 1369503 := bstep (se 1 (by rfl) ⟨1027127, by rfl⟩ : syracuseStep 1369503 = 2054255) B2054255
theorem B1369551 : Blo 1368503 1369551 := bstep (se 1 (by rfl) ⟨1027163, by rfl⟩ : syracuseStep 1369551 = 2054327) B2054327
theorem B44426717 : Blo 1368503 44426717 := bstep (se 3 (by rfl) ⟨8330009, by rfl⟩ : syracuseStep 44426717 = 16660019) B16660019
theorem B19736207 : Blo 1368503 19736207 := bstep (se 1 (by rfl) ⟨14802155, by rfl⟩ : syracuseStep 19736207 = 29604311) B29604311
theorem B39487175 : Blo 1368503 39487175 := bstep (se 1 (by rfl) ⟨29615381, by rfl⟩ : syracuseStep 39487175 = 59230763) B59230763
theorem B26306329 : Blo 1368503 26306329 := bstep (se 2 (by rfl) ⟨9864873, by rfl⟩ : syracuseStep 26306329 = 19729747) B19729747
theorem B1370175 : Blo 1368503 1370175 := bstep (se 1 (by rfl) ⟨1027631, by rfl⟩ : syracuseStep 1370175 = 2055263) B2055263
theorem B6932951 : Blo 1368503 6932951 := bstep (se 1 (by rfl) ⟨5199713, by rfl⟩ : syracuseStep 6932951 = 10399427) B10399427
theorem B3124009 : Blo 1368503 3124009 := bstep (se 2 (by rfl) ⟨1171503, by rfl⟩ : syracuseStep 3124009 = 2343007) B2343007
theorem B3468379 : Blo 1368503 3468379 := bstep (se 1 (by rfl) ⟨2601284, by rfl⟩ : syracuseStep 3468379 = 5202569) B5202569
theorem B35114471 : Blo 1368503 35114471 := bstep (se 1 (by rfl) ⟨26335853, by rfl⟩ : syracuseStep 35114471 = 52671707) B52671707
theorem B60821027 : Blo 1368503 60821027 := bstep (se 1 (by rfl) ⟨45615770, by rfl⟩ : syracuseStep 60821027 = 91231541) B91231541
theorem B3469007 : Blo 1368503 3469007 := bstep (se 1 (by rfl) ⟨2601755, by rfl⟩ : syracuseStep 3469007 = 5203511) B5203511
theorem B1732519 : Blo 1368503 1732519 := bstep (se 1 (by rfl) ⟨1299389, by rfl⟩ : syracuseStep 1732519 = 2598779) B2598779
theorem B2707447 : Blo 1368503 2707447 := bstep (se 1 (by rfl) ⟨2030585, by rfl⟩ : syracuseStep 2707447 = 4061171) B4061171
theorem B12488741 : Blo 1368503 12488741 := bstep (se 4 (by rfl) ⟨1170819, by rfl⟩ : syracuseStep 12488741 = 2341639) B2341639
theorem B4624559 : Blo 1368503 4624559 := bstep (se 1 (by rfl) ⟨3468419, by rfl⟩ : syracuseStep 4624559 = 6936839) B6936839
theorem B23400899 : Blo 1368503 23400899 := bstep (se 1 (by rfl) ⟨17550674, by rfl⟩ : syracuseStep 23400899 = 35101349) B35101349
theorem B2052827 : Blo 1368503 2052827 := bstep (se 1 (by rfl) ⟨1539620, by rfl⟩ : syracuseStep 2052827 = 3079241) B3079241
theorem B4387567 : Blo 1368503 4387567 := bstep (se 1 (by rfl) ⟨3290675, by rfl⟩ : syracuseStep 4387567 = 6581351) B6581351
theorem B4625207 : Blo 1368503 4625207 := bstep (se 1 (by rfl) ⟨3468905, by rfl⟩ : syracuseStep 4625207 = 6937811) B6937811
theorem B1733663 : Blo 1368503 1733663 := bstep (se 1 (by rfl) ⟨1300247, by rfl⟩ : syracuseStep 1733663 = 2600495) B2600495
theorem B13349927 : Blo 1368503 13349927 := bstep (se 1 (by rfl) ⟨10012445, by rfl⟩ : syracuseStep 13349927 = 20024891) B20024891
theorem B2053739 : Blo 1368503 2053739 := bstep (se 1 (by rfl) ⟨1540304, by rfl⟩ : syracuseStep 2053739 = 3080609) B3080609
theorem B6928091 : Blo 1368503 6928091 := bstep (se 1 (by rfl) ⟨5196068, by rfl⟩ : syracuseStep 6928091 = 10392137) B10392137
theorem B2054537 : Blo 1368503 2054537 := bstep (se 2 (by rfl) ⟨770451, by rfl⟩ : syracuseStep 2054537 = 1540903) B1540903
theorem B39508397 : Blo 1368503 39508397 := bstep (se 3 (by rfl) ⟨7407824, by rfl⟩ : syracuseStep 39508397 = 14815649) B14815649
theorem B2054825 : Blo 1368503 2054825 := bstep (se 2 (by rfl) ⟨770559, by rfl⟩ : syracuseStep 2054825 = 1541119) B1541119
theorem B2055305 : Blo 1368503 2055305 := bstep (se 2 (by rfl) ⟨770739, by rfl⟩ : syracuseStep 2055305 = 1541479) B1541479
theorem B3079403 : Blo 1368503 3079403 := bstep (se 1 (by rfl) ⟨2309552, by rfl⟩ : syracuseStep 3079403 = 4619105) B4619105
theorem B3464603 : Blo 1368503 3464603 := bstep (se 1 (by rfl) ⟨2598452, by rfl⟩ : syracuseStep 3464603 = 5196905) B5196905
theorem B3079727 : Blo 1368503 3079727 := bstep (se 1 (by rfl) ⟨2309795, by rfl⟩ : syracuseStep 3079727 = 4619591) B4619591
theorem B3333743 : Blo 1368503 3333743 := bstep (se 1 (by rfl) ⟨2500307, by rfl⟩ : syracuseStep 3333743 = 5000615) B5000615
theorem B42180277 : Blo 1368503 42180277 := bstep (se 5 (by rfl) ⟨1977200, by rfl⟩ : syracuseStep 42180277 = 3954401) B3954401
theorem B22200119 : Blo 1368503 22200119 := bstep (se 1 (by rfl) ⟨16650089, by rfl⟩ : syracuseStep 22200119 = 33300179) B33300179
theorem B2309951 : Blo 1368503 2309951 := bstep (se 1 (by rfl) ⟨1732463, by rfl⟩ : syracuseStep 2309951 = 3464927) B3464927
theorem B48070739 : Blo 1368503 48070739 := bstep (se 1 (by rfl) ⟨36053054, by rfl⟩ : syracuseStep 48070739 = 72106109) B72106109
theorem B2310383 : Blo 1368503 2310383 := bstep (se 1 (by rfl) ⟨1732787, by rfl⟩ : syracuseStep 2310383 = 3465575) B3465575
theorem B21086567 : Blo 1368503 21086567 := bstep (se 1 (by rfl) ⟨15814925, by rfl⟩ : syracuseStep 21086567 = 31629851) B31629851
theorem B1368551 : Blo 1368503 1368551 := bstep (se 1 (by rfl) ⟨1026413, by rfl⟩ : syracuseStep 1368551 = 2052827) B2052827
theorem B5850089 : Blo 1368503 5850089 := bstep (se 2 (by rfl) ⟨2193783, by rfl⟩ : syracuseStep 5850089 = 4387567) B4387567
theorem B3081257 : Blo 1368503 3081257 := bstep (se 2 (by rfl) ⟨1155471, by rfl⟩ : syracuseStep 3081257 = 2310943) B2310943
theorem B1369159 : Blo 1368503 1369159 := bstep (se 1 (by rfl) ⟨1026869, by rfl⟩ : syracuseStep 1369159 = 2053739) B2053739
theorem B13157471 : Blo 1368503 13157471 := bstep (se 1 (by rfl) ⟨9868103, by rfl⟩ : syracuseStep 13157471 = 19736207) B19736207
theorem B1369691 : Blo 1368503 1369691 := bstep (se 1 (by rfl) ⟨1027268, by rfl⟩ : syracuseStep 1369691 = 2054537) B2054537
theorem B26338931 : Blo 1368503 26338931 := bstep (se 1 (by rfl) ⟨19754198, by rfl⟩ : syracuseStep 26338931 = 39508397) B39508397
theorem B4621967 : Blo 1368503 4621967 := bstep (se 1 (by rfl) ⟨3466475, by rfl⟩ : syracuseStep 4621967 = 6932951) B6932951
theorem B1369883 : Blo 1368503 1369883 := bstep (se 1 (by rfl) ⟨1027412, by rfl⟩ : syracuseStep 1369883 = 2054825) B2054825
theorem B1370203 : Blo 1368503 1370203 := bstep (se 1 (by rfl) ⟨1027652, by rfl⟩ : syracuseStep 1370203 = 2055305) B2055305
theorem B56240369 : Blo 1368503 56240369 := bstep (se 2 (by rfl) ⟨21090138, by rfl⟩ : syracuseStep 56240369 = 42180277) B42180277
theorem B2222495 : Blo 1368503 2222495 := bstep (se 1 (by rfl) ⟨1666871, by rfl⟩ : syracuseStep 2222495 = 3333743) B3333743
theorem B2312671 : Blo 1368503 2312671 := bstep (se 1 (by rfl) ⟨1734503, by rfl⟩ : syracuseStep 2312671 = 3469007) B3469007
theorem B8325827 : Blo 1368503 8325827 := bstep (se 1 (by rfl) ⟨6244370, by rfl⟩ : syracuseStep 8325827 = 12488741) B12488741
theorem B4623101 : Blo 1368503 4623101 := bstep (se 3 (by rfl) ⟨866831, by rfl⟩ : syracuseStep 4623101 = 1733663) B1733663
theorem B3083039 : Blo 1368503 3083039 := bstep (se 1 (by rfl) ⟨2312279, by rfl⟩ : syracuseStep 3083039 = 4624559) B4624559
theorem B15600599 : Blo 1368503 15600599 := bstep (se 1 (by rfl) ⟨11700449, by rfl⟩ : syracuseStep 15600599 = 23400899) B23400899
theorem B3468359 : Blo 1368503 3468359 := bstep (se 1 (by rfl) ⟨2601269, by rfl⟩ : syracuseStep 3468359 = 5202539) B5202539
theorem B7400603 : Blo 1368503 7400603 := bstep (se 1 (by rfl) ⟨5550452, by rfl⟩ : syracuseStep 7400603 = 11100905) B11100905
theorem B3083471 : Blo 1368503 3083471 := bstep (se 1 (by rfl) ⟨2312603, by rfl⟩ : syracuseStep 3083471 = 4625207) B4625207
theorem B8899951 : Blo 1368503 8899951 := bstep (se 1 (by rfl) ⟨6674963, by rfl⟩ : syracuseStep 8899951 = 13349927) B13349927
theorem B29617811 : Blo 1368503 29617811 := bstep (se 1 (by rfl) ⟨22213358, by rfl⟩ : syracuseStep 29617811 = 44426717) B44426717
theorem B4165345 : Blo 1368503 4165345 := bstep (se 2 (by rfl) ⟨1562004, by rfl⟩ : syracuseStep 4165345 = 3124009) B3124009
theorem B26324783 : Blo 1368503 26324783 := bstep (se 1 (by rfl) ⟨19743587, by rfl⟩ : syracuseStep 26324783 = 39487175) B39487175
theorem B4624505 : Blo 1368503 4624505 := bstep (se 2 (by rfl) ⟨1734189, by rfl⟩ : syracuseStep 4624505 = 3468379) B3468379
theorem B2052935 : Blo 1368503 2052935 := bstep (se 1 (by rfl) ⟨1539701, by rfl⟩ : syracuseStep 2052935 = 3079403) B3079403
theorem B23409647 : Blo 1368503 23409647 := bstep (se 1 (by rfl) ⟨17557235, by rfl⟩ : syracuseStep 23409647 = 35114471) B35114471
theorem B40547351 : Blo 1368503 40547351 := bstep (se 1 (by rfl) ⟨30410513, by rfl⟩ : syracuseStep 40547351 = 60821027) B60821027
theorem B2053151 : Blo 1368503 2053151 := bstep (se 1 (by rfl) ⟨1539863, by rfl⟩ : syracuseStep 2053151 = 3079727) B3079727
theorem B35075105 : Blo 1368503 35075105 := bstep (se 2 (by rfl) ⟨13153164, by rfl⟩ : syracuseStep 35075105 = 26306329) B26306329
theorem B14800079 : Blo 1368503 14800079 := bstep (se 1 (by rfl) ⟨11100059, by rfl⟩ : syracuseStep 14800079 = 22200119) B22200119
theorem B3609929 : Blo 1368503 3609929 := bstep (se 2 (by rfl) ⟨1353723, by rfl⟩ : syracuseStep 3609929 = 2707447) B2707447
theorem B2053583 : Blo 1368503 2053583 := bstep (se 1 (by rfl) ⟨1540187, by rfl⟩ : syracuseStep 2053583 = 3080375) B3080375
theorem B2054057 : Blo 1368503 2054057 := bstep (se 2 (by rfl) ⟨770271, by rfl⟩ : syracuseStep 2054057 = 1540543) B1540543
theorem B2054123 : Blo 1368503 2054123 := bstep (se 1 (by rfl) ⟨1540592, by rfl⟩ : syracuseStep 2054123 = 3081185) B3081185
theorem B4618727 : Blo 1368503 4618727 := bstep (se 1 (by rfl) ⟨3464045, by rfl⟩ : syracuseStep 4618727 = 6928091) B6928091
theorem B2309735 : Blo 1368503 2309735 := bstep (se 1 (by rfl) ⟨1732301, by rfl⟩ : syracuseStep 2309735 = 3464603) B3464603
theorem B1539967 : Blo 1368503 1539967 := bstep (se 1 (by rfl) ⟨1154975, by rfl⟩ : syracuseStep 1539967 = 2309951) B2309951
theorem B2310025 : Blo 1368503 2310025 := bstep (se 2 (by rfl) ⟨866259, by rfl⟩ : syracuseStep 2310025 = 1732519) B1732519
theorem B32047159 : Blo 1368503 32047159 := bstep (se 1 (by rfl) ⟨24035369, by rfl⟩ : syracuseStep 32047159 = 48070739) B48070739
theorem B1540255 : Blo 1368503 1540255 := bstep (se 1 (by rfl) ⟨1155191, by rfl⟩ : syracuseStep 1540255 = 2310383) B2310383
theorem B14057711 : Blo 1368503 14057711 := bstep (se 1 (by rfl) ⟨10543283, by rfl⟩ : syracuseStep 14057711 = 21086567) B21086567
theorem B19734941 : Blo 1368503 19734941 := bstep (se 3 (by rfl) ⟨3700301, by rfl⟩ : syracuseStep 19734941 = 7400603) B7400603
theorem B1368623 : Blo 1368503 1368623 := bstep (se 1 (by rfl) ⟨1026467, by rfl⟩ : syracuseStep 1368623 = 2052935) B2052935
theorem B3900059 : Blo 1368503 3900059 := bstep (se 1 (by rfl) ⟨2925044, by rfl⟩ : syracuseStep 3900059 = 5850089) B5850089
theorem B15606431 : Blo 1368503 15606431 := bstep (se 1 (by rfl) ⟨11704823, by rfl⟩ : syracuseStep 15606431 = 23409647) B23409647
theorem B1368767 : Blo 1368503 1368767 := bstep (se 1 (by rfl) ⟨1026575, by rfl⟩ : syracuseStep 1368767 = 2053151) B2053151
theorem B1369055 : Blo 1368503 1369055 := bstep (se 1 (by rfl) ⟨1026791, by rfl⟩ : syracuseStep 1369055 = 2053583) B2053583
theorem B3081311 : Blo 1368503 3081311 := bstep (se 1 (by rfl) ⟨2310983, by rfl⟩ : syracuseStep 3081311 = 4621967) B4621967
theorem B1369371 : Blo 1368503 1369371 := bstep (se 1 (by rfl) ⟨1027028, by rfl⟩ : syracuseStep 1369371 = 2054057) B2054057
theorem B1369415 : Blo 1368503 1369415 := bstep (se 1 (by rfl) ⟨1027061, by rfl⟩ : syracuseStep 1369415 = 2054123) B2054123
theorem B3082067 : Blo 1368503 3082067 := bstep (se 1 (by rfl) ⟨2311550, by rfl⟩ : syracuseStep 3082067 = 4623101) B4623101
theorem B2312239 : Blo 1368503 2312239 := bstep (se 1 (by rfl) ⟨1734179, by rfl⟩ : syracuseStep 2312239 = 3468359) B3468359
theorem B19745207 : Blo 1368503 19745207 := bstep (se 1 (by rfl) ⟨14808905, by rfl⟩ : syracuseStep 19745207 = 29617811) B29617811
theorem B17549855 : Blo 1368503 17549855 := bstep (se 1 (by rfl) ⟨13162391, by rfl⟩ : syracuseStep 17549855 = 26324783) B26324783
theorem B3083003 : Blo 1368503 3083003 := bstep (se 1 (by rfl) ⟨2312252, by rfl⟩ : syracuseStep 3083003 = 4624505) B4624505
theorem B3083561 : Blo 1368503 3083561 := bstep (se 2 (by rfl) ⟨1156335, by rfl⟩ : syracuseStep 3083561 = 2312671) B2312671
theorem B23383403 : Blo 1368503 23383403 := bstep (se 1 (by rfl) ⟨17537552, by rfl⟩ : syracuseStep 23383403 = 35075105) B35075105
theorem B9866719 : Blo 1368503 9866719 := bstep (se 1 (by rfl) ⟨7400039, by rfl⟩ : syracuseStep 9866719 = 14800079) B14800079
theorem B17559287 : Blo 1368503 17559287 := bstep (se 1 (by rfl) ⟨13169465, by rfl⟩ : syracuseStep 17559287 = 26338931) B26338931
theorem B5550551 : Blo 1368503 5550551 := bstep (se 1 (by rfl) ⟨4162913, by rfl⟩ : syracuseStep 5550551 = 8325827) B8325827
theorem B11866601 : Blo 1368503 11866601 := bstep (se 2 (by rfl) ⟨4449975, by rfl⟩ : syracuseStep 11866601 = 8899951) B8899951
theorem B10400399 : Blo 1368503 10400399 := bstep (se 1 (by rfl) ⟨7800299, by rfl⟩ : syracuseStep 10400399 = 15600599) B15600599
theorem B2053289 : Blo 1368503 2053289 := bstep (se 2 (by rfl) ⟨769983, by rfl⟩ : syracuseStep 2053289 = 1539967) B1539967
theorem B27031567 : Blo 1368503 27031567 := bstep (se 1 (by rfl) ⟨20273675, by rfl⟩ : syracuseStep 27031567 = 40547351) B40547351
theorem B2054171 : Blo 1368503 2054171 := bstep (se 1 (by rfl) ⟨1540628, by rfl⟩ : syracuseStep 2054171 = 3081257) B3081257
theorem B8771647 : Blo 1368503 8771647 := bstep (se 1 (by rfl) ⟨6578735, by rfl⟩ : syracuseStep 8771647 = 13157471) B13157471
theorem B2406619 : Blo 1368503 2406619 := bstep (se 1 (by rfl) ⟨1804964, by rfl⟩ : syracuseStep 2406619 = 3609929) B3609929
theorem B37493579 : Blo 1368503 37493579 := bstep (se 1 (by rfl) ⟨28120184, by rfl⟩ : syracuseStep 37493579 = 56240369) B56240369
theorem B1481663 : Blo 1368503 1481663 := bstep (se 1 (by rfl) ⟨1111247, by rfl⟩ : syracuseStep 1481663 = 2222495) B2222495
theorem B3079151 : Blo 1368503 3079151 := bstep (se 1 (by rfl) ⟨2309363, by rfl⟩ : syracuseStep 3079151 = 4618727) B4618727
theorem B2055359 : Blo 1368503 2055359 := bstep (se 1 (by rfl) ⟨1541519, by rfl⟩ : syracuseStep 2055359 = 3083039) B3083039
theorem B2055647 : Blo 1368503 2055647 := bstep (se 1 (by rfl) ⟨1541735, by rfl⟩ : syracuseStep 2055647 = 3083471) B3083471
theorem B5553793 : Blo 1368503 5553793 := bstep (se 2 (by rfl) ⟨2082672, by rfl⟩ : syracuseStep 5553793 = 4165345) B4165345
theorem B1539823 : Blo 1368503 1539823 := bstep (se 1 (by rfl) ⟨1154867, by rfl⟩ : syracuseStep 1539823 = 2309735) B2309735
theorem B3080033 : Blo 1368503 3080033 := bstep (se 2 (by rfl) ⟨1155012, by rfl⟩ : syracuseStep 3080033 = 2310025) B2310025
theorem B42729545 : Blo 1368503 42729545 := bstep (se 2 (by rfl) ⟨16023579, by rfl⟩ : syracuseStep 42729545 = 32047159) B32047159
theorem B9371807 : Blo 1368503 9371807 := bstep (se 1 (by rfl) ⟨7028855, by rfl⟩ : syracuseStep 9371807 = 14057711) B14057711
theorem B13156627 : Blo 1368503 13156627 := bstep (se 1 (by rfl) ⟨9867470, by rfl⟩ : syracuseStep 13156627 = 19734941) B19734941
theorem B10404287 : Blo 1368503 10404287 := bstep (se 1 (by rfl) ⟨7803215, by rfl⟩ : syracuseStep 10404287 = 15606431) B15606431
theorem B1368859 : Blo 1368503 1368859 := bstep (se 1 (by rfl) ⟨1026644, by rfl⟩ : syracuseStep 1368859 = 2053289) B2053289
theorem B1369447 : Blo 1368503 1369447 := bstep (se 1 (by rfl) ⟨1027085, by rfl⟩ : syracuseStep 1369447 = 2054171) B2054171
theorem B11699903 : Blo 1368503 11699903 := bstep (se 1 (by rfl) ⟨8774927, by rfl⟩ : syracuseStep 11699903 = 17549855) B17549855
theorem B24995719 : Blo 1368503 24995719 := bstep (se 1 (by rfl) ⟨18746789, by rfl⟩ : syracuseStep 24995719 = 37493579) B37493579
theorem B1370239 : Blo 1368503 1370239 := bstep (se 1 (by rfl) ⟨1027679, by rfl⟩ : syracuseStep 1370239 = 2055359) B2055359
theorem B1370431 : Blo 1368503 1370431 := bstep (se 1 (by rfl) ⟨1027823, by rfl⟩ : syracuseStep 1370431 = 2055647) B2055647
theorem B3951101 : Blo 1368503 3951101 := bstep (se 3 (by rfl) ⟨740831, by rfl⟩ : syracuseStep 3951101 = 1481663) B1481663
theorem B3082985 : Blo 1368503 3082985 := bstep (se 2 (by rfl) ⟨1156119, by rfl⟩ : syracuseStep 3082985 = 2312239) B2312239
theorem B6933599 : Blo 1368503 6933599 := bstep (se 1 (by rfl) ⟨5200199, by rfl⟩ : syracuseStep 6933599 = 10400399) B10400399
theorem B2600039 : Blo 1368503 2600039 := bstep (se 1 (by rfl) ⟨1950029, by rfl⟩ : syracuseStep 2600039 = 3900059) B3900059
theorem B2052767 : Blo 1368503 2052767 := bstep (se 1 (by rfl) ⟨1539575, by rfl⟩ : syracuseStep 2052767 = 3079151) B3079151
theorem B2053097 : Blo 1368503 2053097 := bstep (se 2 (by rfl) ⟨769911, by rfl⟩ : syracuseStep 2053097 = 1539823) B1539823
theorem B2053355 : Blo 1368503 2053355 := bstep (se 1 (by rfl) ⟨1540016, by rfl⟩ : syracuseStep 2053355 = 3080033) B3080033
theorem B36042089 : Blo 1368503 36042089 := bstep (se 2 (by rfl) ⟨13515783, by rfl⟩ : syracuseStep 36042089 = 27031567) B27031567
theorem B11695529 : Blo 1368503 11695529 := bstep (se 2 (by rfl) ⟨4385823, by rfl⟩ : syracuseStep 11695529 = 8771647) B8771647
theorem B2053673 : Blo 1368503 2053673 := bstep (se 2 (by rfl) ⟨770127, by rfl⟩ : syracuseStep 2053673 = 1540255) B1540255
theorem B3208825 : Blo 1368503 3208825 := bstep (se 2 (by rfl) ⟨1203309, by rfl⟩ : syracuseStep 3208825 = 2406619) B2406619
theorem B3700367 : Blo 1368503 3700367 := bstep (se 1 (by rfl) ⟨2775275, by rfl⟩ : syracuseStep 3700367 = 5550551) B5550551
theorem B7911067 : Blo 1368503 7911067 := bstep (se 1 (by rfl) ⟨5933300, by rfl⟩ : syracuseStep 7911067 = 11866601) B11866601
theorem B2054207 : Blo 1368503 2054207 := bstep (se 1 (by rfl) ⟨1540655, by rfl⟩ : syracuseStep 2054207 = 3081311) B3081311
theorem B2054711 : Blo 1368503 2054711 := bstep (se 1 (by rfl) ⟨1541033, by rfl⟩ : syracuseStep 2054711 = 3082067) B3082067
theorem B13163471 : Blo 1368503 13163471 := bstep (se 1 (by rfl) ⟨9872603, by rfl⟩ : syracuseStep 13163471 = 19745207) B19745207
theorem B2055335 : Blo 1368503 2055335 := bstep (se 1 (by rfl) ⟨1541501, by rfl⟩ : syracuseStep 2055335 = 3083003) B3083003
theorem B13155625 : Blo 1368503 13155625 := bstep (se 2 (by rfl) ⟨4933359, by rfl⟩ : syracuseStep 13155625 = 9866719) B9866719
theorem B7405057 : Blo 1368503 7405057 := bstep (se 2 (by rfl) ⟨2776896, by rfl⟩ : syracuseStep 7405057 = 5553793) B5553793
theorem B2055707 : Blo 1368503 2055707 := bstep (se 1 (by rfl) ⟨1541780, by rfl⟩ : syracuseStep 2055707 = 3083561) B3083561
theorem B15588935 : Blo 1368503 15588935 := bstep (se 1 (by rfl) ⟨11691701, by rfl⟩ : syracuseStep 15588935 = 23383403) B23383403
theorem B11706191 : Blo 1368503 11706191 := bstep (se 1 (by rfl) ⟨8779643, by rfl⟩ : syracuseStep 11706191 = 17559287) B17559287
theorem B1368511 : Blo 1368503 1368511 := bstep (se 1 (by rfl) ⟨1026383, by rfl⟩ : syracuseStep 1368511 = 2052767) B2052767
theorem B1368731 : Blo 1368503 1368731 := bstep (se 1 (by rfl) ⟨1026548, by rfl⟩ : syracuseStep 1368731 = 2053097) B2053097
theorem B1368903 : Blo 1368503 1368903 := bstep (se 1 (by rfl) ⟨1026677, by rfl⟩ : syracuseStep 1368903 = 2053355) B2053355
theorem B1369115 : Blo 1368503 1369115 := bstep (se 1 (by rfl) ⟨1026836, by rfl⟩ : syracuseStep 1369115 = 2053673) B2053673
theorem B2466911 : Blo 1368503 2466911 := bstep (se 1 (by rfl) ⟨1850183, by rfl⟩ : syracuseStep 2466911 = 3700367) B3700367
theorem B7799935 : Blo 1368503 7799935 := bstep (se 1 (by rfl) ⟨5849951, by rfl⟩ : syracuseStep 7799935 = 11699903) B11699903
theorem B1369471 : Blo 1368503 1369471 := bstep (se 1 (by rfl) ⟨1027103, by rfl⟩ : syracuseStep 1369471 = 2054207) B2054207
theorem B1369807 : Blo 1368503 1369807 := bstep (se 1 (by rfl) ⟨1027355, by rfl⟩ : syracuseStep 1369807 = 2054711) B2054711
theorem B17540833 : Blo 1368503 17540833 := bstep (se 2 (by rfl) ⟨6577812, by rfl⟩ : syracuseStep 17540833 = 13155625) B13155625
theorem B8775647 : Blo 1368503 8775647 := bstep (se 1 (by rfl) ⟨6581735, by rfl⟩ : syracuseStep 8775647 = 13163471) B13163471
theorem B9873409 : Blo 1368503 9873409 := bstep (se 2 (by rfl) ⟨3702528, by rfl⟩ : syracuseStep 9873409 = 7405057) B7405057
theorem B4622399 : Blo 1368503 4622399 := bstep (se 1 (by rfl) ⟨3466799, by rfl⟩ : syracuseStep 4622399 = 6933599) B6933599
theorem B1370223 : Blo 1368503 1370223 := bstep (se 1 (by rfl) ⟨1027667, by rfl⟩ : syracuseStep 1370223 = 2055335) B2055335
theorem B4278433 : Blo 1368503 4278433 := bstep (se 2 (by rfl) ⟨1604412, by rfl⟩ : syracuseStep 4278433 = 3208825) B3208825
theorem B1370471 : Blo 1368503 1370471 := bstep (se 1 (by rfl) ⟨1027853, by rfl⟩ : syracuseStep 1370471 = 2055707) B2055707
theorem B33327625 : Blo 1368503 33327625 := bstep (se 2 (by rfl) ⟨12497859, by rfl⟩ : syracuseStep 33327625 = 24995719) B24995719
theorem B28486363 : Blo 1368503 28486363 := bstep (se 1 (by rfl) ⟨21364772, by rfl⟩ : syracuseStep 28486363 = 42729545) B42729545
theorem B6933437 : Blo 1368503 6933437 := bstep (se 3 (by rfl) ⟨1300019, by rfl⟩ : syracuseStep 6933437 = 2600039) B2600039
theorem B17542169 : Blo 1368503 17542169 := bstep (se 2 (by rfl) ⟨6578313, by rfl⟩ : syracuseStep 17542169 = 13156627) B13156627
theorem B2634067 : Blo 1368503 2634067 := bstep (se 1 (by rfl) ⟨1975550, by rfl⟩ : syracuseStep 2634067 = 3951101) B3951101
theorem B10548089 : Blo 1368503 10548089 := bstep (se 2 (by rfl) ⟨3955533, by rfl⟩ : syracuseStep 10548089 = 7911067) B7911067
theorem B10392623 : Blo 1368503 10392623 := bstep (se 1 (by rfl) ⟨7794467, by rfl⟩ : syracuseStep 10392623 = 15588935) B15588935
theorem B7804127 : Blo 1368503 7804127 := bstep (se 1 (by rfl) ⟨5853095, by rfl⟩ : syracuseStep 7804127 = 11706191) B11706191
theorem B6247871 : Blo 1368503 6247871 := bstep (se 1 (by rfl) ⟨4685903, by rfl⟩ : syracuseStep 6247871 = 9371807) B9371807
theorem B6936191 : Blo 1368503 6936191 := bstep (se 1 (by rfl) ⟨5202143, by rfl⟩ : syracuseStep 6936191 = 10404287) B10404287
theorem B7797019 : Blo 1368503 7797019 := bstep (se 1 (by rfl) ⟨5847764, by rfl⟩ : syracuseStep 7797019 = 11695529) B11695529
theorem B384448949 : Blo 1368503 384448949 := bstep (se 5 (by rfl) ⟨18021044, by rfl⟩ : syracuseStep 384448949 = 36042089) B36042089
theorem B2055323 : Blo 1368503 2055323 := bstep (se 1 (by rfl) ⟨1541492, by rfl⟩ : syracuseStep 2055323 = 3082985) B3082985
theorem B13164545 : Blo 1368503 13164545 := bstep (se 2 (by rfl) ⟨4936704, by rfl⟩ : syracuseStep 13164545 = 9873409) B9873409
theorem B10396025 : Blo 1368503 10396025 := bstep (se 2 (by rfl) ⟨3898509, by rfl⟩ : syracuseStep 10396025 = 7797019) B7797019
theorem B5202751 : Blo 1368503 5202751 := bstep (se 1 (by rfl) ⟨3902063, by rfl⟩ : syracuseStep 5202751 = 7804127) B7804127
theorem B5850431 : Blo 1368503 5850431 := bstep (se 1 (by rfl) ⟨4387823, by rfl⟩ : syracuseStep 5850431 = 8775647) B8775647
theorem B3081599 : Blo 1368503 3081599 := bstep (se 1 (by rfl) ⟨2311199, by rfl⟩ : syracuseStep 3081599 = 4622399) B4622399
theorem B4622291 : Blo 1368503 4622291 := bstep (se 1 (by rfl) ⟨3466718, by rfl⟩ : syracuseStep 4622291 = 6933437) B6933437
theorem B1370215 : Blo 1368503 1370215 := bstep (se 1 (by rfl) ⟨1027661, by rfl⟩ : syracuseStep 1370215 = 2055323) B2055323
theorem B5704577 : Blo 1368503 5704577 := bstep (se 2 (by rfl) ⟨2139216, by rfl⟩ : syracuseStep 5704577 = 4278433) B4278433
theorem B7032059 : Blo 1368503 7032059 := bstep (se 1 (by rfl) ⟨5274044, by rfl⟩ : syracuseStep 7032059 = 10548089) B10548089
theorem B44436833 : Blo 1368503 44436833 := bstep (se 2 (by rfl) ⟨16663812, by rfl⟩ : syracuseStep 44436833 = 33327625) B33327625
theorem B37981817 : Blo 1368503 37981817 := bstep (se 2 (by rfl) ⟨14243181, by rfl⟩ : syracuseStep 37981817 = 28486363) B28486363
theorem B4165247 : Blo 1368503 4165247 := bstep (se 1 (by rfl) ⟨3123935, by rfl⟩ : syracuseStep 4165247 = 6247871) B6247871
theorem B4624127 : Blo 1368503 4624127 := bstep (se 1 (by rfl) ⟨3468095, by rfl⟩ : syracuseStep 4624127 = 6936191) B6936191
theorem B10399913 : Blo 1368503 10399913 := bstep (se 2 (by rfl) ⟨3899967, by rfl⟩ : syracuseStep 10399913 = 7799935) B7799935
theorem B256299299 : Blo 1368503 256299299 := bstep (se 1 (by rfl) ⟨192224474, by rfl⟩ : syracuseStep 256299299 = 384448949) B384448949
theorem B11694779 : Blo 1368503 11694779 := bstep (se 1 (by rfl) ⟨8771084, by rfl⟩ : syracuseStep 11694779 = 17542169) B17542169
theorem B3512089 : Blo 1368503 3512089 := bstep (se 2 (by rfl) ⟨1317033, by rfl⟩ : syracuseStep 3512089 = 2634067) B2634067
theorem B6928415 : Blo 1368503 6928415 := bstep (se 1 (by rfl) ⟨5196311, by rfl⟩ : syracuseStep 6928415 = 10392623) B10392623
theorem B1644607 : Blo 1368503 1644607 := bstep (se 1 (by rfl) ⟨1233455, by rfl⟩ : syracuseStep 1644607 = 2466911) B2466911
theorem B23387777 : Blo 1368503 23387777 := bstep (se 2 (by rfl) ⟨8770416, by rfl⟩ : syracuseStep 23387777 = 17540833) B17540833
theorem B6930683 : Blo 1368503 6930683 := bstep (se 1 (by rfl) ⟨5198012, by rfl⟩ : syracuseStep 6930683 = 10396025) B10396025
theorem B3900287 : Blo 1368503 3900287 := bstep (se 1 (by rfl) ⟨2925215, by rfl⟩ : syracuseStep 3900287 = 5850431) B5850431
theorem B3081527 : Blo 1368503 3081527 := bstep (se 1 (by rfl) ⟨2311145, by rfl⟩ : syracuseStep 3081527 = 4622291) B4622291
theorem B3803051 : Blo 1368503 3803051 := bstep (se 1 (by rfl) ⟨2852288, by rfl⟩ : syracuseStep 3803051 = 5704577) B5704577
theorem B4688039 : Blo 1368503 4688039 := bstep (se 1 (by rfl) ⟨3516029, by rfl⟩ : syracuseStep 4688039 = 7032059) B7032059
theorem B29624555 : Blo 1368503 29624555 := bstep (se 1 (by rfl) ⟨22218416, by rfl⟩ : syracuseStep 29624555 = 44436833) B44436833
theorem B15591851 : Blo 1368503 15591851 := bstep (se 1 (by rfl) ⟨11693888, by rfl⟩ : syracuseStep 15591851 = 23387777) B23387777
theorem B3082751 : Blo 1368503 3082751 := bstep (se 1 (by rfl) ⟨2312063, by rfl⟩ : syracuseStep 3082751 = 4624127) B4624127
theorem B8776363 : Blo 1368503 8776363 := bstep (se 1 (by rfl) ⟨6582272, by rfl⟩ : syracuseStep 8776363 = 13164545) B13164545
theorem B6933275 : Blo 1368503 6933275 := bstep (se 1 (by rfl) ⟨5199956, by rfl⟩ : syracuseStep 6933275 = 10399913) B10399913
theorem B4682785 : Blo 1368503 4682785 := bstep (se 2 (by rfl) ⟨1756044, by rfl⟩ : syracuseStep 4682785 = 3512089) B3512089
theorem B170866199 : Blo 1368503 170866199 := bstep (se 1 (by rfl) ⟨128149649, by rfl⟩ : syracuseStep 170866199 = 256299299) B256299299
theorem B8771237 : Blo 1368503 8771237 := bstep (se 4 (by rfl) ⟨822303, by rfl⟩ : syracuseStep 8771237 = 1644607) B1644607
theorem B7796519 : Blo 1368503 7796519 := bstep (se 1 (by rfl) ⟨5847389, by rfl⟩ : syracuseStep 7796519 = 11694779) B11694779
theorem B2054399 : Blo 1368503 2054399 := bstep (se 1 (by rfl) ⟨1540799, by rfl⟩ : syracuseStep 2054399 = 3081599) B3081599
theorem B6937001 : Blo 1368503 6937001 := bstep (se 2 (by rfl) ⟨2601375, by rfl⟩ : syracuseStep 6937001 = 5202751) B5202751
theorem B4618943 : Blo 1368503 4618943 := bstep (se 1 (by rfl) ⟨3464207, by rfl⟩ : syracuseStep 4618943 = 6928415) B6928415
theorem B11107325 : Blo 1368503 11107325 := bstep (se 3 (by rfl) ⟨2082623, by rfl⟩ : syracuseStep 11107325 = 4165247) B4165247
theorem B25321211 : Blo 1368503 25321211 := bstep (se 1 (by rfl) ⟨18990908, by rfl⟩ : syracuseStep 25321211 = 37981817) B37981817
theorem B4620455 : Blo 1368503 4620455 := bstep (se 1 (by rfl) ⟨3465341, by rfl⟩ : syracuseStep 4620455 = 6930683) B6930683
theorem B113910799 : Blo 1368503 113910799 := bstep (se 1 (by rfl) ⟨85433099, by rfl⟩ : syracuseStep 113910799 = 170866199) B170866199
theorem B6243713 : Blo 1368503 6243713 := bstep (se 2 (by rfl) ⟨2341392, by rfl⟩ : syracuseStep 6243713 = 4682785) B4682785
theorem B1369599 : Blo 1368503 1369599 := bstep (se 1 (by rfl) ⟨1027199, by rfl⟩ : syracuseStep 1369599 = 2054399) B2054399
theorem B4622183 : Blo 1368503 4622183 := bstep (se 1 (by rfl) ⟨3466637, by rfl⟩ : syracuseStep 4622183 = 6933275) B6933275
theorem B2600191 : Blo 1368503 2600191 := bstep (se 1 (by rfl) ⟨1950143, by rfl⟩ : syracuseStep 2600191 = 3900287) B3900287
theorem B11701817 : Blo 1368503 11701817 := bstep (se 2 (by rfl) ⟨4388181, by rfl⟩ : syracuseStep 11701817 = 8776363) B8776363
theorem B5197679 : Blo 1368503 5197679 := bstep (se 1 (by rfl) ⟨3898259, by rfl⟩ : syracuseStep 5197679 = 7796519) B7796519
theorem B3125359 : Blo 1368503 3125359 := bstep (se 1 (by rfl) ⟨2344019, by rfl⟩ : syracuseStep 3125359 = 4688039) B4688039
theorem B4624667 : Blo 1368503 4624667 := bstep (se 1 (by rfl) ⟨3468500, by rfl⟩ : syracuseStep 4624667 = 6937001) B6937001
theorem B16880807 : Blo 1368503 16880807 := bstep (se 1 (by rfl) ⟨12660605, by rfl⟩ : syracuseStep 16880807 = 25321211) B25321211
theorem B29619533 : Blo 1368503 29619533 := bstep (se 3 (by rfl) ⟨5553662, by rfl⟩ : syracuseStep 29619533 = 11107325) B11107325
theorem B2054351 : Blo 1368503 2054351 := bstep (se 1 (by rfl) ⟨1540763, by rfl⟩ : syracuseStep 2054351 = 3081527) B3081527
theorem B5847491 : Blo 1368503 5847491 := bstep (se 1 (by rfl) ⟨4385618, by rfl⟩ : syracuseStep 5847491 = 8771237) B8771237
theorem B19749703 : Blo 1368503 19749703 := bstep (se 1 (by rfl) ⟨14812277, by rfl⟩ : syracuseStep 19749703 = 29624555) B29624555
theorem B10394567 : Blo 1368503 10394567 := bstep (se 1 (by rfl) ⟨7795925, by rfl⟩ : syracuseStep 10394567 = 15591851) B15591851
theorem B2055167 : Blo 1368503 2055167 := bstep (se 1 (by rfl) ⟨1541375, by rfl⟩ : syracuseStep 2055167 = 3082751) B3082751
theorem B3079295 : Blo 1368503 3079295 := bstep (se 1 (by rfl) ⟨2309471, by rfl⟩ : syracuseStep 3079295 = 4618943) B4618943
theorem B10141469 : Blo 1368503 10141469 := bstep (se 3 (by rfl) ⟨1901525, by rfl⟩ : syracuseStep 10141469 = 3803051) B3803051
theorem B3080303 : Blo 1368503 3080303 := bstep (se 1 (by rfl) ⟨2310227, by rfl⟩ : syracuseStep 3080303 = 4620455) B4620455
theorem B4162475 : Blo 1368503 4162475 := bstep (se 1 (by rfl) ⟨3121856, by rfl⟩ : syracuseStep 4162475 = 6243713) B6243713
theorem B3081455 : Blo 1368503 3081455 := bstep (se 1 (by rfl) ⟨2311091, by rfl⟩ : syracuseStep 3081455 = 4622183) B4622183
theorem B151881065 : Blo 1368503 151881065 := bstep (se 2 (by rfl) ⟨56955399, by rfl⟩ : syracuseStep 151881065 = 113910799) B113910799
theorem B1369567 : Blo 1368503 1369567 := bstep (se 1 (by rfl) ⟨1027175, by rfl⟩ : syracuseStep 1369567 = 2054351) B2054351
theorem B3466921 : Blo 1368503 3466921 := bstep (se 2 (by rfl) ⟨1300095, by rfl⟩ : syracuseStep 3466921 = 2600191) B2600191
theorem B1370111 : Blo 1368503 1370111 := bstep (se 1 (by rfl) ⟨1027583, by rfl⟩ : syracuseStep 1370111 = 2055167) B2055167
theorem B7801211 : Blo 1368503 7801211 := bstep (se 1 (by rfl) ⟨5850908, by rfl⟩ : syracuseStep 7801211 = 11701817) B11701817
theorem B6760979 : Blo 1368503 6760979 := bstep (se 1 (by rfl) ⟨5070734, by rfl⟩ : syracuseStep 6760979 = 10141469) B10141469
theorem B3083111 : Blo 1368503 3083111 := bstep (se 1 (by rfl) ⟨2312333, by rfl⟩ : syracuseStep 3083111 = 4624667) B4624667
theorem B19746355 : Blo 1368503 19746355 := bstep (se 1 (by rfl) ⟨14809766, by rfl⟩ : syracuseStep 19746355 = 29619533) B29619533
theorem B26332937 : Blo 1368503 26332937 := bstep (se 2 (by rfl) ⟨9874851, by rfl⟩ : syracuseStep 26332937 = 19749703) B19749703
theorem B15593309 : Blo 1368503 15593309 := bstep (se 3 (by rfl) ⟨2923745, by rfl⟩ : syracuseStep 15593309 = 5847491) B5847491
theorem B2052863 : Blo 1368503 2052863 := bstep (se 1 (by rfl) ⟨1539647, by rfl⟩ : syracuseStep 2052863 = 3079295) B3079295
theorem B4167145 : Blo 1368503 4167145 := bstep (se 2 (by rfl) ⟨1562679, by rfl⟩ : syracuseStep 4167145 = 3125359) B3125359
theorem B11253871 : Blo 1368503 11253871 := bstep (se 1 (by rfl) ⟨8440403, by rfl⟩ : syracuseStep 11253871 = 16880807) B16880807
theorem B6929711 : Blo 1368503 6929711 := bstep (se 1 (by rfl) ⟨5197283, by rfl⟩ : syracuseStep 6929711 = 10394567) B10394567
theorem B3465119 : Blo 1368503 3465119 := bstep (se 1 (by rfl) ⟨2598839, by rfl⟩ : syracuseStep 3465119 = 5197679) B5197679
theorem B1368575 : Blo 1368503 1368575 := bstep (se 1 (by rfl) ⟨1026431, by rfl⟩ : syracuseStep 1368575 = 2052863) B2052863
theorem B101254043 : Blo 1368503 101254043 := bstep (se 1 (by rfl) ⟨75940532, by rfl⟩ : syracuseStep 101254043 = 151881065) B151881065
theorem B4507319 : Blo 1368503 4507319 := bstep (se 1 (by rfl) ⟨3380489, by rfl⟩ : syracuseStep 4507319 = 6760979) B6760979
theorem B4622561 : Blo 1368503 4622561 := bstep (se 2 (by rfl) ⟨1733460, by rfl⟩ : syracuseStep 4622561 = 3466921) B3466921
theorem B2053535 : Blo 1368503 2053535 := bstep (se 1 (by rfl) ⟨1540151, by rfl⟩ : syracuseStep 2053535 = 3080303) B3080303
theorem B15005161 : Blo 1368503 15005161 := bstep (se 2 (by rfl) ⟨5626935, by rfl⟩ : syracuseStep 15005161 = 11253871) B11253871
theorem B2774983 : Blo 1368503 2774983 := bstep (se 1 (by rfl) ⟨2081237, by rfl⟩ : syracuseStep 2774983 = 4162475) B4162475
theorem B2054303 : Blo 1368503 2054303 := bstep (se 1 (by rfl) ⟨1540727, by rfl⟩ : syracuseStep 2054303 = 3081455) B3081455
theorem B5200807 : Blo 1368503 5200807 := bstep (se 1 (by rfl) ⟨3900605, by rfl⟩ : syracuseStep 5200807 = 7801211) B7801211
theorem B2055407 : Blo 1368503 2055407 := bstep (se 1 (by rfl) ⟨1541555, by rfl⟩ : syracuseStep 2055407 = 3083111) B3083111
theorem B26328473 : Blo 1368503 26328473 := bstep (se 2 (by rfl) ⟨9873177, by rfl⟩ : syracuseStep 26328473 = 19746355) B19746355
theorem B4619807 : Blo 1368503 4619807 := bstep (se 1 (by rfl) ⟨3464855, by rfl⟩ : syracuseStep 4619807 = 6929711) B6929711
theorem B17555291 : Blo 1368503 17555291 := bstep (se 1 (by rfl) ⟨13166468, by rfl⟩ : syracuseStep 17555291 = 26332937) B26332937
theorem B22224773 : Blo 1368503 22224773 := bstep (se 4 (by rfl) ⟨2083572, by rfl⟩ : syracuseStep 22224773 = 4167145) B4167145
theorem B10395539 : Blo 1368503 10395539 := bstep (se 1 (by rfl) ⟨7796654, by rfl⟩ : syracuseStep 10395539 = 15593309) B15593309
theorem B2310079 : Blo 1368503 2310079 := bstep (se 1 (by rfl) ⟨1732559, by rfl⟩ : syracuseStep 2310079 = 3465119) B3465119
theorem B67502695 : Blo 1368503 67502695 := bstep (se 1 (by rfl) ⟨50627021, by rfl⟩ : syracuseStep 67502695 = 101254043) B101254043
theorem B1369023 : Blo 1368503 1369023 := bstep (se 1 (by rfl) ⟨1026767, by rfl⟩ : syracuseStep 1369023 = 2053535) B2053535
theorem B1369535 : Blo 1368503 1369535 := bstep (se 1 (by rfl) ⟨1027151, by rfl⟩ : syracuseStep 1369535 = 2054303) B2054303
theorem B3081707 : Blo 1368503 3081707 := bstep (se 1 (by rfl) ⟨2311280, by rfl⟩ : syracuseStep 3081707 = 4622561) B4622561
theorem B20006881 : Blo 1368503 20006881 := bstep (se 2 (by rfl) ⟨7502580, by rfl⟩ : syracuseStep 20006881 = 15005161) B15005161
theorem B1370271 : Blo 1368503 1370271 := bstep (se 1 (by rfl) ⟨1027703, by rfl⟩ : syracuseStep 1370271 = 2055407) B2055407
theorem B6934409 : Blo 1368503 6934409 := bstep (se 2 (by rfl) ⟨2600403, by rfl⟩ : syracuseStep 6934409 = 5200807) B5200807
theorem B17552315 : Blo 1368503 17552315 := bstep (se 1 (by rfl) ⟨13164236, by rfl⟩ : syracuseStep 17552315 = 26328473) B26328473
theorem B11703527 : Blo 1368503 11703527 := bstep (se 1 (by rfl) ⟨8777645, by rfl⟩ : syracuseStep 11703527 = 17555291) B17555291
theorem B14816515 : Blo 1368503 14816515 := bstep (se 1 (by rfl) ⟨11112386, by rfl⟩ : syracuseStep 14816515 = 22224773) B22224773
theorem B3699977 : Blo 1368503 3699977 := bstep (se 2 (by rfl) ⟨1387491, by rfl⟩ : syracuseStep 3699977 = 2774983) B2774983
theorem B3004879 : Blo 1368503 3004879 := bstep (se 1 (by rfl) ⟨2253659, by rfl⟩ : syracuseStep 3004879 = 4507319) B4507319
theorem B3079871 : Blo 1368503 3079871 := bstep (se 1 (by rfl) ⟨2309903, by rfl⟩ : syracuseStep 3079871 = 4619807) B4619807
theorem B3080105 : Blo 1368503 3080105 := bstep (se 2 (by rfl) ⟨1155039, by rfl⟩ : syracuseStep 3080105 = 2310079) B2310079
theorem B6930359 : Blo 1368503 6930359 := bstep (se 1 (by rfl) ⟨5197769, by rfl⟩ : syracuseStep 6930359 = 10395539) B10395539
theorem B4006505 : Blo 1368503 4006505 := bstep (se 2 (by rfl) ⟨1502439, by rfl⟩ : syracuseStep 4006505 = 3004879) B3004879
theorem B106703365 : Blo 1368503 106703365 := bstep (se 4 (by rfl) ⟨10003440, by rfl⟩ : syracuseStep 106703365 = 20006881) B20006881
theorem B4622939 : Blo 1368503 4622939 := bstep (se 1 (by rfl) ⟨3467204, by rfl⟩ : syracuseStep 4622939 = 6934409) B6934409
theorem B11701543 : Blo 1368503 11701543 := bstep (se 1 (by rfl) ⟨8776157, by rfl⟩ : syracuseStep 11701543 = 17552315) B17552315
theorem B9866605 : Blo 1368503 9866605 := bstep (se 3 (by rfl) ⟨1849988, by rfl⟩ : syracuseStep 9866605 = 3699977) B3699977
theorem B7802351 : Blo 1368503 7802351 := bstep (se 1 (by rfl) ⟨5851763, by rfl⟩ : syracuseStep 7802351 = 11703527) B11703527
theorem B19755353 : Blo 1368503 19755353 := bstep (se 2 (by rfl) ⟨7408257, by rfl⟩ : syracuseStep 19755353 = 14816515) B14816515
theorem B2053247 : Blo 1368503 2053247 := bstep (se 1 (by rfl) ⟨1539935, by rfl⟩ : syracuseStep 2053247 = 3079871) B3079871
theorem B2053403 : Blo 1368503 2053403 := bstep (se 1 (by rfl) ⟨1540052, by rfl⟩ : syracuseStep 2053403 = 3080105) B3080105
theorem B90003593 : Blo 1368503 90003593 := bstep (se 2 (by rfl) ⟨33751347, by rfl⟩ : syracuseStep 90003593 = 67502695) B67502695
theorem B2054471 : Blo 1368503 2054471 := bstep (se 1 (by rfl) ⟨1540853, by rfl⟩ : syracuseStep 2054471 = 3081707) B3081707
theorem B4620239 : Blo 1368503 4620239 := bstep (se 1 (by rfl) ⟨3465179, by rfl⟩ : syracuseStep 4620239 = 6930359) B6930359
theorem B240009581 : Blo 1368503 240009581 := bstep (se 3 (by rfl) ⟨45001796, by rfl⟩ : syracuseStep 240009581 = 90003593) B90003593
theorem B2671003 : Blo 1368503 2671003 := bstep (se 1 (by rfl) ⟨2003252, by rfl⟩ : syracuseStep 2671003 = 4006505) B4006505
theorem B142271153 : Blo 1368503 142271153 := bstep (se 2 (by rfl) ⟨53351682, by rfl⟩ : syracuseStep 142271153 = 106703365) B106703365
theorem B1368831 : Blo 1368503 1368831 := bstep (se 1 (by rfl) ⟨1026623, by rfl⟩ : syracuseStep 1368831 = 2053247) B2053247
theorem B1368935 : Blo 1368503 1368935 := bstep (se 1 (by rfl) ⟨1026701, by rfl⟩ : syracuseStep 1368935 = 2053403) B2053403
theorem B1369647 : Blo 1368503 1369647 := bstep (se 1 (by rfl) ⟨1027235, by rfl⟩ : syracuseStep 1369647 = 2054471) B2054471
theorem B3081959 : Blo 1368503 3081959 := bstep (se 1 (by rfl) ⟨2311469, by rfl⟩ : syracuseStep 3081959 = 4622939) B4622939
theorem B15602057 : Blo 1368503 15602057 := bstep (se 2 (by rfl) ⟨5850771, by rfl⟩ : syracuseStep 15602057 = 11701543) B11701543
theorem B13170235 : Blo 1368503 13170235 := bstep (se 1 (by rfl) ⟨9877676, by rfl⟩ : syracuseStep 13170235 = 19755353) B19755353
theorem B13155473 : Blo 1368503 13155473 := bstep (se 2 (by rfl) ⟨4933302, by rfl⟩ : syracuseStep 13155473 = 9866605) B9866605
theorem B5201567 : Blo 1368503 5201567 := bstep (se 1 (by rfl) ⟨3901175, by rfl⟩ : syracuseStep 5201567 = 7802351) B7802351
theorem B3080159 : Blo 1368503 3080159 := bstep (se 1 (by rfl) ⟨2310119, by rfl⟩ : syracuseStep 3080159 = 4620239) B4620239
theorem B94847435 : Blo 1368503 94847435 := bstep (se 1 (by rfl) ⟨71135576, by rfl⟩ : syracuseStep 94847435 = 142271153) B142271153
theorem B640025549 : Blo 1368503 640025549 := bstep (se 3 (by rfl) ⟨120004790, by rfl⟩ : syracuseStep 640025549 = 240009581) B240009581
theorem B3467711 : Blo 1368503 3467711 := bstep (se 1 (by rfl) ⟨2600783, by rfl⟩ : syracuseStep 3467711 = 5201567) B5201567
theorem B17560313 : Blo 1368503 17560313 := bstep (se 2 (by rfl) ⟨6585117, by rfl⟩ : syracuseStep 17560313 = 13170235) B13170235
theorem B8770315 : Blo 1368503 8770315 := bstep (se 1 (by rfl) ⟨6577736, by rfl⟩ : syracuseStep 8770315 = 13155473) B13155473
theorem B2053439 : Blo 1368503 2053439 := bstep (se 1 (by rfl) ⟨1540079, by rfl⟩ : syracuseStep 2053439 = 3080159) B3080159
theorem B10401371 : Blo 1368503 10401371 := bstep (se 1 (by rfl) ⟨7801028, by rfl⟩ : syracuseStep 10401371 = 15602057) B15602057
theorem B3561337 : Blo 1368503 3561337 := bstep (se 2 (by rfl) ⟨1335501, by rfl⟩ : syracuseStep 3561337 = 2671003) B2671003
theorem B2054639 : Blo 1368503 2054639 := bstep (se 1 (by rfl) ⟨1540979, by rfl⟩ : syracuseStep 2054639 = 3081959) B3081959
theorem B11706875 : Blo 1368503 11706875 := bstep (se 1 (by rfl) ⟨8780156, by rfl⟩ : syracuseStep 11706875 = 17560313) B17560313
theorem B1368959 : Blo 1368503 1368959 := bstep (se 1 (by rfl) ⟨1026719, by rfl⟩ : syracuseStep 1368959 = 2053439) B2053439
theorem B2311807 : Blo 1368503 2311807 := bstep (se 1 (by rfl) ⟨1733855, by rfl⟩ : syracuseStep 2311807 = 3467711) B3467711
theorem B1369759 : Blo 1368503 1369759 := bstep (se 1 (by rfl) ⟨1027319, by rfl⟩ : syracuseStep 1369759 = 2054639) B2054639
theorem B426683699 : Blo 1368503 426683699 := bstep (se 1 (by rfl) ⟨320012774, by rfl⟩ : syracuseStep 426683699 = 640025549) B640025549
theorem B11693753 : Blo 1368503 11693753 := bstep (se 2 (by rfl) ⟨4385157, by rfl⟩ : syracuseStep 11693753 = 8770315) B8770315
theorem B6934247 : Blo 1368503 6934247 := bstep (se 1 (by rfl) ⟨5200685, by rfl⟩ : syracuseStep 6934247 = 10401371) B10401371
theorem B18993797 : Blo 1368503 18993797 := bstep (se 4 (by rfl) ⟨1780668, by rfl⟩ : syracuseStep 18993797 = 3561337) B3561337
theorem B63231623 : Blo 1368503 63231623 := bstep (se 1 (by rfl) ⟨47423717, by rfl⟩ : syracuseStep 63231623 = 94847435) B94847435
theorem B3082409 : Blo 1368503 3082409 := bstep (se 2 (by rfl) ⟨1155903, by rfl⟩ : syracuseStep 3082409 = 2311807) B2311807
theorem B4622831 : Blo 1368503 4622831 := bstep (se 1 (by rfl) ⟨3467123, by rfl⟩ : syracuseStep 4622831 = 6934247) B6934247
theorem B284455799 : Blo 1368503 284455799 := bstep (se 1 (by rfl) ⟨213341849, by rfl⟩ : syracuseStep 284455799 = 426683699) B426683699
theorem B7795835 : Blo 1368503 7795835 := bstep (se 1 (by rfl) ⟨5846876, by rfl⟩ : syracuseStep 7795835 = 11693753) B11693753
theorem B7804583 : Blo 1368503 7804583 := bstep (se 1 (by rfl) ⟨5853437, by rfl⟩ : syracuseStep 7804583 = 11706875) B11706875
theorem B12662531 : Blo 1368503 12662531 := bstep (se 1 (by rfl) ⟨9496898, by rfl⟩ : syracuseStep 12662531 = 18993797) B18993797
theorem B42154415 : Blo 1368503 42154415 := bstep (se 1 (by rfl) ⟨31615811, by rfl⟩ : syracuseStep 42154415 = 63231623) B63231623
theorem B189637199 : Blo 1368503 189637199 := bstep (se 1 (by rfl) ⟨142227899, by rfl⟩ : syracuseStep 189637199 = 284455799) B284455799
theorem B5203055 : Blo 1368503 5203055 := bstep (se 1 (by rfl) ⟨3902291, by rfl⟩ : syracuseStep 5203055 = 7804583) B7804583
theorem B3081887 : Blo 1368503 3081887 := bstep (se 1 (by rfl) ⟨2311415, by rfl⟩ : syracuseStep 3081887 = 4622831) B4622831
theorem B5197223 : Blo 1368503 5197223 := bstep (se 1 (by rfl) ⟨3897917, by rfl⟩ : syracuseStep 5197223 = 7795835) B7795835
theorem B8441687 : Blo 1368503 8441687 := bstep (se 1 (by rfl) ⟨6331265, by rfl⟩ : syracuseStep 8441687 = 12662531) B12662531
theorem B28102943 : Blo 1368503 28102943 := bstep (se 1 (by rfl) ⟨21077207, by rfl⟩ : syracuseStep 28102943 = 42154415) B42154415
theorem B2054939 : Blo 1368503 2054939 := bstep (se 1 (by rfl) ⟨1541204, by rfl⟩ : syracuseStep 2054939 = 3082409) B3082409
theorem B18735295 : Blo 1368503 18735295 := bstep (se 1 (by rfl) ⟨14051471, by rfl⟩ : syracuseStep 18735295 = 28102943) B28102943
theorem B1369959 : Blo 1368503 1369959 := bstep (se 1 (by rfl) ⟨1027469, by rfl⟩ : syracuseStep 1369959 = 2054939) B2054939
theorem B3468703 : Blo 1368503 3468703 := bstep (se 1 (by rfl) ⟨2601527, by rfl⟩ : syracuseStep 3468703 = 5203055) B5203055
theorem B126424799 : Blo 1368503 126424799 := bstep (se 1 (by rfl) ⟨94818599, by rfl⟩ : syracuseStep 126424799 = 189637199) B189637199
theorem B2054591 : Blo 1368503 2054591 := bstep (se 1 (by rfl) ⟨1540943, by rfl⟩ : syracuseStep 2054591 = 3081887) B3081887
theorem B3464815 : Blo 1368503 3464815 := bstep (se 1 (by rfl) ⟨2598611, by rfl⟩ : syracuseStep 3464815 = 5197223) B5197223
theorem B5627791 : Blo 1368503 5627791 := bstep (se 1 (by rfl) ⟨4220843, by rfl⟩ : syracuseStep 5627791 = 8441687) B8441687
theorem B1369727 : Blo 1368503 1369727 := bstep (se 1 (by rfl) ⟨1027295, by rfl⟩ : syracuseStep 1369727 = 2054591) B2054591
theorem B24980393 : Blo 1368503 24980393 := bstep (se 2 (by rfl) ⟨9367647, by rfl⟩ : syracuseStep 24980393 = 18735295) B18735295
theorem B84283199 : Blo 1368503 84283199 := bstep (se 1 (by rfl) ⟨63212399, by rfl⟩ : syracuseStep 84283199 = 126424799) B126424799
theorem B4624937 : Blo 1368503 4624937 := bstep (se 2 (by rfl) ⟨1734351, by rfl⟩ : syracuseStep 4624937 = 3468703) B3468703
theorem B4619753 : Blo 1368503 4619753 := bstep (se 2 (by rfl) ⟨1732407, by rfl⟩ : syracuseStep 4619753 = 3464815) B3464815
theorem B7503721 : Blo 1368503 7503721 := bstep (se 2 (by rfl) ⟨2813895, by rfl⟩ : syracuseStep 7503721 = 5627791) B5627791
theorem B40019845 : Blo 1368503 40019845 := bstep (se 4 (by rfl) ⟨3751860, by rfl⟩ : syracuseStep 40019845 = 7503721) B7503721
theorem B3083291 : Blo 1368503 3083291 := bstep (se 1 (by rfl) ⟨2312468, by rfl⟩ : syracuseStep 3083291 = 4624937) B4624937
theorem B16653595 : Blo 1368503 16653595 := bstep (se 1 (by rfl) ⟨12490196, by rfl⟩ : syracuseStep 16653595 = 24980393) B24980393
theorem B3079835 : Blo 1368503 3079835 := bstep (se 1 (by rfl) ⟨2309876, by rfl⟩ : syracuseStep 3079835 = 4619753) B4619753
theorem B56188799 : Blo 1368503 56188799 := bstep (se 1 (by rfl) ⟨42141599, by rfl⟩ : syracuseStep 56188799 = 84283199) B84283199
theorem B22204793 : Blo 1368503 22204793 := bstep (se 2 (by rfl) ⟨8326797, by rfl⟩ : syracuseStep 22204793 = 16653595) B16653595
theorem B2053223 : Blo 1368503 2053223 := bstep (se 1 (by rfl) ⟨1539917, by rfl⟩ : syracuseStep 2053223 = 3079835) B3079835
theorem B53359793 : Blo 1368503 53359793 := bstep (se 2 (by rfl) ⟨20009922, by rfl⟩ : syracuseStep 53359793 = 40019845) B40019845
theorem B37459199 : Blo 1368503 37459199 := bstep (se 1 (by rfl) ⟨28094399, by rfl⟩ : syracuseStep 37459199 = 56188799) B56188799
theorem B2055527 : Blo 1368503 2055527 := bstep (se 1 (by rfl) ⟨1541645, by rfl⟩ : syracuseStep 2055527 = 3083291) B3083291
theorem B14803195 : Blo 1368503 14803195 := bstep (se 1 (by rfl) ⟨11102396, by rfl⟩ : syracuseStep 14803195 = 22204793) B22204793
theorem B1368815 : Blo 1368503 1368815 := bstep (se 1 (by rfl) ⟨1026611, by rfl⟩ : syracuseStep 1368815 = 2053223) B2053223
theorem B1370351 : Blo 1368503 1370351 := bstep (se 1 (by rfl) ⟨1027763, by rfl⟩ : syracuseStep 1370351 = 2055527) B2055527
theorem B35573195 : Blo 1368503 35573195 := bstep (se 1 (by rfl) ⟨26679896, by rfl⟩ : syracuseStep 35573195 = 53359793) B53359793
theorem B24972799 : Blo 1368503 24972799 := bstep (se 1 (by rfl) ⟨18729599, by rfl⟩ : syracuseStep 24972799 = 37459199) B37459199
theorem B19737593 : Blo 1368503 19737593 := bstep (se 2 (by rfl) ⟨7401597, by rfl⟩ : syracuseStep 19737593 = 14803195) B14803195
theorem B33297065 : Blo 1368503 33297065 := bstep (se 2 (by rfl) ⟨12486399, by rfl⟩ : syracuseStep 33297065 = 24972799) B24972799
theorem B23715463 : Blo 1368503 23715463 := bstep (se 1 (by rfl) ⟨17786597, by rfl⟩ : syracuseStep 23715463 = 35573195) B35573195
theorem B13158395 : Blo 1368503 13158395 := bstep (se 1 (by rfl) ⟨9868796, by rfl⟩ : syracuseStep 13158395 = 19737593) B19737593
theorem B22198043 : Blo 1368503 22198043 := bstep (se 1 (by rfl) ⟨16648532, by rfl⟩ : syracuseStep 22198043 = 33297065) B33297065
theorem B31620617 : Blo 1368503 31620617 := bstep (se 2 (by rfl) ⟨11857731, by rfl⟩ : syracuseStep 31620617 = 23715463) B23715463
theorem B21080411 : Blo 1368503 21080411 := bstep (se 1 (by rfl) ⟨15810308, by rfl⟩ : syracuseStep 21080411 = 31620617) B31620617
theorem B14798695 : Blo 1368503 14798695 := bstep (se 1 (by rfl) ⟨11099021, by rfl⟩ : syracuseStep 14798695 = 22198043) B22198043
theorem B8772263 : Blo 1368503 8772263 := bstep (se 1 (by rfl) ⟨6579197, by rfl⟩ : syracuseStep 8772263 = 13158395) B13158395
theorem B14053607 : Blo 1368503 14053607 := bstep (se 1 (by rfl) ⟨10540205, by rfl⟩ : syracuseStep 14053607 = 21080411) B21080411
theorem B19731593 : Blo 1368503 19731593 := bstep (se 2 (by rfl) ⟨7399347, by rfl⟩ : syracuseStep 19731593 = 14798695) B14798695
theorem B5848175 : Blo 1368503 5848175 := bstep (se 1 (by rfl) ⟨4386131, by rfl⟩ : syracuseStep 5848175 = 8772263) B8772263
theorem B9369071 : Blo 1368503 9369071 := bstep (se 1 (by rfl) ⟨7026803, by rfl⟩ : syracuseStep 9369071 = 14053607) B14053607
theorem B13154395 : Blo 1368503 13154395 := bstep (se 1 (by rfl) ⟨9865796, by rfl⟩ : syracuseStep 13154395 = 19731593) B19731593
theorem B3898783 : Blo 1368503 3898783 := bstep (se 1 (by rfl) ⟨2924087, by rfl⟩ : syracuseStep 3898783 = 5848175) B5848175
theorem B17539193 : Blo 1368503 17539193 := bstep (se 2 (by rfl) ⟨6577197, by rfl⟩ : syracuseStep 17539193 = 13154395) B13154395
theorem B6246047 : Blo 1368503 6246047 := bstep (se 1 (by rfl) ⟨4684535, by rfl⟩ : syracuseStep 6246047 = 9369071) B9369071
theorem B5198377 : Blo 1368503 5198377 := bstep (se 2 (by rfl) ⟨1949391, by rfl⟩ : syracuseStep 5198377 = 3898783) B3898783
theorem B6931169 : Blo 1368503 6931169 := bstep (se 2 (by rfl) ⟨2599188, by rfl⟩ : syracuseStep 6931169 = 5198377) B5198377
theorem B4164031 : Blo 1368503 4164031 := bstep (se 1 (by rfl) ⟨3123023, by rfl⟩ : syracuseStep 4164031 = 6246047) B6246047
theorem B11692795 : Blo 1368503 11692795 := bstep (se 1 (by rfl) ⟨8769596, by rfl⟩ : syracuseStep 11692795 = 17539193) B17539193
theorem B4620779 : Blo 1368503 4620779 := bstep (se 1 (by rfl) ⟨3465584, by rfl⟩ : syracuseStep 4620779 = 6931169) B6931169
theorem B15590393 : Blo 1368503 15590393 := bstep (se 2 (by rfl) ⟨5846397, by rfl⟩ : syracuseStep 15590393 = 11692795) B11692795
theorem B22208165 : Blo 1368503 22208165 := bstep (se 4 (by rfl) ⟨2082015, by rfl⟩ : syracuseStep 22208165 = 4164031) B4164031
theorem B3080519 : Blo 1368503 3080519 := bstep (se 1 (by rfl) ⟨2310389, by rfl⟩ : syracuseStep 3080519 = 4620779) B4620779
theorem B14805443 : Blo 1368503 14805443 := bstep (se 1 (by rfl) ⟨11104082, by rfl⟩ : syracuseStep 14805443 = 22208165) B22208165
theorem B10393595 : Blo 1368503 10393595 := bstep (se 1 (by rfl) ⟨7795196, by rfl⟩ : syracuseStep 10393595 = 15590393) B15590393
theorem B39481181 : Blo 1368503 39481181 := bstep (se 3 (by rfl) ⟨7402721, by rfl⟩ : syracuseStep 39481181 = 14805443) B14805443
theorem B2053679 : Blo 1368503 2053679 := bstep (se 1 (by rfl) ⟨1540259, by rfl⟩ : syracuseStep 2053679 = 3080519) B3080519
theorem B6929063 : Blo 1368503 6929063 := bstep (se 1 (by rfl) ⟨5196797, by rfl⟩ : syracuseStep 6929063 = 10393595) B10393595
theorem B1369119 : Blo 1368503 1369119 := bstep (se 1 (by rfl) ⟨1026839, by rfl⟩ : syracuseStep 1369119 = 2053679) B2053679
theorem B4619375 : Blo 1368503 4619375 := bstep (se 1 (by rfl) ⟨3464531, by rfl⟩ : syracuseStep 4619375 = 6929063) B6929063
theorem B26320787 : Blo 1368503 26320787 := bstep (se 1 (by rfl) ⟨19740590, by rfl⟩ : syracuseStep 26320787 = 39481181) B39481181
theorem B3079583 : Blo 1368503 3079583 := bstep (se 1 (by rfl) ⟨2309687, by rfl⟩ : syracuseStep 3079583 = 4619375) B4619375
theorem B17547191 : Blo 1368503 17547191 := bstep (se 1 (by rfl) ⟨13160393, by rfl⟩ : syracuseStep 17547191 = 26320787) B26320787
theorem B2053055 : Blo 1368503 2053055 := bstep (se 1 (by rfl) ⟨1539791, by rfl⟩ : syracuseStep 2053055 = 3079583) B3079583
theorem B11698127 : Blo 1368503 11698127 := bstep (se 1 (by rfl) ⟨8773595, by rfl⟩ : syracuseStep 11698127 = 17547191) B17547191
theorem B1368703 : Blo 1368503 1368703 := bstep (se 1 (by rfl) ⟨1026527, by rfl⟩ : syracuseStep 1368703 = 2053055) B2053055
theorem B7798751 : Blo 1368503 7798751 := bstep (se 1 (by rfl) ⟨5849063, by rfl⟩ : syracuseStep 7798751 = 11698127) B11698127
theorem B5199167 : Blo 1368503 5199167 := bstep (se 1 (by rfl) ⟨3899375, by rfl⟩ : syracuseStep 5199167 = 7798751) B7798751
theorem B3466111 : Blo 1368503 3466111 := bstep (se 1 (by rfl) ⟨2599583, by rfl⟩ : syracuseStep 3466111 = 5199167) B5199167
theorem B4621481 : Blo 1368503 4621481 := bstep (se 2 (by rfl) ⟨1733055, by rfl⟩ : syracuseStep 4621481 = 3466111) B3466111
theorem B3080987 : Blo 1368503 3080987 := bstep (se 1 (by rfl) ⟨2310740, by rfl⟩ : syracuseStep 3080987 = 4621481) B4621481
theorem B2053991 : Blo 1368503 2053991 := bstep (se 1 (by rfl) ⟨1540493, by rfl⟩ : syracuseStep 2053991 = 3080987) B3080987
theorem B1369327 : Blo 1368503 1369327 := bstep (se 1 (by rfl) ⟨1026995, by rfl⟩ : syracuseStep 1369327 = 2053991) B2053991

theorem C0 (j : ℕ) (h1 : 342125 ≤ j) (h2 : j ≤ 342625) : Blo 1368503 (4 * j + 3) := by
  interval_cases j
  · exact B1368503
  · exact B1368507
  · exact B1368511
  · exact B1368515
  · exact B1368519
  · exact B1368523
  · exact B1368527
  · exact B1368531
  · exact B1368535
  · exact B1368539
  · exact B1368543
  · exact B1368547
  · exact B1368551
  · exact B1368555
  · exact B1368559
  · exact B1368563
  · exact B1368567
  · exact B1368571
  · exact B1368575
  · exact B1368579
  · exact B1368583
  · exact B1368587
  · exact B1368591
  · exact B1368595
  · exact B1368599
  · exact B1368603
  · exact B1368607
  · exact B1368611
  · exact B1368615
  · exact B1368619
  · exact B1368623
  · exact B1368627
  · exact B1368631
  · exact B1368635
  · exact B1368639
  · exact B1368643
  · exact B1368647
  · exact B1368651
  · exact B1368655
  · exact B1368659
  · exact B1368663
  · exact B1368667
  · exact B1368671
  · exact B1368675
  · exact B1368679
  · exact B1368683
  · exact B1368687
  · exact B1368691
  · exact B1368695
  · exact B1368699
  · exact B1368703
  · exact B1368707
  · exact B1368711
  · exact B1368715
  · exact B1368719
  · exact B1368723
  · exact B1368727
  · exact B1368731
  · exact B1368735
  · exact B1368739
  · exact B1368743
  · exact B1368747
  · exact B1368751
  · exact B1368755
  · exact B1368759
  · exact B1368763
  · exact B1368767
  · exact B1368771
  · exact B1368775
  · exact B1368779
  · exact B1368783
  · exact B1368787
  · exact B1368791
  · exact B1368795
  · exact B1368799
  · exact B1368803
  · exact B1368807
  · exact B1368811
  · exact B1368815
  · exact B1368819
  · exact B1368823
  · exact B1368827
  · exact B1368831
  · exact B1368835
  · exact B1368839
  · exact B1368843
  · exact B1368847
  · exact B1368851
  · exact B1368855
  · exact B1368859
  · exact B1368863
  · exact B1368867
  · exact B1368871
  · exact B1368875
  · exact B1368879
  · exact B1368883
  · exact B1368887
  · exact B1368891
  · exact B1368895
  · exact B1368899
  · exact B1368903
  · exact B1368907
  · exact B1368911
  · exact B1368915
  · exact B1368919
  · exact B1368923
  · exact B1368927
  · exact B1368931
  · exact B1368935
  · exact B1368939
  · exact B1368943
  · exact B1368947
  · exact B1368951
  · exact B1368955
  · exact B1368959
  · exact B1368963
  · exact B1368967
  · exact B1368971
  · exact B1368975
  · exact B1368979
  · exact B1368983
  · exact B1368987
  · exact B1368991
  · exact B1368995
  · exact B1368999
  · exact B1369003
  · exact B1369007
  · exact B1369011
  · exact B1369015
  · exact B1369019
  · exact B1369023
  · exact B1369027
  · exact B1369031
  · exact B1369035
  · exact B1369039
  · exact B1369043
  · exact B1369047
  · exact B1369051
  · exact B1369055
  · exact B1369059
  · exact B1369063
  · exact B1369067
  · exact B1369071
  · exact B1369075
  · exact B1369079
  · exact B1369083
  · exact B1369087
  · exact B1369091
  · exact B1369095
  · exact B1369099
  · exact B1369103
  · exact B1369107
  · exact B1369111
  · exact B1369115
  · exact B1369119
  · exact B1369123
  · exact B1369127
  · exact B1369131
  · exact B1369135
  · exact B1369139
  · exact B1369143
  · exact B1369147
  · exact B1369151
  · exact B1369155
  · exact B1369159
  · exact B1369163
  · exact B1369167
  · exact B1369171
  · exact B1369175
  · exact B1369179
  · exact B1369183
  · exact B1369187
  · exact B1369191
  · exact B1369195
  · exact B1369199
  · exact B1369203
  · exact B1369207
  · exact B1369211
  · exact B1369215
  · exact B1369219
  · exact B1369223
  · exact B1369227
  · exact B1369231
  · exact B1369235
  · exact B1369239
  · exact B1369243
  · exact B1369247
  · exact B1369251
  · exact B1369255
  · exact B1369259
  · exact B1369263
  · exact B1369267
  · exact B1369271
  · exact B1369275
  · exact B1369279
  · exact B1369283
  · exact B1369287
  · exact B1369291
  · exact B1369295
  · exact B1369299
  · exact B1369303
  · exact B1369307
  · exact B1369311
  · exact B1369315
  · exact B1369319
  · exact B1369323
  · exact B1369327
  · exact B1369331
  · exact B1369335
  · exact B1369339
  · exact B1369343
  · exact B1369347
  · exact B1369351
  · exact B1369355
  · exact B1369359
  · exact B1369363
  · exact B1369367
  · exact B1369371
  · exact B1369375
  · exact B1369379
  · exact B1369383
  · exact B1369387
  · exact B1369391
  · exact B1369395
  · exact B1369399
  · exact B1369403
  · exact B1369407
  · exact B1369411
  · exact B1369415
  · exact B1369419
  · exact B1369423
  · exact B1369427
  · exact B1369431
  · exact B1369435
  · exact B1369439
  · exact B1369443
  · exact B1369447
  · exact B1369451
  · exact B1369455
  · exact B1369459
  · exact B1369463
  · exact B1369467
  · exact B1369471
  · exact B1369475
  · exact B1369479
  · exact B1369483
  · exact B1369487
  · exact B1369491
  · exact B1369495
  · exact B1369499
  · exact B1369503
  · exact B1369507
  · exact B1369511
  · exact B1369515
  · exact B1369519
  · exact B1369523
  · exact B1369527
  · exact B1369531
  · exact B1369535
  · exact B1369539
  · exact B1369543
  · exact B1369547
  · exact B1369551
  · exact B1369555
  · exact B1369559
  · exact B1369563
  · exact B1369567
  · exact B1369571
  · exact B1369575
  · exact B1369579
  · exact B1369583
  · exact B1369587
  · exact B1369591
  · exact B1369595
  · exact B1369599
  · exact B1369603
  · exact B1369607
  · exact B1369611
  · exact B1369615
  · exact B1369619
  · exact B1369623
  · exact B1369627
  · exact B1369631
  · exact B1369635
  · exact B1369639
  · exact B1369643
  · exact B1369647
  · exact B1369651
  · exact B1369655
  · exact B1369659
  · exact B1369663
  · exact B1369667
  · exact B1369671
  · exact B1369675
  · exact B1369679
  · exact B1369683
  · exact B1369687
  · exact B1369691
  · exact B1369695
  · exact B1369699
  · exact B1369703
  · exact B1369707
  · exact B1369711
  · exact B1369715
  · exact B1369719
  · exact B1369723
  · exact B1369727
  · exact B1369731
  · exact B1369735
  · exact B1369739
  · exact B1369743
  · exact B1369747
  · exact B1369751
  · exact B1369755
  · exact B1369759
  · exact B1369763
  · exact B1369767
  · exact B1369771
  · exact B1369775
  · exact B1369779
  · exact B1369783
  · exact B1369787
  · exact B1369791
  · exact B1369795
  · exact B1369799
  · exact B1369803
  · exact B1369807
  · exact B1369811
  · exact B1369815
  · exact B1369819
  · exact B1369823
  · exact B1369827
  · exact B1369831
  · exact B1369835
  · exact B1369839
  · exact B1369843
  · exact B1369847
  · exact B1369851
  · exact B1369855
  · exact B1369859
  · exact B1369863
  · exact B1369867
  · exact B1369871
  · exact B1369875
  · exact B1369879
  · exact B1369883
  · exact B1369887
  · exact B1369891
  · exact B1369895
  · exact B1369899
  · exact B1369903
  · exact B1369907
  · exact B1369911
  · exact B1369915
  · exact B1369919
  · exact B1369923
  · exact B1369927
  · exact B1369931
  · exact B1369935
  · exact B1369939
  · exact B1369943
  · exact B1369947
  · exact B1369951
  · exact B1369955
  · exact B1369959
  · exact B1369963
  · exact B1369967
  · exact B1369971
  · exact B1369975
  · exact B1369979
  · exact B1369983
  · exact B1369987
  · exact B1369991
  · exact B1369995
  · exact B1369999
  · exact B1370003
  · exact B1370007
  · exact B1370011
  · exact B1370015
  · exact B1370019
  · exact B1370023
  · exact B1370027
  · exact B1370031
  · exact B1370035
  · exact B1370039
  · exact B1370043
  · exact B1370047
  · exact B1370051
  · exact B1370055
  · exact B1370059
  · exact B1370063
  · exact B1370067
  · exact B1370071
  · exact B1370075
  · exact B1370079
  · exact B1370083
  · exact B1370087
  · exact B1370091
  · exact B1370095
  · exact B1370099
  · exact B1370103
  · exact B1370107
  · exact B1370111
  · exact B1370115
  · exact B1370119
  · exact B1370123
  · exact B1370127
  · exact B1370131
  · exact B1370135
  · exact B1370139
  · exact B1370143
  · exact B1370147
  · exact B1370151
  · exact B1370155
  · exact B1370159
  · exact B1370163
  · exact B1370167
  · exact B1370171
  · exact B1370175
  · exact B1370179
  · exact B1370183
  · exact B1370187
  · exact B1370191
  · exact B1370195
  · exact B1370199
  · exact B1370203
  · exact B1370207
  · exact B1370211
  · exact B1370215
  · exact B1370219
  · exact B1370223
  · exact B1370227
  · exact B1370231
  · exact B1370235
  · exact B1370239
  · exact B1370243
  · exact B1370247
  · exact B1370251
  · exact B1370255
  · exact B1370259
  · exact B1370263
  · exact B1370267
  · exact B1370271
  · exact B1370275
  · exact B1370279
  · exact B1370283
  · exact B1370287
  · exact B1370291
  · exact B1370295
  · exact B1370299
  · exact B1370303
  · exact B1370307
  · exact B1370311
  · exact B1370315
  · exact B1370319
  · exact B1370323
  · exact B1370327
  · exact B1370331
  · exact B1370335
  · exact B1370339
  · exact B1370343
  · exact B1370347
  · exact B1370351
  · exact B1370355
  · exact B1370359
  · exact B1370363
  · exact B1370367
  · exact B1370371
  · exact B1370375
  · exact B1370379
  · exact B1370383
  · exact B1370387
  · exact B1370391
  · exact B1370395
  · exact B1370399
  · exact B1370403
  · exact B1370407
  · exact B1370411
  · exact B1370415
  · exact B1370419
  · exact B1370423
  · exact B1370427
  · exact B1370431
  · exact B1370435
  · exact B1370439
  · exact B1370443
  · exact B1370447
  · exact B1370451
  · exact B1370455
  · exact B1370459
  · exact B1370463
  · exact B1370467
  · exact B1370471
  · exact B1370475
  · exact B1370479
  · exact B1370483
  · exact B1370487
  · exact B1370491
  · exact B1370495
  · exact B1370499
  · exact B1370503

theorem solution (m : ℕ) (hlo : 1368503 ≤ m) (hhi : m ≤ 1370503) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 342125 ≤ j := by omega
    have hj2 : j ≤ 342625 := by omega
    have hb : Blo 1368503 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
