-- Prove2me | solution 1 for syracuse_descends_range_1447543_1449543
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:43:15.026488+00:00
-- url     : https://prove2.me/submissions/7c7e432f-00a9-4363-9d64-cda6602be182

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


theorem B3260429 : Blo 1447543 3260429 := bbase (se 3 (by rfl) ⟨611330, by rfl⟩ : syracuseStep 3260429 = 1222661) (by norm_num)
theorem B1630237 : Blo 1447543 1630237 := bbase (se 3 (by rfl) ⟨305669, by rfl⟩ : syracuseStep 1630237 = 611339) (by norm_num)
theorem B1630273 : Blo 1447543 1630273 := bbase (se 2 (by rfl) ⟨611352, by rfl⟩ : syracuseStep 1630273 = 1222705) (by norm_num)
theorem B47644757 : Blo 1447543 47644757 := bbase (se 8 (by rfl) ⟨279168, by rfl⟩ : syracuseStep 47644757 = 558337) (by norm_num)
theorem B3260501 : Blo 1447543 3260501 := bbase (se 8 (by rfl) ⟨19104, by rfl⟩ : syracuseStep 3260501 = 38209) (by norm_num)
theorem B4890725 : Blo 1447543 4890725 := bbase (se 4 (by rfl) ⟨458505, by rfl⟩ : syracuseStep 4890725 = 917011) (by norm_num)
theorem B1630309 : Blo 1447543 1630309 := bbase (se 4 (by rfl) ⟨152841, by rfl⟩ : syracuseStep 1630309 = 305683) (by norm_num)
theorem B7331957 : Blo 1447543 7331957 := bbase (se 5 (by rfl) ⟨343685, by rfl⟩ : syracuseStep 7331957 = 687371) (by norm_num)
theorem B1630345 : Blo 1447543 1630345 := bbase (se 2 (by rfl) ⟨611379, by rfl⟩ : syracuseStep 1630345 = 1222759) (by norm_num)
theorem B5873813 : Blo 1447543 5873813 := bbase (se 6 (by rfl) ⟨137667, by rfl⟩ : syracuseStep 5873813 = 275335) (by norm_num)
theorem B3260573 : Blo 1447543 3260573 := bbase (se 3 (by rfl) ⟨611357, by rfl⟩ : syracuseStep 3260573 = 1222715) (by norm_num)
theorem B1630381 : Blo 1447543 1630381 := bbase (se 3 (by rfl) ⟨305696, by rfl⟩ : syracuseStep 1630381 = 611393) (by norm_num)
theorem B8249525 : Blo 1447543 8249525 := bbase (se 5 (by rfl) ⟨386696, by rfl⟩ : syracuseStep 8249525 = 773393) (by norm_num)
theorem B1630417 : Blo 1447543 1630417 := bbase (se 2 (by rfl) ⟨611406, by rfl⟩ : syracuseStep 1630417 = 1222813) (by norm_num)
theorem B3260645 : Blo 1447543 3260645 := bbase (se 4 (by rfl) ⟨305685, by rfl⟩ : syracuseStep 3260645 = 611371) (by norm_num)
theorem B1630453 : Blo 1447543 1630453 := bbase (se 5 (by rfl) ⟨76427, by rfl⟩ : syracuseStep 1630453 = 152855) (by norm_num)
theorem B1630489 : Blo 1447543 1630489 := bbase (se 2 (by rfl) ⟨611433, by rfl⟩ : syracuseStep 1630489 = 1222867) (by norm_num)
theorem B3260717 : Blo 1447543 3260717 := bbase (se 3 (by rfl) ⟨611384, by rfl⟩ : syracuseStep 3260717 = 1222769) (by norm_num)
theorem B1630525 : Blo 1447543 1630525 := bbase (se 3 (by rfl) ⟨305723, by rfl⟩ : syracuseStep 1630525 = 611447) (by norm_num)
theorem B5292373 : Blo 1447543 5292373 := bbase (se 10 (by rfl) ⟨7752, by rfl⟩ : syracuseStep 5292373 = 15505) (by norm_num)
theorem B1630561 : Blo 1447543 1630561 := bbase (se 2 (by rfl) ⟨611460, by rfl⟩ : syracuseStep 1630561 = 1222921) (by norm_num)
theorem B3260789 : Blo 1447543 3260789 := bbase (se 5 (by rfl) ⟨152849, by rfl⟩ : syracuseStep 3260789 = 305699) (by norm_num)
theorem B1630597 : Blo 1447543 1630597 := bbase (se 4 (by rfl) ⟨152868, by rfl⟩ : syracuseStep 1630597 = 305737) (by norm_num)
theorem B5497253 : Blo 1447543 5497253 := bbase (se 4 (by rfl) ⟨515367, by rfl⟩ : syracuseStep 5497253 = 1030735) (by norm_num)
theorem B1630633 : Blo 1447543 1630633 := bbase (se 2 (by rfl) ⟨611487, by rfl⟩ : syracuseStep 1630633 = 1222975) (by norm_num)
theorem B3260861 : Blo 1447543 3260861 := bbase (se 3 (by rfl) ⟨611411, by rfl⟩ : syracuseStep 3260861 = 1222823) (by norm_num)
theorem B2171333 : Blo 1447543 2171333 := bbase (se 4 (by rfl) ⟨203562, by rfl⟩ : syracuseStep 2171333 = 407125) (by norm_num)
theorem B1630669 : Blo 1447543 1630669 := bbase (se 3 (by rfl) ⟨305750, by rfl⟩ : syracuseStep 1630669 = 611501) (by norm_num)
theorem B2171357 : Blo 1447543 2171357 := bbase (se 3 (by rfl) ⟨407129, by rfl⟩ : syracuseStep 2171357 = 814259) (by norm_num)
theorem B5366245 : Blo 1447543 5366245 := bbase (se 4 (by rfl) ⟨503085, by rfl⟩ : syracuseStep 5366245 = 1006171) (by norm_num)
theorem B1630705 : Blo 1447543 1630705 := bbase (se 2 (by rfl) ⟨611514, by rfl⟩ : syracuseStep 1630705 = 1223029) (by norm_num)
theorem B2171381 : Blo 1447543 2171381 := bbase (se 5 (by rfl) ⟨101783, by rfl⟩ : syracuseStep 2171381 = 203567) (by norm_num)
theorem B3260933 : Blo 1447543 3260933 := bbase (se 4 (by rfl) ⟨305712, by rfl⟩ : syracuseStep 3260933 = 611425) (by norm_num)
theorem B2171405 : Blo 1447543 2171405 := bbase (se 3 (by rfl) ⟨407138, by rfl⟩ : syracuseStep 2171405 = 814277) (by norm_num)
theorem B15065621 : Blo 1447543 15065621 := bbase (se 6 (by rfl) ⟨353100, by rfl⟩ : syracuseStep 15065621 = 706201) (by norm_num)
theorem B4891157 : Blo 1447543 4891157 := bbase (se 6 (by rfl) ⟨114636, by rfl⟩ : syracuseStep 4891157 = 229273) (by norm_num)
theorem B2171429 : Blo 1447543 2171429 := bbase (se 4 (by rfl) ⟨203571, by rfl⟩ : syracuseStep 2171429 = 407143) (by norm_num)
theorem B2171453 : Blo 1447543 2171453 := bbase (se 3 (by rfl) ⟨407147, by rfl⟩ : syracuseStep 2171453 = 814295) (by norm_num)
theorem B3261005 : Blo 1447543 3261005 := bbase (se 3 (by rfl) ⟨611438, by rfl⟩ : syracuseStep 3261005 = 1222877) (by norm_num)
theorem B2171477 : Blo 1447543 2171477 := bbase (se 8 (by rfl) ⟨12723, by rfl⟩ : syracuseStep 2171477 = 25447) (by norm_num)
theorem B2171501 : Blo 1447543 2171501 := bbase (se 3 (by rfl) ⟨407156, by rfl⟩ : syracuseStep 2171501 = 814313) (by norm_num)
theorem B2171525 : Blo 1447543 2171525 := bbase (se 4 (by rfl) ⟨203580, by rfl⟩ : syracuseStep 2171525 = 407161) (by norm_num)
theorem B3261077 : Blo 1447543 3261077 := bbase (se 6 (by rfl) ⟨76431, by rfl⟩ : syracuseStep 3261077 = 152863) (by norm_num)
theorem B2171549 : Blo 1447543 2171549 := bbase (se 3 (by rfl) ⟨407165, by rfl⟩ : syracuseStep 2171549 = 814331) (by norm_num)
theorem B6267557 : Blo 1447543 6267557 := bbase (se 4 (by rfl) ⟨587583, by rfl⟩ : syracuseStep 6267557 = 1175167) (by norm_num)
theorem B2171573 : Blo 1447543 2171573 := bbase (se 5 (by rfl) ⟨101792, by rfl⟩ : syracuseStep 2171573 = 203585) (by norm_num)
theorem B5497541 : Blo 1447543 5497541 := bbase (se 4 (by rfl) ⟨515394, by rfl⟩ : syracuseStep 5497541 = 1030789) (by norm_num)
theorem B2171597 : Blo 1447543 2171597 := bbase (se 3 (by rfl) ⟨407174, by rfl⟩ : syracuseStep 2171597 = 814349) (by norm_num)
theorem B3261149 : Blo 1447543 3261149 := bbase (se 3 (by rfl) ⟨611465, by rfl⟩ : syracuseStep 3261149 = 1222931) (by norm_num)
theorem B2171621 : Blo 1447543 2171621 := bbase (se 4 (by rfl) ⟨203589, by rfl⟩ : syracuseStep 2171621 = 407179) (by norm_num)
theorem B2171645 : Blo 1447543 2171645 := bbase (se 3 (by rfl) ⟨407183, by rfl⟩ : syracuseStep 2171645 = 814367) (by norm_num)
theorem B2171669 : Blo 1447543 2171669 := bbase (se 6 (by rfl) ⟨50898, by rfl⟩ : syracuseStep 2171669 = 101797) (by norm_num)
theorem B3261221 : Blo 1447543 3261221 := bbase (se 4 (by rfl) ⟨305739, by rfl⟩ : syracuseStep 3261221 = 611479) (by norm_num)
theorem B2171693 : Blo 1447543 2171693 := bbase (se 3 (by rfl) ⟨407192, by rfl⟩ : syracuseStep 2171693 = 814385) (by norm_num)
theorem B2089781 : Blo 1447543 2089781 := bbase (se 5 (by rfl) ⟨97958, by rfl⟩ : syracuseStep 2089781 = 195917) (by norm_num)
theorem B2171717 : Blo 1447543 2171717 := bbase (se 4 (by rfl) ⟨203598, by rfl⟩ : syracuseStep 2171717 = 407197) (by norm_num)
theorem B2171741 : Blo 1447543 2171741 := bbase (se 3 (by rfl) ⟨407201, by rfl⟩ : syracuseStep 2171741 = 814403) (by norm_num)
theorem B3261293 : Blo 1447543 3261293 := bbase (se 3 (by rfl) ⟨611492, by rfl⟩ : syracuseStep 3261293 = 1222985) (by norm_num)
theorem B2171765 : Blo 1447543 2171765 := bbase (se 5 (by rfl) ⟨101801, by rfl⟩ : syracuseStep 2171765 = 203603) (by norm_num)
theorem B2171789 : Blo 1447543 2171789 := bbase (se 3 (by rfl) ⟨407210, by rfl⟩ : syracuseStep 2171789 = 814421) (by norm_num)
theorem B2171813 : Blo 1447543 2171813 := bbase (se 4 (by rfl) ⟨203607, by rfl⟩ : syracuseStep 2171813 = 407215) (by norm_num)
theorem B1983413 : Blo 1447543 1983413 := bbase (se 5 (by rfl) ⟨92972, by rfl⟩ : syracuseStep 1983413 = 185945) (by norm_num)
theorem B3261365 : Blo 1447543 3261365 := bbase (se 5 (by rfl) ⟨152876, by rfl⟩ : syracuseStep 3261365 = 305753) (by norm_num)
theorem B2171837 : Blo 1447543 2171837 := bbase (se 3 (by rfl) ⟨407219, by rfl⟩ : syracuseStep 2171837 = 814439) (by norm_num)
theorem B4891589 : Blo 1447543 4891589 := bbase (se 4 (by rfl) ⟨458586, by rfl⟩ : syracuseStep 4891589 = 917173) (by norm_num)
theorem B2171861 : Blo 1447543 2171861 := bbase (se 7 (by rfl) ⟨25451, by rfl⟩ : syracuseStep 2171861 = 50903) (by norm_num)
theorem B2171885 : Blo 1447543 2171885 := bbase (se 3 (by rfl) ⟨407228, by rfl⟩ : syracuseStep 2171885 = 814457) (by norm_num)
theorem B3261437 : Blo 1447543 3261437 := bbase (se 3 (by rfl) ⟨611519, by rfl⟩ : syracuseStep 3261437 = 1223039) (by norm_num)
theorem B2171909 : Blo 1447543 2171909 := bbase (se 4 (by rfl) ⟨203616, by rfl⟩ : syracuseStep 2171909 = 407233) (by norm_num)
theorem B2319365 : Blo 1447543 2319365 := bbase (se 4 (by rfl) ⟨217440, by rfl⟩ : syracuseStep 2319365 = 434881) (by norm_num)
theorem B2171933 : Blo 1447543 2171933 := bbase (se 3 (by rfl) ⟨407237, by rfl⟩ : syracuseStep 2171933 = 814475) (by norm_num)
theorem B2171957 : Blo 1447543 2171957 := bbase (se 5 (by rfl) ⟨101810, by rfl⟩ : syracuseStep 2171957 = 203621) (by norm_num)
theorem B2171981 : Blo 1447543 2171981 := bbase (se 3 (by rfl) ⟨407246, by rfl⟩ : syracuseStep 2171981 = 814493) (by norm_num)
theorem B2172005 : Blo 1447543 2172005 := bbase (se 4 (by rfl) ⟨203625, by rfl⟩ : syracuseStep 2172005 = 407251) (by norm_num)
theorem B6964325 : Blo 1447543 6964325 := bbase (se 4 (by rfl) ⟨652905, by rfl⟩ : syracuseStep 6964325 = 1305811) (by norm_num)
theorem B2172029 : Blo 1447543 2172029 := bbase (se 3 (by rfl) ⟨407255, by rfl⟩ : syracuseStep 2172029 = 814511) (by norm_num)
theorem B2172053 : Blo 1447543 2172053 := bbase (se 6 (by rfl) ⟨50907, by rfl⟩ : syracuseStep 2172053 = 101815) (by norm_num)
theorem B2172077 : Blo 1447543 2172077 := bbase (se 3 (by rfl) ⟨407264, by rfl⟩ : syracuseStep 2172077 = 814529) (by norm_num)
theorem B2172101 : Blo 1447543 2172101 := bbase (se 4 (by rfl) ⟨203634, by rfl⟩ : syracuseStep 2172101 = 407269) (by norm_num)
theorem B2172125 : Blo 1447543 2172125 := bbase (se 3 (by rfl) ⟨407273, by rfl⟩ : syracuseStep 2172125 = 814547) (by norm_num)
theorem B2172149 : Blo 1447543 2172149 := bbase (se 5 (by rfl) ⟨101819, by rfl⟩ : syracuseStep 2172149 = 203639) (by norm_num)
theorem B2172173 : Blo 1447543 2172173 := bbase (se 3 (by rfl) ⟨407282, by rfl⟩ : syracuseStep 2172173 = 814565) (by norm_num)
theorem B2172197 : Blo 1447543 2172197 := bbase (se 4 (by rfl) ⟨203643, by rfl⟩ : syracuseStep 2172197 = 407287) (by norm_num)
theorem B2172221 : Blo 1447543 2172221 := bbase (se 3 (by rfl) ⟨407291, by rfl⟩ : syracuseStep 2172221 = 814583) (by norm_num)
theorem B2786645 : Blo 1447543 2786645 := bbase (se 12 (by rfl) ⟨1020, by rfl⟩ : syracuseStep 2786645 = 2041) (by norm_num)
theorem B2172245 : Blo 1447543 2172245 := bbase (se 12 (by rfl) ⟨795, by rfl⟩ : syracuseStep 2172245 = 1591) (by norm_num)
theorem B2172269 : Blo 1447543 2172269 := bbase (se 3 (by rfl) ⟨407300, by rfl⟩ : syracuseStep 2172269 = 814601) (by norm_num)
theorem B4892021 : Blo 1447543 4892021 := bbase (se 5 (by rfl) ⟨229313, by rfl⟩ : syracuseStep 4892021 = 458627) (by norm_num)
theorem B2172293 : Blo 1447543 2172293 := bbase (se 4 (by rfl) ⟨203652, by rfl⟩ : syracuseStep 2172293 = 407305) (by norm_num)
theorem B7333253 : Blo 1447543 7333253 := bbase (se 4 (by rfl) ⟨687492, by rfl⟩ : syracuseStep 7333253 = 1374985) (by norm_num)
theorem B2172317 : Blo 1447543 2172317 := bbase (se 3 (by rfl) ⟨407309, by rfl⟩ : syracuseStep 2172317 = 814619) (by norm_num)
theorem B1467821 : Blo 1447543 1467821 := bbase (se 3 (by rfl) ⟨275216, by rfl⟩ : syracuseStep 1467821 = 550433) (by norm_num)
theorem B2172341 : Blo 1447543 2172341 := bbase (se 5 (by rfl) ⟨101828, by rfl⟩ : syracuseStep 2172341 = 203657) (by norm_num)
theorem B2172365 : Blo 1447543 2172365 := bbase (se 3 (by rfl) ⟨407318, by rfl⟩ : syracuseStep 2172365 = 814637) (by norm_num)
theorem B2172389 : Blo 1447543 2172389 := bbase (se 4 (by rfl) ⟨203661, by rfl⟩ : syracuseStep 2172389 = 407323) (by norm_num)
theorem B2172413 : Blo 1447543 2172413 := bbase (se 3 (by rfl) ⟨407327, by rfl⟩ : syracuseStep 2172413 = 814655) (by norm_num)
theorem B2442757 : Blo 1447543 2442757 := bbase (se 4 (by rfl) ⟨229008, by rfl⟩ : syracuseStep 2442757 = 458017) (by norm_num)
theorem B2172437 : Blo 1447543 2172437 := bbase (se 6 (by rfl) ⟨50916, by rfl⟩ : syracuseStep 2172437 = 101833) (by norm_num)
theorem B2172461 : Blo 1447543 2172461 := bbase (se 3 (by rfl) ⟨407336, by rfl⟩ : syracuseStep 2172461 = 814673) (by norm_num)
theorem B6956597 : Blo 1447543 6956597 := bbase (se 5 (by rfl) ⟨326090, by rfl⟩ : syracuseStep 6956597 = 652181) (by norm_num)
theorem B2172485 : Blo 1447543 2172485 := bbase (se 4 (by rfl) ⟨203670, by rfl⟩ : syracuseStep 2172485 = 407341) (by norm_num)
theorem B4957781 : Blo 1447543 4957781 := bbase (se 8 (by rfl) ⟨29049, by rfl⟩ : syracuseStep 4957781 = 58099) (by norm_num)
theorem B2442845 : Blo 1447543 2442845 := bbase (se 3 (by rfl) ⟨458033, by rfl⟩ : syracuseStep 2442845 = 916067) (by norm_num)
theorem B2172509 : Blo 1447543 2172509 := bbase (se 3 (by rfl) ⟨407345, by rfl⟩ : syracuseStep 2172509 = 814691) (by norm_num)
theorem B6186613 : Blo 1447543 6186613 := bbase (se 5 (by rfl) ⟨289997, by rfl⟩ : syracuseStep 6186613 = 579995) (by norm_num)
theorem B2172533 : Blo 1447543 2172533 := bbase (se 5 (by rfl) ⟨101837, by rfl⟩ : syracuseStep 2172533 = 203675) (by norm_num)
theorem B4122245 : Blo 1447543 4122245 := bbase (se 4 (by rfl) ⟨386460, by rfl⟩ : syracuseStep 4122245 = 772921) (by norm_num)
theorem B2172557 : Blo 1447543 2172557 := bbase (se 3 (by rfl) ⟨407354, by rfl⟩ : syracuseStep 2172557 = 814709) (by norm_num)
theorem B2172581 : Blo 1447543 2172581 := bbase (se 4 (by rfl) ⟨203679, by rfl⟩ : syracuseStep 2172581 = 407359) (by norm_num)
theorem B1468081 : Blo 1447543 1468081 := bbase (se 2 (by rfl) ⟨550530, by rfl⟩ : syracuseStep 1468081 = 1101061) (by norm_num)
theorem B2172605 : Blo 1447543 2172605 := bbase (se 3 (by rfl) ⟨407363, by rfl⟩ : syracuseStep 2172605 = 814727) (by norm_num)
theorem B2172629 : Blo 1447543 2172629 := bbase (se 7 (by rfl) ⟨25460, by rfl⟩ : syracuseStep 2172629 = 50921) (by norm_num)
theorem B2442973 : Blo 1447543 2442973 := bbase (se 3 (by rfl) ⟨458057, by rfl⟩ : syracuseStep 2442973 = 916115) (by norm_num)
theorem B2172653 : Blo 1447543 2172653 := bbase (se 3 (by rfl) ⟨407372, by rfl⟩ : syracuseStep 2172653 = 814745) (by norm_num)
theorem B2172677 : Blo 1447543 2172677 := bbase (se 4 (by rfl) ⟨203688, by rfl⟩ : syracuseStep 2172677 = 407377) (by norm_num)
theorem B2172701 : Blo 1447543 2172701 := bbase (se 3 (by rfl) ⟨407381, by rfl⟩ : syracuseStep 2172701 = 814763) (by norm_num)
theorem B2443061 : Blo 1447543 2443061 := bbase (se 5 (by rfl) ⟨114518, by rfl⟩ : syracuseStep 2443061 = 229037) (by norm_num)
theorem B2172725 : Blo 1447543 2172725 := bbase (se 5 (by rfl) ⟨101846, by rfl⟩ : syracuseStep 2172725 = 203693) (by norm_num)
theorem B2172749 : Blo 1447543 2172749 := bbase (se 3 (by rfl) ⟨407390, by rfl⟩ : syracuseStep 2172749 = 814781) (by norm_num)
theorem B5498725 : Blo 1447543 5498725 := bbase (se 4 (by rfl) ⟨515505, by rfl⟩ : syracuseStep 5498725 = 1031011) (by norm_num)
theorem B2172773 : Blo 1447543 2172773 := bbase (se 4 (by rfl) ⟨203697, by rfl⟩ : syracuseStep 2172773 = 407395) (by norm_num)
theorem B4122485 : Blo 1447543 4122485 := bbase (se 5 (by rfl) ⟨193241, by rfl⟩ : syracuseStep 4122485 = 386483) (by norm_num)
theorem B2172797 : Blo 1447543 2172797 := bbase (se 3 (by rfl) ⟨407399, by rfl⟩ : syracuseStep 2172797 = 814799) (by norm_num)
theorem B20875157 : Blo 1447543 20875157 := bbase (se 6 (by rfl) ⟨489261, by rfl⟩ : syracuseStep 20875157 = 978523) (by norm_num)
theorem B2172821 : Blo 1447543 2172821 := bbase (se 6 (by rfl) ⟨50925, by rfl⟩ : syracuseStep 2172821 = 101851) (by norm_num)
theorem B2320301 : Blo 1447543 2320301 := bbase (se 3 (by rfl) ⟨435056, by rfl⟩ : syracuseStep 2320301 = 870113) (by norm_num)
theorem B2172845 : Blo 1447543 2172845 := bbase (se 3 (by rfl) ⟨407408, by rfl⟩ : syracuseStep 2172845 = 814817) (by norm_num)
theorem B2443189 : Blo 1447543 2443189 := bbase (se 5 (by rfl) ⟨114524, by rfl⟩ : syracuseStep 2443189 = 229049) (by norm_num)
theorem B2172869 : Blo 1447543 2172869 := bbase (se 4 (by rfl) ⟨203706, by rfl⟩ : syracuseStep 2172869 = 407413) (by norm_num)
theorem B2172893 : Blo 1447543 2172893 := bbase (se 3 (by rfl) ⟨407417, by rfl⟩ : syracuseStep 2172893 = 814835) (by norm_num)
theorem B2172917 : Blo 1447543 2172917 := bbase (se 5 (by rfl) ⟨101855, by rfl⟩ : syracuseStep 2172917 = 203711) (by norm_num)
theorem B1468405 : Blo 1447543 1468405 := bbase (se 5 (by rfl) ⟨68831, by rfl⟩ : syracuseStep 1468405 = 137663) (by norm_num)
theorem B2443277 : Blo 1447543 2443277 := bbase (se 3 (by rfl) ⟨458114, by rfl⟩ : syracuseStep 2443277 = 916229) (by norm_num)
theorem B2172941 : Blo 1447543 2172941 := bbase (se 3 (by rfl) ⟨407426, by rfl⟩ : syracuseStep 2172941 = 814853) (by norm_num)
theorem B2172965 : Blo 1447543 2172965 := bbase (se 4 (by rfl) ⟨203715, by rfl⟩ : syracuseStep 2172965 = 407431) (by norm_num)
theorem B4122677 : Blo 1447543 4122677 := bbase (se 5 (by rfl) ⟨193250, by rfl⟩ : syracuseStep 4122677 = 386501) (by norm_num)
theorem B2172989 : Blo 1447543 2172989 := bbase (se 3 (by rfl) ⟨407435, by rfl⟩ : syracuseStep 2172989 = 814871) (by norm_num)
theorem B2173013 : Blo 1447543 2173013 := bbase (se 8 (by rfl) ⟨12732, by rfl⟩ : syracuseStep 2173013 = 25465) (by norm_num)
theorem B3917909 : Blo 1447543 3917909 := bbase (se 8 (by rfl) ⟨22956, by rfl⟩ : syracuseStep 3917909 = 45913) (by norm_num)
theorem B2173037 : Blo 1447543 2173037 := bbase (se 3 (by rfl) ⟨407444, by rfl⟩ : syracuseStep 2173037 = 814889) (by norm_num)
theorem B2173061 : Blo 1447543 2173061 := bbase (se 4 (by rfl) ⟨203724, by rfl⟩ : syracuseStep 2173061 = 407449) (by norm_num)
theorem B2443405 : Blo 1447543 2443405 := bbase (se 3 (by rfl) ⟨458138, by rfl⟩ : syracuseStep 2443405 = 916277) (by norm_num)
theorem B5499029 : Blo 1447543 5499029 := bbase (se 6 (by rfl) ⟨128883, by rfl⟩ : syracuseStep 5499029 = 257767) (by norm_num)
theorem B2173085 : Blo 1447543 2173085 := bbase (se 3 (by rfl) ⟨407453, by rfl⟩ : syracuseStep 2173085 = 814907) (by norm_num)
theorem B2173109 : Blo 1447543 2173109 := bbase (se 5 (by rfl) ⟨101864, by rfl⟩ : syracuseStep 2173109 = 203729) (by norm_num)
theorem B1673417 : Blo 1447543 1673417 := bbase (se 2 (by rfl) ⟨627531, by rfl⟩ : syracuseStep 1673417 = 1255063) (by norm_num)
theorem B2173133 : Blo 1447543 2173133 := bbase (se 3 (by rfl) ⟨407462, by rfl⟩ : syracuseStep 2173133 = 814925) (by norm_num)
theorem B2443493 : Blo 1447543 2443493 := bbase (se 4 (by rfl) ⟨229077, by rfl⟩ : syracuseStep 2443493 = 458155) (by norm_num)
theorem B2173157 : Blo 1447543 2173157 := bbase (se 4 (by rfl) ⟨203733, by rfl⟩ : syracuseStep 2173157 = 407467) (by norm_num)
theorem B6965477 : Blo 1447543 6965477 := bbase (se 4 (by rfl) ⟨653013, by rfl⟩ : syracuseStep 6965477 = 1306027) (by norm_num)
theorem B2173181 : Blo 1447543 2173181 := bbase (se 3 (by rfl) ⟨407471, by rfl⟩ : syracuseStep 2173181 = 814943) (by norm_num)
theorem B1566977 : Blo 1447543 1566977 := bbase (se 2 (by rfl) ⟨587616, by rfl⟩ : syracuseStep 1566977 = 1175233) (by norm_num)
theorem B2173205 : Blo 1447543 2173205 := bbase (se 6 (by rfl) ⟨50934, by rfl⟩ : syracuseStep 2173205 = 101869) (by norm_num)
theorem B1468697 : Blo 1447543 1468697 := bbase (se 2 (by rfl) ⟨550761, by rfl⟩ : syracuseStep 1468697 = 1101523) (by norm_num)
theorem B2173229 : Blo 1447543 2173229 := bbase (se 3 (by rfl) ⟨407480, by rfl⟩ : syracuseStep 2173229 = 814961) (by norm_num)
theorem B2173253 : Blo 1447543 2173253 := bbase (se 4 (by rfl) ⟨203742, by rfl⟩ : syracuseStep 2173253 = 407485) (by norm_num)
theorem B11741525 : Blo 1447543 11741525 := bbase (se 10 (by rfl) ⟨17199, by rfl⟩ : syracuseStep 11741525 = 34399) (by norm_num)
theorem B23816533 : Blo 1447543 23816533 := bbase (se 10 (by rfl) ⟨34887, by rfl⟩ : syracuseStep 23816533 = 69775) (by norm_num)
theorem B8251733 : Blo 1447543 8251733 := bbase (se 10 (by rfl) ⟨12087, by rfl⟩ : syracuseStep 8251733 = 24175) (by norm_num)
theorem B1739101 : Blo 1447543 1739101 := bbase (se 3 (by rfl) ⟨326081, by rfl⟩ : syracuseStep 1739101 = 652163) (by norm_num)
theorem B2173277 : Blo 1447543 2173277 := bbase (se 3 (by rfl) ⟨407489, by rfl⟩ : syracuseStep 2173277 = 814979) (by norm_num)
theorem B2443621 : Blo 1447543 2443621 := bbase (se 4 (by rfl) ⟨229089, by rfl⟩ : syracuseStep 2443621 = 458179) (by norm_num)
theorem B3664237 : Blo 1447543 3664237 := bbase (se 3 (by rfl) ⟨687044, by rfl⟩ : syracuseStep 3664237 = 1374089) (by norm_num)
theorem B7825781 : Blo 1447543 7825781 := bbase (se 5 (by rfl) ⟨366833, by rfl⟩ : syracuseStep 7825781 = 733667) (by norm_num)
theorem B2173301 : Blo 1447543 2173301 := bbase (se 5 (by rfl) ⟨101873, by rfl⟩ : syracuseStep 2173301 = 203747) (by norm_num)
theorem B2173325 : Blo 1447543 2173325 := bbase (se 3 (by rfl) ⟨407498, by rfl⟩ : syracuseStep 2173325 = 814997) (by norm_num)
theorem B2935205 : Blo 1447543 2935205 := bbase (se 4 (by rfl) ⟨275175, by rfl⟩ : syracuseStep 2935205 = 550351) (by norm_num)
theorem B2173349 : Blo 1447543 2173349 := bbase (se 4 (by rfl) ⟨203751, by rfl⟩ : syracuseStep 2173349 = 407503) (by norm_num)
theorem B4180405 : Blo 1447543 4180405 := bbase (se 5 (by rfl) ⟨195956, by rfl⟩ : syracuseStep 4180405 = 391913) (by norm_num)
theorem B9284021 : Blo 1447543 9284021 := bbase (se 5 (by rfl) ⟨435188, by rfl⟩ : syracuseStep 9284021 = 870377) (by norm_num)
theorem B2443709 : Blo 1447543 2443709 := bbase (se 3 (by rfl) ⟨458195, by rfl⟩ : syracuseStep 2443709 = 916391) (by norm_num)
theorem B2173373 : Blo 1447543 2173373 := bbase (se 3 (by rfl) ⟨407507, by rfl⟩ : syracuseStep 2173373 = 815015) (by norm_num)
theorem B2935253 : Blo 1447543 2935253 := bbase (se 7 (by rfl) ⟨34397, by rfl⟩ : syracuseStep 2935253 = 68795) (by norm_num)
theorem B2173397 : Blo 1447543 2173397 := bbase (se 7 (by rfl) ⟨25469, by rfl⟩ : syracuseStep 2173397 = 50939) (by norm_num)
theorem B3664349 : Blo 1447543 3664349 := bbase (se 3 (by rfl) ⟨687065, by rfl⟩ : syracuseStep 3664349 = 1374131) (by norm_num)
theorem B2173421 : Blo 1447543 2173421 := bbase (se 3 (by rfl) ⟨407516, by rfl⟩ : syracuseStep 2173421 = 815033) (by norm_num)
theorem B2173445 : Blo 1447543 2173445 := bbase (se 4 (by rfl) ⟨203760, by rfl⟩ : syracuseStep 2173445 = 407521) (by norm_num)
theorem B2173469 : Blo 1447543 2173469 := bbase (se 3 (by rfl) ⟨407525, by rfl⟩ : syracuseStep 2173469 = 815051) (by norm_num)
theorem B2320949 : Blo 1447543 2320949 := bbase (se 5 (by rfl) ⟨108794, by rfl⟩ : syracuseStep 2320949 = 217589) (by norm_num)
theorem B2173493 : Blo 1447543 2173493 := bbase (se 5 (by rfl) ⟨101882, by rfl⟩ : syracuseStep 2173493 = 203765) (by norm_num)
theorem B2443837 : Blo 1447543 2443837 := bbase (se 3 (by rfl) ⟨458219, by rfl⟩ : syracuseStep 2443837 = 916439) (by norm_num)
theorem B2173517 : Blo 1447543 2173517 := bbase (se 3 (by rfl) ⟨407534, by rfl⟩ : syracuseStep 2173517 = 815069) (by norm_num)
theorem B2173541 : Blo 1447543 2173541 := bbase (se 4 (by rfl) ⟨203769, by rfl⟩ : syracuseStep 2173541 = 407539) (by norm_num)
theorem B2173565 : Blo 1447543 2173565 := bbase (se 3 (by rfl) ⟨407543, by rfl⟩ : syracuseStep 2173565 = 815087) (by norm_num)
theorem B2443925 : Blo 1447543 2443925 := bbase (se 6 (by rfl) ⟨57279, by rfl⟩ : syracuseStep 2443925 = 114559) (by norm_num)
theorem B7334549 : Blo 1447543 7334549 := bbase (se 6 (by rfl) ⟨171903, by rfl⟩ : syracuseStep 7334549 = 343807) (by norm_num)
theorem B2173589 : Blo 1447543 2173589 := bbase (se 6 (by rfl) ⟨50943, by rfl⟩ : syracuseStep 2173589 = 101887) (by norm_num)
theorem B3664541 : Blo 1447543 3664541 := bbase (se 3 (by rfl) ⟨687101, by rfl⟩ : syracuseStep 3664541 = 1374203) (by norm_num)
theorem B2173613 : Blo 1447543 2173613 := bbase (se 3 (by rfl) ⟨407552, by rfl⟩ : syracuseStep 2173613 = 815105) (by norm_num)
theorem B2173637 : Blo 1447543 2173637 := bbase (se 4 (by rfl) ⟨203778, by rfl⟩ : syracuseStep 2173637 = 407557) (by norm_num)
theorem B4467413 : Blo 1447543 4467413 := bbase (se 7 (by rfl) ⟨52352, by rfl⟩ : syracuseStep 4467413 = 104705) (by norm_num)
theorem B2173661 : Blo 1447543 2173661 := bbase (se 3 (by rfl) ⟨407561, by rfl⟩ : syracuseStep 2173661 = 815123) (by norm_num)
theorem B2173685 : Blo 1447543 2173685 := bbase (se 5 (by rfl) ⟨101891, by rfl⟩ : syracuseStep 2173685 = 203783) (by norm_num)
theorem B2173709 : Blo 1447543 2173709 := bbase (se 3 (by rfl) ⟨407570, by rfl⟩ : syracuseStep 2173709 = 815141) (by norm_num)
theorem B2444053 : Blo 1447543 2444053 := bbase (se 6 (by rfl) ⟨57282, by rfl⟩ : syracuseStep 2444053 = 114565) (by norm_num)
theorem B2173733 : Blo 1447543 2173733 := bbase (se 4 (by rfl) ⟨203787, by rfl⟩ : syracuseStep 2173733 = 407575) (by norm_num)
theorem B2173757 : Blo 1447543 2173757 := bbase (se 3 (by rfl) ⟨407579, by rfl⟩ : syracuseStep 2173757 = 815159) (by norm_num)
theorem B5294917 : Blo 1447543 5294917 := bbase (se 4 (by rfl) ⟨496398, by rfl⟩ : syracuseStep 5294917 = 992797) (by norm_num)
theorem B2173781 : Blo 1447543 2173781 := bbase (se 9 (by rfl) ⟨6368, by rfl⟩ : syracuseStep 2173781 = 12737) (by norm_num)
theorem B2444141 : Blo 1447543 2444141 := bbase (se 3 (by rfl) ⟨458276, by rfl⟩ : syracuseStep 2444141 = 916553) (by norm_num)
theorem B2173805 : Blo 1447543 2173805 := bbase (se 3 (by rfl) ⟨407588, by rfl⟩ : syracuseStep 2173805 = 815177) (by norm_num)
theorem B1469297 : Blo 1447543 1469297 := bbase (se 2 (by rfl) ⟨550986, by rfl⟩ : syracuseStep 1469297 = 1101973) (by norm_num)
theorem B2173829 : Blo 1447543 2173829 := bbase (se 4 (by rfl) ⟨203796, by rfl⟩ : syracuseStep 2173829 = 407593) (by norm_num)
theorem B2173853 : Blo 1447543 2173853 := bbase (se 3 (by rfl) ⟨407597, by rfl⟩ : syracuseStep 2173853 = 815195) (by norm_num)
theorem B2173877 : Blo 1447543 2173877 := bbase (se 5 (by rfl) ⟨101900, by rfl⟩ : syracuseStep 2173877 = 203801) (by norm_num)
theorem B2173901 : Blo 1447543 2173901 := bbase (se 3 (by rfl) ⟨407606, by rfl⟩ : syracuseStep 2173901 = 815213) (by norm_num)
theorem B2173925 : Blo 1447543 2173925 := bbase (se 4 (by rfl) ⟨203805, by rfl⟩ : syracuseStep 2173925 = 407611) (by norm_num)
theorem B2444269 : Blo 1447543 2444269 := bbase (se 3 (by rfl) ⟨458300, by rfl⟩ : syracuseStep 2444269 = 916601) (by norm_num)
theorem B3664885 : Blo 1447543 3664885 := bbase (se 5 (by rfl) ⟨171791, by rfl⟩ : syracuseStep 3664885 = 343583) (by norm_num)
theorem B2173949 : Blo 1447543 2173949 := bbase (se 3 (by rfl) ⟨407615, by rfl⟩ : syracuseStep 2173949 = 815231) (by norm_num)
theorem B4123669 : Blo 1447543 4123669 := bbase (se 6 (by rfl) ⟨96648, by rfl⟩ : syracuseStep 4123669 = 193297) (by norm_num)
theorem B2173973 : Blo 1447543 2173973 := bbase (se 6 (by rfl) ⟨50952, by rfl⟩ : syracuseStep 2173973 = 101905) (by norm_num)
theorem B4885541 : Blo 1447543 4885541 := bbase (se 4 (by rfl) ⟨458019, by rfl⟩ : syracuseStep 4885541 = 916039) (by norm_num)
theorem B4639781 : Blo 1447543 4639781 := bbase (se 4 (by rfl) ⟨434979, by rfl⟩ : syracuseStep 4639781 = 869959) (by norm_num)
theorem B2173997 : Blo 1447543 2173997 := bbase (se 3 (by rfl) ⟨407624, by rfl⟩ : syracuseStep 2173997 = 815249) (by norm_num)
theorem B2444357 : Blo 1447543 2444357 := bbase (se 4 (by rfl) ⟨229158, by rfl⟩ : syracuseStep 2444357 = 458317) (by norm_num)
theorem B2174021 : Blo 1447543 2174021 := bbase (se 4 (by rfl) ⟨203814, by rfl⟩ : syracuseStep 2174021 = 407629) (by norm_num)
theorem B2935901 : Blo 1447543 2935901 := bbase (se 3 (by rfl) ⟨550481, by rfl⟩ : syracuseStep 2935901 = 1100963) (by norm_num)
theorem B2174045 : Blo 1447543 2174045 := bbase (se 3 (by rfl) ⟨407633, by rfl⟩ : syracuseStep 2174045 = 815267) (by norm_num)
theorem B3664997 : Blo 1447543 3664997 := bbase (se 4 (by rfl) ⟨343593, by rfl⟩ : syracuseStep 3664997 = 687187) (by norm_num)
theorem B2174069 : Blo 1447543 2174069 := bbase (se 5 (by rfl) ⟨101909, by rfl⟩ : syracuseStep 2174069 = 203819) (by norm_num)
theorem B2174093 : Blo 1447543 2174093 := bbase (se 3 (by rfl) ⟨407642, by rfl⟩ : syracuseStep 2174093 = 815285) (by norm_num)
theorem B2174117 : Blo 1447543 2174117 := bbase (se 4 (by rfl) ⟨203823, by rfl⟩ : syracuseStep 2174117 = 407647) (by norm_num)
theorem B2174141 : Blo 1447543 2174141 := bbase (se 3 (by rfl) ⟨407651, by rfl⟩ : syracuseStep 2174141 = 815303) (by norm_num)
theorem B2444485 : Blo 1447543 2444485 := bbase (se 4 (by rfl) ⟨229170, by rfl⟩ : syracuseStep 2444485 = 458341) (by norm_num)
theorem B1739981 : Blo 1447543 1739981 := bbase (se 3 (by rfl) ⟨326246, by rfl⟩ : syracuseStep 1739981 = 652493) (by norm_num)
theorem B2174165 : Blo 1447543 2174165 := bbase (se 7 (by rfl) ⟨25478, by rfl⟩ : syracuseStep 2174165 = 50957) (by norm_num)
theorem B2174189 : Blo 1447543 2174189 := bbase (se 3 (by rfl) ⟨407660, by rfl⟩ : syracuseStep 2174189 = 815321) (by norm_num)
theorem B2174213 : Blo 1447543 2174213 := bbase (se 4 (by rfl) ⟨203832, by rfl⟩ : syracuseStep 2174213 = 407665) (by norm_num)
theorem B2444573 : Blo 1447543 2444573 := bbase (se 3 (by rfl) ⟨458357, by rfl⟩ : syracuseStep 2444573 = 916715) (by norm_num)
theorem B2174237 : Blo 1447543 2174237 := bbase (se 3 (by rfl) ⟨407669, by rfl⟩ : syracuseStep 2174237 = 815339) (by norm_num)
theorem B3665189 : Blo 1447543 3665189 := bbase (se 4 (by rfl) ⟨343611, by rfl⟩ : syracuseStep 3665189 = 687223) (by norm_num)
theorem B5221685 : Blo 1447543 5221685 := bbase (se 5 (by rfl) ⟨244766, by rfl⟩ : syracuseStep 5221685 = 489533) (by norm_num)
theorem B2788661 : Blo 1447543 2788661 := bbase (se 5 (by rfl) ⟨130718, by rfl⟩ : syracuseStep 2788661 = 261437) (by norm_num)
theorem B2174261 : Blo 1447543 2174261 := bbase (se 5 (by rfl) ⟨101918, by rfl⟩ : syracuseStep 2174261 = 203837) (by norm_num)
theorem B2174285 : Blo 1447543 2174285 := bbase (se 3 (by rfl) ⟨407678, by rfl⟩ : syracuseStep 2174285 = 815357) (by norm_num)
theorem B11750741 : Blo 1447543 11750741 := bbase (se 11 (by rfl) ⟨8606, by rfl⟩ : syracuseStep 11750741 = 17213) (by norm_num)
theorem B2174309 : Blo 1447543 2174309 := bbase (se 4 (by rfl) ⟨203841, by rfl⟩ : syracuseStep 2174309 = 407683) (by norm_num)
theorem B2444701 : Blo 1447543 2444701 := bbase (se 3 (by rfl) ⟨458381, by rfl⟩ : syracuseStep 2444701 = 916763) (by norm_num)
theorem B4885973 : Blo 1447543 4885973 := bbase (se 7 (by rfl) ⟨57257, by rfl⟩ : syracuseStep 4885973 = 114515) (by norm_num)
theorem B2444789 : Blo 1447543 2444789 := bbase (se 5 (by rfl) ⟨114599, by rfl⟩ : syracuseStep 2444789 = 229199) (by norm_num)
theorem B3092069 : Blo 1447543 3092069 := bbase (se 4 (by rfl) ⟨289881, by rfl⟩ : syracuseStep 3092069 = 579763) (by norm_num)
theorem B2444917 : Blo 1447543 2444917 := bbase (se 5 (by rfl) ⟨114605, by rfl⟩ : syracuseStep 2444917 = 229211) (by norm_num)
theorem B3665533 : Blo 1447543 3665533 := bbase (se 3 (by rfl) ⟨687287, by rfl⟩ : syracuseStep 3665533 = 1374575) (by norm_num)
theorem B10440373 : Blo 1447543 10440373 := bbase (se 5 (by rfl) ⟨489392, by rfl⟩ : syracuseStep 10440373 = 978785) (by norm_num)
theorem B1740485 : Blo 1447543 1740485 := bbase (se 4 (by rfl) ⟨163170, by rfl⟩ : syracuseStep 1740485 = 326341) (by norm_num)
theorem B2445005 : Blo 1447543 2445005 := bbase (se 3 (by rfl) ⟨458438, by rfl⟩ : syracuseStep 2445005 = 916877) (by norm_num)
theorem B3665645 : Blo 1447543 3665645 := bbase (se 3 (by rfl) ⟨687308, by rfl⟩ : syracuseStep 3665645 = 1374617) (by norm_num)
theorem B3092213 : Blo 1447543 3092213 := bbase (se 5 (by rfl) ⟨144947, by rfl⟩ : syracuseStep 3092213 = 289895) (by norm_num)
theorem B1740533 : Blo 1447543 1740533 := bbase (se 5 (by rfl) ⟨81587, by rfl⟩ : syracuseStep 1740533 = 163175) (by norm_num)
theorem B2477893 : Blo 1447543 2477893 := bbase (se 4 (by rfl) ⟨232302, by rfl⟩ : syracuseStep 2477893 = 464605) (by norm_num)
theorem B2445133 : Blo 1447543 2445133 := bbase (se 3 (by rfl) ⟨458462, by rfl⟩ : syracuseStep 2445133 = 916925) (by norm_num)
theorem B2748269 : Blo 1447543 2748269 := bbase (se 3 (by rfl) ⟨515300, by rfl⟩ : syracuseStep 2748269 = 1030601) (by norm_num)
theorem B4886405 : Blo 1447543 4886405 := bbase (se 4 (by rfl) ⟨458100, by rfl⟩ : syracuseStep 4886405 = 916201) (by norm_num)
theorem B2445221 : Blo 1447543 2445221 := bbase (se 4 (by rfl) ⟨229239, by rfl⟩ : syracuseStep 2445221 = 458479) (by norm_num)
theorem B7335845 : Blo 1447543 7335845 := bbase (se 4 (by rfl) ⟨687735, by rfl⟩ : syracuseStep 7335845 = 1375471) (by norm_num)
theorem B3665837 : Blo 1447543 3665837 := bbase (se 3 (by rfl) ⟨687344, by rfl⟩ : syracuseStep 3665837 = 1374689) (by norm_num)
theorem B3715013 : Blo 1447543 3715013 := bbase (se 4 (by rfl) ⟨348282, by rfl⟩ : syracuseStep 3715013 = 696565) (by norm_num)
theorem B35229653 : Blo 1447543 35229653 := bbase (se 7 (by rfl) ⟨412847, by rfl⟩ : syracuseStep 35229653 = 825695) (by norm_num)
theorem B1740793 : Blo 1447543 1740793 := bbase (se 2 (by rfl) ⟨652797, by rfl⟩ : syracuseStep 1740793 = 1305595) (by norm_num)
theorem B2748421 : Blo 1447543 2748421 := bbase (se 4 (by rfl) ⟨257664, by rfl⟩ : syracuseStep 2748421 = 515329) (by norm_num)
theorem B2445349 : Blo 1447543 2445349 := bbase (se 4 (by rfl) ⟨229251, by rfl⟩ : syracuseStep 2445349 = 458503) (by norm_num)
theorem B3092573 : Blo 1447543 3092573 := bbase (se 3 (by rfl) ⟨579857, by rfl⟩ : syracuseStep 3092573 = 1159715) (by norm_num)
theorem B4124773 : Blo 1447543 4124773 := bbase (se 4 (by rfl) ⟨386697, by rfl⟩ : syracuseStep 4124773 = 773395) (by norm_num)
theorem B2445437 : Blo 1447543 2445437 := bbase (se 3 (by rfl) ⟨458519, by rfl⟩ : syracuseStep 2445437 = 917039) (by norm_num)
theorem B4526293 : Blo 1447543 4526293 := bbase (se 7 (by rfl) ⟨53042, by rfl⟩ : syracuseStep 4526293 = 106085) (by norm_num)
theorem B5501141 : Blo 1447543 5501141 := bbase (se 7 (by rfl) ⟨64466, by rfl⟩ : syracuseStep 5501141 = 128933) (by norm_num)
theorem B8589557 : Blo 1447543 8589557 := bbase (se 5 (by rfl) ⟨402635, by rfl⟩ : syracuseStep 8589557 = 805271) (by norm_num)
theorem B2445565 : Blo 1447543 2445565 := bbase (se 3 (by rfl) ⟨458543, by rfl⟩ : syracuseStep 2445565 = 917087) (by norm_num)
theorem B1741057 : Blo 1447543 1741057 := bbase (se 2 (by rfl) ⟨652896, by rfl⟩ : syracuseStep 1741057 = 1305793) (by norm_num)
theorem B3666181 : Blo 1447543 3666181 := bbase (se 4 (by rfl) ⟨343704, by rfl⟩ : syracuseStep 3666181 = 687409) (by norm_num)
theorem B1650989 : Blo 1447543 1650989 := bbase (se 3 (by rfl) ⟨309560, by rfl⟩ : syracuseStep 1650989 = 619121) (by norm_num)
theorem B2748725 : Blo 1447543 2748725 := bbase (se 5 (by rfl) ⟨128846, by rfl⟩ : syracuseStep 2748725 = 257693) (by norm_num)
theorem B4886837 : Blo 1447543 4886837 := bbase (se 5 (by rfl) ⟨229070, by rfl⟩ : syracuseStep 4886837 = 458141) (by norm_num)
theorem B4641077 : Blo 1447543 4641077 := bbase (se 5 (by rfl) ⟨217550, by rfl⟩ : syracuseStep 4641077 = 435101) (by norm_num)
theorem B2445653 : Blo 1447543 2445653 := bbase (se 10 (by rfl) ⟨3582, by rfl⟩ : syracuseStep 2445653 = 7165) (by norm_num)
theorem B3666293 : Blo 1447543 3666293 := bbase (se 5 (by rfl) ⟨171857, by rfl⟩ : syracuseStep 3666293 = 343715) (by norm_num)
theorem B1741177 : Blo 1447543 1741177 := bbase (se 2 (by rfl) ⟨652941, by rfl⟩ : syracuseStep 1741177 = 1305883) (by norm_num)
theorem B7942549 : Blo 1447543 7942549 := bbase (se 6 (by rfl) ⟨186153, by rfl⟩ : syracuseStep 7942549 = 372307) (by norm_num)
theorem B2445781 : Blo 1447543 2445781 := bbase (se 7 (by rfl) ⟨28661, by rfl⟩ : syracuseStep 2445781 = 57323) (by norm_num)
theorem B5501429 : Blo 1447543 5501429 := bbase (se 5 (by rfl) ⟨257879, by rfl⟩ : syracuseStep 5501429 = 515759) (by norm_num)
theorem B9277973 : Blo 1447543 9277973 := bbase (se 6 (by rfl) ⟨217452, by rfl⟩ : syracuseStep 9277973 = 434905) (by norm_num)
theorem B6189605 : Blo 1447543 6189605 := bbase (se 4 (by rfl) ⟨580275, by rfl⟩ : syracuseStep 6189605 = 1160551) (by norm_num)
theorem B2445869 : Blo 1447543 2445869 := bbase (se 3 (by rfl) ⟨458600, by rfl⟩ : syracuseStep 2445869 = 917201) (by norm_num)
theorem B3666485 : Blo 1447543 3666485 := bbase (se 5 (by rfl) ⟨171866, by rfl⟩ : syracuseStep 3666485 = 343733) (by norm_num)
theorem B2609741 : Blo 1447543 2609741 := bbase (se 3 (by rfl) ⟨489326, by rfl⟩ : syracuseStep 2609741 = 978653) (by norm_num)
theorem B3256973 : Blo 1447543 3256973 := bbase (se 3 (by rfl) ⟨610682, by rfl⟩ : syracuseStep 3256973 = 1221365) (by norm_num)
theorem B5870245 : Blo 1447543 5870245 := bbase (se 4 (by rfl) ⟨550335, by rfl⟩ : syracuseStep 5870245 = 1100671) (by norm_num)
theorem B2445997 : Blo 1447543 2445997 := bbase (se 3 (by rfl) ⟨458624, by rfl⟩ : syracuseStep 2445997 = 917249) (by norm_num)
theorem B3257045 : Blo 1447543 3257045 := bbase (se 7 (by rfl) ⟨38168, by rfl⟩ : syracuseStep 3257045 = 76337) (by norm_num)
theorem B7533269 : Blo 1447543 7533269 := bbase (se 7 (by rfl) ⟨88280, by rfl⟩ : syracuseStep 7533269 = 176561) (by norm_num)
theorem B4887269 : Blo 1447543 4887269 := bbase (se 4 (by rfl) ⟨458181, by rfl⟩ : syracuseStep 4887269 = 916363) (by norm_num)
theorem B1651441 : Blo 1447543 1651441 := bbase (se 2 (by rfl) ⟨619290, by rfl⟩ : syracuseStep 1651441 = 1238581) (by norm_num)
theorem B2446085 : Blo 1447543 2446085 := bbase (se 4 (by rfl) ⟨229320, by rfl⟩ : syracuseStep 2446085 = 458641) (by norm_num)
theorem B3257117 : Blo 1447543 3257117 := bbase (se 3 (by rfl) ⟨610709, by rfl⟩ : syracuseStep 3257117 = 1221419) (by norm_num)
theorem B3257189 : Blo 1447543 3257189 := bbase (se 4 (by rfl) ⟨305361, by rfl⟩ : syracuseStep 3257189 = 610723) (by norm_num)
theorem B2683757 : Blo 1447543 2683757 := bbase (se 3 (by rfl) ⟨503204, by rfl⟩ : syracuseStep 2683757 = 1006409) (by norm_num)
theorem B3666829 : Blo 1447543 3666829 := bbase (se 3 (by rfl) ⟨687530, by rfl⟩ : syracuseStep 3666829 = 1375061) (by norm_num)
theorem B3257261 : Blo 1447543 3257261 := bbase (se 3 (by rfl) ⟨610736, by rfl⟩ : syracuseStep 3257261 = 1221473) (by norm_num)
theorem B3093461 : Blo 1447543 3093461 := bbase (se 7 (by rfl) ⟨36251, by rfl⟩ : syracuseStep 3093461 = 72503) (by norm_num)
theorem B2061293 : Blo 1447543 2061293 := bbase (se 3 (by rfl) ⟨386492, by rfl⟩ : syracuseStep 2061293 = 772985) (by norm_num)
theorem B3257333 : Blo 1447543 3257333 := bbase (se 5 (by rfl) ⟨152687, by rfl⟩ : syracuseStep 3257333 = 305375) (by norm_num)
theorem B3666941 : Blo 1447543 3666941 := bbase (se 3 (by rfl) ⟨687551, by rfl⟩ : syracuseStep 3666941 = 1375103) (by norm_num)
theorem B2749477 : Blo 1447543 2749477 := bbase (se 4 (by rfl) ⟨257763, by rfl⟩ : syracuseStep 2749477 = 515527) (by norm_num)
theorem B3257405 : Blo 1447543 3257405 := bbase (se 3 (by rfl) ⟨610763, by rfl⟩ : syracuseStep 3257405 = 1221527) (by norm_num)
theorem B8246357 : Blo 1447543 8246357 := bbase (se 8 (by rfl) ⟨48318, by rfl⟩ : syracuseStep 8246357 = 96637) (by norm_num)
theorem B1832053 : Blo 1447543 1832053 := bbase (se 5 (by rfl) ⟨85877, by rfl⟩ : syracuseStep 1832053 = 171755) (by norm_num)
theorem B3257477 : Blo 1447543 3257477 := bbase (se 4 (by rfl) ⟨305388, by rfl⟩ : syracuseStep 3257477 = 610777) (by norm_num)
theorem B4887701 : Blo 1447543 4887701 := bbase (se 6 (by rfl) ⟨114555, by rfl⟩ : syracuseStep 4887701 = 229111) (by norm_num)
theorem B2749621 : Blo 1447543 2749621 := bbase (se 5 (by rfl) ⟨128888, by rfl⟩ : syracuseStep 2749621 = 257777) (by norm_num)
theorem B7337141 : Blo 1447543 7337141 := bbase (se 5 (by rfl) ⟨343928, by rfl⟩ : syracuseStep 7337141 = 687857) (by norm_num)
theorem B3667133 : Blo 1447543 3667133 := bbase (se 3 (by rfl) ⟨687587, by rfl⟩ : syracuseStep 3667133 = 1375175) (by norm_num)
theorem B6960325 : Blo 1447543 6960325 := bbase (se 4 (by rfl) ⟨652530, by rfl⟩ : syracuseStep 6960325 = 1305061) (by norm_num)
theorem B3257549 : Blo 1447543 3257549 := bbase (se 3 (by rfl) ⟨610790, by rfl⟩ : syracuseStep 3257549 = 1221581) (by norm_num)
theorem B3093709 : Blo 1447543 3093709 := bbase (se 3 (by rfl) ⟨580070, by rfl⟩ : syracuseStep 3093709 = 1160141) (by norm_num)
theorem B1832149 : Blo 1447543 1832149 := bbase (se 7 (by rfl) ⟨21470, by rfl⟩ : syracuseStep 1832149 = 42941) (by norm_num)
theorem B3257621 : Blo 1447543 3257621 := bbase (se 6 (by rfl) ⟨76350, by rfl⟩ : syracuseStep 3257621 = 152701) (by norm_num)
theorem B2479405 : Blo 1447543 2479405 := bbase (se 3 (by rfl) ⟨464888, by rfl⟩ : syracuseStep 2479405 = 929777) (by norm_num)
theorem B2749781 : Blo 1447543 2749781 := bbase (se 13 (by rfl) ⟨503, by rfl⟩ : syracuseStep 2749781 = 1007) (by norm_num)
theorem B3257693 : Blo 1447543 3257693 := bbase (se 3 (by rfl) ⟨610817, by rfl⟩ : syracuseStep 3257693 = 1221635) (by norm_num)
theorem B1652065 : Blo 1447543 1652065 := bbase (se 2 (by rfl) ⟨619524, by rfl⟩ : syracuseStep 1652065 = 1239049) (by norm_num)
theorem B12375413 : Blo 1447543 12375413 := bbase (se 5 (by rfl) ⟨580097, by rfl⟩ : syracuseStep 12375413 = 1160195) (by norm_num)
theorem B1832321 : Blo 1447543 1832321 := bbase (se 2 (by rfl) ⟨687120, by rfl⟩ : syracuseStep 1832321 = 1374241) (by norm_num)
theorem B4404629 : Blo 1447543 4404629 := bbase (se 6 (by rfl) ⟨103233, by rfl⟩ : syracuseStep 4404629 = 206467) (by norm_num)
theorem B21755285 : Blo 1447543 21755285 := bbase (se 6 (by rfl) ⟨509889, by rfl⟩ : syracuseStep 21755285 = 1019779) (by norm_num)
theorem B3257765 : Blo 1447543 3257765 := bbase (se 4 (by rfl) ⟨305415, by rfl⟩ : syracuseStep 3257765 = 610831) (by norm_num)
theorem B11007413 : Blo 1447543 11007413 := bbase (se 5 (by rfl) ⟨515972, by rfl⟩ : syracuseStep 11007413 = 1031945) (by norm_num)
theorem B1832377 : Blo 1447543 1832377 := bbase (se 2 (by rfl) ⟨687141, by rfl⟩ : syracuseStep 1832377 = 1374283) (by norm_num)
theorem B2749925 : Blo 1447543 2749925 := bbase (se 4 (by rfl) ⟨257805, by rfl⟩ : syracuseStep 2749925 = 515611) (by norm_num)
theorem B3257837 : Blo 1447543 3257837 := bbase (se 3 (by rfl) ⟨610844, by rfl⟩ : syracuseStep 3257837 = 1221689) (by norm_num)
theorem B12367349 : Blo 1447543 12367349 := bbase (se 5 (by rfl) ⟨579719, by rfl⟩ : syracuseStep 12367349 = 1159439) (by norm_num)
theorem B3667477 : Blo 1447543 3667477 := bbase (se 6 (by rfl) ⟨85956, by rfl⟩ : syracuseStep 3667477 = 171913) (by norm_num)
theorem B6190613 : Blo 1447543 6190613 := bbase (se 6 (by rfl) ⟨145092, by rfl⟩ : syracuseStep 6190613 = 290185) (by norm_num)
theorem B1832473 : Blo 1447543 1832473 := bbase (se 2 (by rfl) ⟨687177, by rfl⟩ : syracuseStep 1832473 = 1374355) (by norm_num)
theorem B3257909 : Blo 1447543 3257909 := bbase (se 5 (by rfl) ⟨152714, by rfl⟩ : syracuseStep 3257909 = 305429) (by norm_num)
theorem B4888133 : Blo 1447543 4888133 := bbase (se 4 (by rfl) ⟨458262, by rfl⟩ : syracuseStep 4888133 = 916525) (by norm_num)
theorem B4126277 : Blo 1447543 4126277 := bbase (se 4 (by rfl) ⟨386838, by rfl⟩ : syracuseStep 4126277 = 773677) (by norm_num)
theorem B7329365 : Blo 1447543 7329365 := bbase (se 8 (by rfl) ⟨42945, by rfl⟩ : syracuseStep 7329365 = 85891) (by norm_num)
theorem B3479125 : Blo 1447543 3479125 := bbase (se 8 (by rfl) ⟨20385, by rfl⟩ : syracuseStep 3479125 = 40771) (by norm_num)
theorem B3257981 : Blo 1447543 3257981 := bbase (se 3 (by rfl) ⟨610871, by rfl⟩ : syracuseStep 3257981 = 1221743) (by norm_num)
theorem B3667589 : Blo 1447543 3667589 := bbase (se 4 (by rfl) ⟨343836, by rfl⟩ : syracuseStep 3667589 = 687673) (by norm_num)
theorem B5502613 : Blo 1447543 5502613 := bbase (se 6 (by rfl) ⟨128967, by rfl⟩ : syracuseStep 5502613 = 257935) (by norm_num)
theorem B3479221 : Blo 1447543 3479221 := bbase (se 5 (by rfl) ⟨163088, by rfl⟩ : syracuseStep 3479221 = 326177) (by norm_num)
theorem B1832645 : Blo 1447543 1832645 := bbase (se 4 (by rfl) ⟨171810, by rfl⟩ : syracuseStep 1832645 = 343621) (by norm_num)
theorem B3258053 : Blo 1447543 3258053 := bbase (se 4 (by rfl) ⟨305442, by rfl⟩ : syracuseStep 3258053 = 610885) (by norm_num)
theorem B3094213 : Blo 1447543 3094213 := bbase (se 4 (by rfl) ⟨290082, by rfl⟩ : syracuseStep 3094213 = 580165) (by norm_num)
theorem B2062045 : Blo 1447543 2062045 := bbase (se 3 (by rfl) ⟨386633, by rfl⟩ : syracuseStep 2062045 = 773267) (by norm_num)
theorem B1832701 : Blo 1447543 1832701 := bbase (se 3 (by rfl) ⟨343631, by rfl⟩ : syracuseStep 1832701 = 687263) (by norm_num)
theorem B2750213 : Blo 1447543 2750213 := bbase (se 4 (by rfl) ⟨257832, by rfl⟩ : syracuseStep 2750213 = 515665) (by norm_num)
theorem B3258125 : Blo 1447543 3258125 := bbase (se 3 (by rfl) ⟨610898, by rfl⟩ : syracuseStep 3258125 = 1221797) (by norm_num)
theorem B1546013 : Blo 1447543 1546013 := bbase (se 3 (by rfl) ⟨289877, by rfl⟩ : syracuseStep 1546013 = 579755) (by norm_num)
theorem B3667781 : Blo 1447543 3667781 := bbase (se 4 (by rfl) ⟨343854, by rfl⟩ : syracuseStep 3667781 = 687709) (by norm_num)
theorem B3258197 : Blo 1447543 3258197 := bbase (se 9 (by rfl) ⟨9545, by rfl⟩ : syracuseStep 3258197 = 19091) (by norm_num)
theorem B10999637 : Blo 1447543 10999637 := bbase (se 9 (by rfl) ⟨32225, by rfl⟩ : syracuseStep 10999637 = 64451) (by norm_num)
theorem B1832797 : Blo 1447543 1832797 := bbase (se 3 (by rfl) ⟨343649, by rfl⟩ : syracuseStep 1832797 = 687299) (by norm_num)
theorem B2611045 : Blo 1447543 2611045 := bbase (se 4 (by rfl) ⟨244785, by rfl⟩ : syracuseStep 2611045 = 489571) (by norm_num)
theorem B1652609 : Blo 1447543 1652609 := bbase (se 2 (by rfl) ⟨619728, by rfl⟩ : syracuseStep 1652609 = 1239457) (by norm_num)
theorem B3258269 : Blo 1447543 3258269 := bbase (se 3 (by rfl) ⟨610925, by rfl⟩ : syracuseStep 3258269 = 1221851) (by norm_num)
theorem B2750365 : Blo 1447543 2750365 := bbase (se 3 (by rfl) ⟨515693, by rfl⟩ : syracuseStep 2750365 = 1031387) (by norm_num)
theorem B5502917 : Blo 1447543 5502917 := bbase (se 4 (by rfl) ⟨515898, by rfl⟩ : syracuseStep 5502917 = 1031797) (by norm_num)
theorem B7436245 : Blo 1447543 7436245 := bbase (se 7 (by rfl) ⟨87143, by rfl⟩ : syracuseStep 7436245 = 174287) (by norm_num)
theorem B3258341 : Blo 1447543 3258341 := bbase (se 4 (by rfl) ⟨305469, by rfl⟩ : syracuseStep 3258341 = 610939) (by norm_num)
theorem B4888565 : Blo 1447543 4888565 := bbase (se 5 (by rfl) ⟨229151, by rfl⟩ : syracuseStep 4888565 = 458303) (by norm_num)
theorem B1832969 : Blo 1447543 1832969 := bbase (se 2 (by rfl) ⟨687363, by rfl⟩ : syracuseStep 1832969 = 1374727) (by norm_num)
theorem B3258413 : Blo 1447543 3258413 := bbase (se 3 (by rfl) ⟨610952, by rfl⟩ : syracuseStep 3258413 = 1221905) (by norm_num)
theorem B2611261 : Blo 1447543 2611261 := bbase (se 3 (by rfl) ⟨489611, by rfl⟩ : syracuseStep 2611261 = 979223) (by norm_num)
theorem B1833025 : Blo 1447543 1833025 := bbase (se 2 (by rfl) ⟨687384, by rfl⟩ : syracuseStep 1833025 = 1374769) (by norm_num)
theorem B3135581 : Blo 1447543 3135581 := bbase (se 3 (by rfl) ⟨587921, by rfl⟩ : syracuseStep 3135581 = 1175843) (by norm_num)
theorem B4954229 : Blo 1447543 4954229 := bbase (se 5 (by rfl) ⟨232229, by rfl⟩ : syracuseStep 4954229 = 464459) (by norm_num)
theorem B3258485 : Blo 1447543 3258485 := bbase (se 5 (by rfl) ⟨152741, by rfl⟩ : syracuseStep 3258485 = 305483) (by norm_num)
theorem B4642933 : Blo 1447543 4642933 := bbase (se 5 (by rfl) ⟨217637, by rfl⟩ : syracuseStep 4642933 = 435275) (by norm_num)
theorem B3668125 : Blo 1447543 3668125 := bbase (se 3 (by rfl) ⟨687773, by rfl⟩ : syracuseStep 3668125 = 1375547) (by norm_num)
theorem B1833121 : Blo 1447543 1833121 := bbase (se 2 (by rfl) ⟨687420, by rfl⟩ : syracuseStep 1833121 = 1374841) (by norm_num)
theorem B3258557 : Blo 1447543 3258557 := bbase (se 3 (by rfl) ⟨610979, by rfl⟩ : syracuseStep 3258557 = 1221959) (by norm_num)
theorem B2750669 : Blo 1447543 2750669 := bbase (se 3 (by rfl) ⟨515750, by rfl⟩ : syracuseStep 2750669 = 1031501) (by norm_num)
theorem B1546457 : Blo 1447543 1546457 := bbase (se 2 (by rfl) ⟨579921, by rfl⟩ : syracuseStep 1546457 = 1159843) (by norm_num)
theorem B8247541 : Blo 1447543 8247541 := bbase (se 5 (by rfl) ⟨386603, by rfl⟩ : syracuseStep 8247541 = 773207) (by norm_num)
theorem B3258629 : Blo 1447543 3258629 := bbase (se 4 (by rfl) ⟨305496, by rfl⟩ : syracuseStep 3258629 = 610993) (by norm_num)
theorem B3668237 : Blo 1447543 3668237 := bbase (se 3 (by rfl) ⟨687794, by rfl⟩ : syracuseStep 3668237 = 1375589) (by norm_num)
theorem B3258701 : Blo 1447543 3258701 := bbase (se 3 (by rfl) ⟨611006, by rfl⟩ : syracuseStep 3258701 = 1222013) (by norm_num)
theorem B1833293 : Blo 1447543 1833293 := bbase (se 3 (by rfl) ⟨343742, by rfl⟩ : syracuseStep 1833293 = 687485) (by norm_num)
theorem B1628509 : Blo 1447543 1628509 := bbase (se 3 (by rfl) ⟨305345, by rfl⟩ : syracuseStep 1628509 = 610691) (by norm_num)
theorem B1628545 : Blo 1447543 1628545 := bbase (se 2 (by rfl) ⟨610704, by rfl⟩ : syracuseStep 1628545 = 1221409) (by norm_num)
theorem B1833349 : Blo 1447543 1833349 := bbase (se 4 (by rfl) ⟨171876, by rfl⟩ : syracuseStep 1833349 = 343753) (by norm_num)
theorem B6183317 : Blo 1447543 6183317 := bbase (se 6 (by rfl) ⟨144921, by rfl⟩ : syracuseStep 6183317 = 289843) (by norm_num)
theorem B3258773 : Blo 1447543 3258773 := bbase (se 6 (by rfl) ⟨76377, by rfl⟩ : syracuseStep 3258773 = 152755) (by norm_num)
theorem B1628581 : Blo 1447543 1628581 := bbase (se 4 (by rfl) ⟨152679, by rfl⟩ : syracuseStep 1628581 = 305359) (by norm_num)
theorem B4888997 : Blo 1447543 4888997 := bbase (se 4 (by rfl) ⟨458343, by rfl⟩ : syracuseStep 4888997 = 916687) (by norm_num)
theorem B1628617 : Blo 1447543 1628617 := bbase (se 2 (by rfl) ⟨610731, by rfl⟩ : syracuseStep 1628617 = 1221463) (by norm_num)
theorem B3668429 : Blo 1447543 3668429 := bbase (se 3 (by rfl) ⟨687830, by rfl⟩ : syracuseStep 3668429 = 1375661) (by norm_num)
theorem B1546705 : Blo 1447543 1546705 := bbase (se 2 (by rfl) ⟨580014, by rfl⟩ : syracuseStep 1546705 = 1160029) (by norm_num)
theorem B3258845 : Blo 1447543 3258845 := bbase (se 3 (by rfl) ⟨611033, by rfl⟩ : syracuseStep 3258845 = 1222067) (by norm_num)
theorem B1833445 : Blo 1447543 1833445 := bbase (se 4 (by rfl) ⟨171885, by rfl⟩ : syracuseStep 1833445 = 343771) (by norm_num)
theorem B1628653 : Blo 1447543 1628653 := bbase (se 3 (by rfl) ⟨305372, by rfl⟩ : syracuseStep 1628653 = 610745) (by norm_num)
theorem B2062837 : Blo 1447543 2062837 := bbase (se 5 (by rfl) ⟨96695, by rfl⟩ : syracuseStep 2062837 = 193391) (by norm_num)
theorem B1628689 : Blo 1447543 1628689 := bbase (se 2 (by rfl) ⟨610758, by rfl⟩ : syracuseStep 1628689 = 1221517) (by norm_num)
theorem B3258917 : Blo 1447543 3258917 := bbase (se 4 (by rfl) ⟨305523, by rfl⟩ : syracuseStep 3258917 = 611047) (by norm_num)
theorem B1628725 : Blo 1447543 1628725 := bbase (se 5 (by rfl) ⟨76346, by rfl⟩ : syracuseStep 1628725 = 152693) (by norm_num)
theorem B3095101 : Blo 1447543 3095101 := bbase (se 3 (by rfl) ⟨580331, by rfl⟩ : syracuseStep 3095101 = 1160663) (by norm_num)
theorem B1628761 : Blo 1447543 1628761 := bbase (se 2 (by rfl) ⟨610785, by rfl⟩ : syracuseStep 1628761 = 1221571) (by norm_num)
theorem B3258989 : Blo 1447543 3258989 := bbase (se 3 (by rfl) ⟨611060, by rfl⟩ : syracuseStep 3258989 = 1222121) (by norm_num)
theorem B1628797 : Blo 1447543 1628797 := bbase (se 3 (by rfl) ⟨305399, by rfl⟩ : syracuseStep 1628797 = 610799) (by norm_num)
theorem B1833617 : Blo 1447543 1833617 := bbase (se 2 (by rfl) ⟨687606, by rfl⟩ : syracuseStep 1833617 = 1375213) (by norm_num)
theorem B1628833 : Blo 1447543 1628833 := bbase (se 2 (by rfl) ⟨610812, by rfl⟩ : syracuseStep 1628833 = 1221625) (by norm_num)
theorem B3259061 : Blo 1447543 3259061 := bbase (se 5 (by rfl) ⟨152768, by rfl⟩ : syracuseStep 3259061 = 305537) (by norm_num)
theorem B1628869 : Blo 1447543 1628869 := bbase (se 4 (by rfl) ⟨152706, by rfl⟩ : syracuseStep 1628869 = 305413) (by norm_num)
theorem B1833673 : Blo 1447543 1833673 := bbase (se 2 (by rfl) ⟨687627, by rfl⟩ : syracuseStep 1833673 = 1375255) (by norm_num)
theorem B1628905 : Blo 1447543 1628905 := bbase (se 2 (by rfl) ⟨610839, by rfl⟩ : syracuseStep 1628905 = 1221679) (by norm_num)
theorem B3480317 : Blo 1447543 3480317 := bbase (se 3 (by rfl) ⟨652559, by rfl⟩ : syracuseStep 3480317 = 1305119) (by norm_num)
theorem B3259133 : Blo 1447543 3259133 := bbase (se 3 (by rfl) ⟨611087, by rfl⟩ : syracuseStep 3259133 = 1222175) (by norm_num)
theorem B1628941 : Blo 1447543 1628941 := bbase (se 3 (by rfl) ⟨305426, by rfl⟩ : syracuseStep 1628941 = 610853) (by norm_num)
theorem B3668773 : Blo 1447543 3668773 := bbase (se 4 (by rfl) ⟨343947, by rfl⟩ : syracuseStep 3668773 = 687895) (by norm_num)
theorem B1833769 : Blo 1447543 1833769 := bbase (se 2 (by rfl) ⟨687663, by rfl⟩ : syracuseStep 1833769 = 1375327) (by norm_num)
theorem B1628977 : Blo 1447543 1628977 := bbase (se 2 (by rfl) ⟨610866, by rfl⟩ : syracuseStep 1628977 = 1221733) (by norm_num)
theorem B7060277 : Blo 1447543 7060277 := bbase (se 5 (by rfl) ⟨330950, by rfl⟩ : syracuseStep 7060277 = 661901) (by norm_num)
theorem B3259205 : Blo 1447543 3259205 := bbase (se 4 (by rfl) ⟨305550, by rfl⟩ : syracuseStep 3259205 = 611101) (by norm_num)
theorem B2063173 : Blo 1447543 2063173 := bbase (se 4 (by rfl) ⟨193422, by rfl⟩ : syracuseStep 2063173 = 386845) (by norm_num)
theorem B1629013 : Blo 1447543 1629013 := bbase (se 9 (by rfl) ⟨4772, by rfl⟩ : syracuseStep 1629013 = 9545) (by norm_num)
theorem B4889429 : Blo 1447543 4889429 := bbase (se 9 (by rfl) ⟨14324, by rfl⟩ : syracuseStep 4889429 = 28649) (by norm_num)
theorem B7330661 : Blo 1447543 7330661 := bbase (se 4 (by rfl) ⟨687249, by rfl⟩ : syracuseStep 7330661 = 1374499) (by norm_num)
theorem B1858405 : Blo 1447543 1858405 := bbase (se 4 (by rfl) ⟨174225, by rfl⟩ : syracuseStep 1858405 = 348451) (by norm_num)
theorem B1629049 : Blo 1447543 1629049 := bbase (se 2 (by rfl) ⟨610893, by rfl⟩ : syracuseStep 1629049 = 1221787) (by norm_num)
theorem B3259277 : Blo 1447543 3259277 := bbase (se 3 (by rfl) ⟨611114, by rfl⟩ : syracuseStep 3259277 = 1222229) (by norm_num)
theorem B1547149 : Blo 1447543 1547149 := bbase (se 3 (by rfl) ⟨290090, by rfl⟩ : syracuseStep 1547149 = 580181) (by norm_num)
theorem B3668885 : Blo 1447543 3668885 := bbase (se 6 (by rfl) ⟨85989, by rfl⟩ : syracuseStep 3668885 = 171979) (by norm_num)
theorem B1629085 : Blo 1447543 1629085 := bbase (se 3 (by rfl) ⟨305453, by rfl⟩ : syracuseStep 1629085 = 610907) (by norm_num)
theorem B2751421 : Blo 1447543 2751421 := bbase (se 3 (by rfl) ⟨515891, by rfl⟩ : syracuseStep 2751421 = 1031783) (by norm_num)
theorem B1629121 : Blo 1447543 1629121 := bbase (se 2 (by rfl) ⟨610920, by rfl⟩ : syracuseStep 1629121 = 1221841) (by norm_num)
theorem B1547209 : Blo 1447543 1547209 := bbase (se 2 (by rfl) ⟨580203, by rfl⟩ : syracuseStep 1547209 = 1160407) (by norm_num)
theorem B3259349 : Blo 1447543 3259349 := bbase (se 7 (by rfl) ⟨38195, by rfl⟩ : syracuseStep 3259349 = 76391) (by norm_num)
theorem B1833941 : Blo 1447543 1833941 := bbase (se 7 (by rfl) ⟨21491, by rfl⟩ : syracuseStep 1833941 = 42983) (by norm_num)
theorem B1629157 : Blo 1447543 1629157 := bbase (se 4 (by rfl) ⟨152733, by rfl⟩ : syracuseStep 1629157 = 305467) (by norm_num)
theorem B3718133 : Blo 1447543 3718133 := bbase (se 5 (by rfl) ⟨174287, by rfl⟩ : syracuseStep 3718133 = 348575) (by norm_num)
theorem B1629193 : Blo 1447543 1629193 := bbase (se 2 (by rfl) ⟨610947, by rfl⟩ : syracuseStep 1629193 = 1221895) (by norm_num)
theorem B1833997 : Blo 1447543 1833997 := bbase (se 3 (by rfl) ⟨343874, by rfl⟩ : syracuseStep 1833997 = 687749) (by norm_num)
theorem B3259421 : Blo 1447543 3259421 := bbase (se 3 (by rfl) ⟨611141, by rfl⟩ : syracuseStep 3259421 = 1222283) (by norm_num)
theorem B2063389 : Blo 1447543 2063389 := bbase (se 3 (by rfl) ⟨386885, by rfl⟩ : syracuseStep 2063389 = 773771) (by norm_num)
theorem B1629229 : Blo 1447543 1629229 := bbase (se 3 (by rfl) ⟨305480, by rfl⟩ : syracuseStep 1629229 = 610961) (by norm_num)
theorem B3095597 : Blo 1447543 3095597 := bbase (se 3 (by rfl) ⟨580424, by rfl⟩ : syracuseStep 3095597 = 1160849) (by norm_num)
theorem B1956917 : Blo 1447543 1956917 := bbase (se 5 (by rfl) ⟨91730, by rfl⟩ : syracuseStep 1956917 = 183461) (by norm_num)
theorem B2751565 : Blo 1447543 2751565 := bbase (se 3 (by rfl) ⟨515918, by rfl⟩ : syracuseStep 2751565 = 1031837) (by norm_num)
theorem B1629265 : Blo 1447543 1629265 := bbase (se 2 (by rfl) ⟨610974, by rfl⟩ : syracuseStep 1629265 = 1221949) (by norm_num)
theorem B17849429 : Blo 1447543 17849429 := bbase (se 8 (by rfl) ⟨104586, by rfl⟩ : syracuseStep 17849429 = 209173) (by norm_num)
theorem B3669077 : Blo 1447543 3669077 := bbase (se 8 (by rfl) ⟨21498, by rfl⟩ : syracuseStep 3669077 = 42997) (by norm_num)
theorem B3259493 : Blo 1447543 3259493 := bbase (se 4 (by rfl) ⟨305577, by rfl⟩ : syracuseStep 3259493 = 611155) (by norm_num)
theorem B1834093 : Blo 1447543 1834093 := bbase (se 3 (by rfl) ⟨343892, by rfl⟩ : syracuseStep 1834093 = 687785) (by norm_num)
theorem B1629301 : Blo 1447543 1629301 := bbase (se 5 (by rfl) ⟨76373, by rfl⟩ : syracuseStep 1629301 = 152747) (by norm_num)
theorem B1629337 : Blo 1447543 1629337 := bbase (se 2 (by rfl) ⟨611001, by rfl⟩ : syracuseStep 1629337 = 1222003) (by norm_num)
theorem B3259565 : Blo 1447543 3259565 := bbase (se 3 (by rfl) ⟨611168, by rfl⟩ : syracuseStep 3259565 = 1222337) (by norm_num)
theorem B1629373 : Blo 1447543 1629373 := bbase (se 3 (by rfl) ⟨305507, by rfl⟩ : syracuseStep 1629373 = 611015) (by norm_num)
theorem B28212437 : Blo 1447543 28212437 := bbase (se 7 (by rfl) ⟨330614, by rfl⟩ : syracuseStep 28212437 = 661229) (by norm_num)
theorem B1629409 : Blo 1447543 1629409 := bbase (se 2 (by rfl) ⟨611028, by rfl⟩ : syracuseStep 1629409 = 1222057) (by norm_num)
theorem B2751725 : Blo 1447543 2751725 := bbase (se 3 (by rfl) ⟨515948, by rfl⟩ : syracuseStep 2751725 = 1031897) (by norm_num)
theorem B3259637 : Blo 1447543 3259637 := bbase (se 5 (by rfl) ⟨152795, by rfl⟩ : syracuseStep 3259637 = 305591) (by norm_num)
theorem B1629445 : Blo 1447543 1629445 := bbase (se 4 (by rfl) ⟨152760, by rfl⟩ : syracuseStep 1629445 = 305521) (by norm_num)
theorem B4889861 : Blo 1447543 4889861 := bbase (se 4 (by rfl) ⟨458424, by rfl⟩ : syracuseStep 4889861 = 916849) (by norm_num)
theorem B1547525 : Blo 1447543 1547525 := bbase (se 4 (by rfl) ⟨145080, by rfl⟩ : syracuseStep 1547525 = 290161) (by norm_num)
theorem B1834265 : Blo 1447543 1834265 := bbase (se 2 (by rfl) ⟨687849, by rfl⟩ : syracuseStep 1834265 = 1375699) (by norm_num)
theorem B1629481 : Blo 1447543 1629481 := bbase (se 2 (by rfl) ⟨611055, by rfl⟩ : syracuseStep 1629481 = 1222111) (by norm_num)
theorem B3259709 : Blo 1447543 3259709 := bbase (se 3 (by rfl) ⟨611195, by rfl⟩ : syracuseStep 3259709 = 1222391) (by norm_num)
theorem B1629517 : Blo 1447543 1629517 := bbase (se 3 (by rfl) ⟨305534, by rfl⟩ : syracuseStep 1629517 = 611069) (by norm_num)
theorem B1858897 : Blo 1447543 1858897 := bbase (se 2 (by rfl) ⟨697086, by rfl⟩ : syracuseStep 1858897 = 1394173) (by norm_num)
theorem B80379221 : Blo 1447543 80379221 := bbase (se 11 (by rfl) ⟨58871, by rfl⟩ : syracuseStep 80379221 = 117743) (by norm_num)
theorem B1834321 : Blo 1447543 1834321 := bbase (se 2 (by rfl) ⟨687870, by rfl⟩ : syracuseStep 1834321 = 1375741) (by norm_num)
theorem B1629553 : Blo 1447543 1629553 := bbase (se 2 (by rfl) ⟨611082, by rfl⟩ : syracuseStep 1629553 = 1222165) (by norm_num)
theorem B2751869 : Blo 1447543 2751869 := bbase (se 3 (by rfl) ⟨515975, by rfl⟩ : syracuseStep 2751869 = 1031951) (by norm_num)
theorem B3259781 : Blo 1447543 3259781 := bbase (se 4 (by rfl) ⟨305604, by rfl⟩ : syracuseStep 3259781 = 611209) (by norm_num)
theorem B1629589 : Blo 1447543 1629589 := bbase (se 6 (by rfl) ⟨38193, by rfl⟩ : syracuseStep 1629589 = 76387) (by norm_num)
theorem B2063765 : Blo 1447543 2063765 := bbase (se 6 (by rfl) ⟨48369, by rfl⟩ : syracuseStep 2063765 = 96739) (by norm_num)
theorem B1834417 : Blo 1447543 1834417 := bbase (se 2 (by rfl) ⟨687906, by rfl⟩ : syracuseStep 1834417 = 1375813) (by norm_num)
theorem B1629625 : Blo 1447543 1629625 := bbase (se 2 (by rfl) ⟨611109, by rfl⟩ : syracuseStep 1629625 = 1222219) (by norm_num)
theorem B3259853 : Blo 1447543 3259853 := bbase (se 3 (by rfl) ⟨611222, by rfl⟩ : syracuseStep 3259853 = 1222445) (by norm_num)
theorem B1629661 : Blo 1447543 1629661 := bbase (se 3 (by rfl) ⟨305561, by rfl⟩ : syracuseStep 1629661 = 611123) (by norm_num)
theorem B1629697 : Blo 1447543 1629697 := bbase (se 2 (by rfl) ⟨611136, by rfl⟩ : syracuseStep 1629697 = 1222273) (by norm_num)
theorem B3259925 : Blo 1447543 3259925 := bbase (se 6 (by rfl) ⟨76404, by rfl⟩ : syracuseStep 3259925 = 152809) (by norm_num)
theorem B1629733 : Blo 1447543 1629733 := bbase (se 4 (by rfl) ⟨152787, by rfl⟩ : syracuseStep 1629733 = 305575) (by norm_num)
theorem B1629769 : Blo 1447543 1629769 := bbase (se 2 (by rfl) ⟨611163, by rfl⟩ : syracuseStep 1629769 = 1222327) (by norm_num)
theorem B3259997 : Blo 1447543 3259997 := bbase (se 3 (by rfl) ⟨611249, by rfl⟩ : syracuseStep 3259997 = 1222499) (by norm_num)
theorem B1629805 : Blo 1447543 1629805 := bbase (se 3 (by rfl) ⟨305588, by rfl⟩ : syracuseStep 1629805 = 611177) (by norm_num)
theorem B3718781 : Blo 1447543 3718781 := bbase (se 3 (by rfl) ⟨697271, by rfl⟩ : syracuseStep 3718781 = 1394543) (by norm_num)
theorem B1629841 : Blo 1447543 1629841 := bbase (se 2 (by rfl) ⟨611190, by rfl⟩ : syracuseStep 1629841 = 1222381) (by norm_num)
theorem B18562709 : Blo 1447543 18562709 := bbase (se 6 (by rfl) ⟨435063, by rfl⟩ : syracuseStep 18562709 = 870127) (by norm_num)
theorem B3260069 : Blo 1447543 3260069 := bbase (se 4 (by rfl) ⟨305631, by rfl⟩ : syracuseStep 3260069 = 611263) (by norm_num)
theorem B1629877 : Blo 1447543 1629877 := bbase (se 5 (by rfl) ⟨76400, by rfl⟩ : syracuseStep 1629877 = 152801) (by norm_num)
theorem B4890293 : Blo 1447543 4890293 := bbase (se 5 (by rfl) ⟨229232, by rfl⟩ : syracuseStep 4890293 = 458465) (by norm_num)
theorem B3481277 : Blo 1447543 3481277 := bbase (se 3 (by rfl) ⟨652739, by rfl⟩ : syracuseStep 3481277 = 1305479) (by norm_num)
theorem B1629913 : Blo 1447543 1629913 := bbase (se 2 (by rfl) ⟨611217, by rfl⟩ : syracuseStep 1629913 = 1222435) (by norm_num)
theorem B3260141 : Blo 1447543 3260141 := bbase (se 3 (by rfl) ⟨611276, by rfl⟩ : syracuseStep 3260141 = 1222553) (by norm_num)
theorem B1629949 : Blo 1447543 1629949 := bbase (se 3 (by rfl) ⟨305615, by rfl⟩ : syracuseStep 1629949 = 611231) (by norm_num)
theorem B1629985 : Blo 1447543 1629985 := bbase (se 2 (by rfl) ⟨611244, by rfl⟩ : syracuseStep 1629985 = 1222489) (by norm_num)
theorem B3260213 : Blo 1447543 3260213 := bbase (se 5 (by rfl) ⟨152822, by rfl⟩ : syracuseStep 3260213 = 305645) (by norm_num)
theorem B1630021 : Blo 1447543 1630021 := bbase (se 4 (by rfl) ⟨152814, by rfl⟩ : syracuseStep 1630021 = 305629) (by norm_num)
theorem B3137381 : Blo 1447543 3137381 := bbase (se 4 (by rfl) ⟨294129, by rfl⟩ : syracuseStep 3137381 = 588259) (by norm_num)
theorem B1630057 : Blo 1447543 1630057 := bbase (se 2 (by rfl) ⟨611271, by rfl⟩ : syracuseStep 1630057 = 1222543) (by norm_num)
theorem B3260285 : Blo 1447543 3260285 := bbase (se 3 (by rfl) ⟨611303, by rfl⟩ : syracuseStep 3260285 = 1222607) (by norm_num)
theorem B1957765 : Blo 1447543 1957765 := bbase (se 4 (by rfl) ⟨183540, by rfl⟩ : syracuseStep 1957765 = 367081) (by norm_num)
theorem B1630093 : Blo 1447543 1630093 := bbase (se 3 (by rfl) ⟨305642, by rfl⟩ : syracuseStep 1630093 = 611285) (by norm_num)
theorem B1630129 : Blo 1447543 1630129 := bbase (se 2 (by rfl) ⟨611298, by rfl⟩ : syracuseStep 1630129 = 1222597) (by norm_num)
theorem B3260357 : Blo 1447543 3260357 := bbase (se 4 (by rfl) ⟨305658, by rfl⟩ : syracuseStep 3260357 = 611317) (by norm_num)
theorem B1630165 : Blo 1447543 1630165 := bbase (se 7 (by rfl) ⟨19103, by rfl⟩ : syracuseStep 1630165 = 38207) (by norm_num)
theorem B1630201 : Blo 1447543 1630201 := bbase (se 2 (by rfl) ⟨611325, by rfl⟩ : syracuseStep 1630201 = 1222651) (by norm_num)
theorem B6184973 : Blo 1447543 6184973 := bstep (se 3 (by rfl) ⟨1159682, by rfl⟩ : syracuseStep 6184973 = 2319365) B2319365
theorem B3260465 : Blo 1447543 3260465 := bstep (se 2 (by rfl) ⟨1222674, by rfl⟩ : syracuseStep 3260465 = 2445349) B2445349
theorem B3260483 : Blo 1447543 3260483 := bstep (se 1 (by rfl) ⟨2445362, by rfl⟩ : syracuseStep 3260483 = 4890725) B4890725
theorem B1630291 : Blo 1447543 1630291 := bstep (se 1 (by rfl) ⟨1222718, by rfl⟩ : syracuseStep 1630291 = 2445437) B2445437
theorem B3915875 : Blo 1447543 3915875 := bstep (se 1 (by rfl) ⟨2936906, by rfl⟩ : syracuseStep 3915875 = 5873813) B5873813
theorem B10993805 : Blo 1447543 10993805 := bstep (se 3 (by rfl) ⟨2061338, by rfl⟩ : syracuseStep 10993805 = 4122677) B4122677
theorem B5218445 : Blo 1447543 5218445 := bstep (se 3 (by rfl) ⟨978458, by rfl⟩ : syracuseStep 5218445 = 1956917) B1956917
theorem B5726371 : Blo 1447543 5726371 := bstep (se 1 (by rfl) ⟨4294778, by rfl⟩ : syracuseStep 5726371 = 8589557) B8589557
theorem B4890833 : Blo 1447543 4890833 := bstep (se 2 (by rfl) ⟨1834062, by rfl⟩ : syracuseStep 4890833 = 3668125) B3668125
theorem B1630435 : Blo 1447543 1630435 := bstep (se 1 (by rfl) ⟨1222826, by rfl⟩ : syracuseStep 1630435 = 2445653) B2445653
theorem B13926725 : Blo 1447543 13926725 := bstep (se 4 (by rfl) ⟨1305630, by rfl⟩ : syracuseStep 13926725 = 2611261) B2611261
theorem B3260753 : Blo 1447543 3260753 := bstep (se 2 (by rfl) ⟨1222782, by rfl⟩ : syracuseStep 3260753 = 2445565) B2445565
theorem B6185315 : Blo 1447543 6185315 := bstep (se 1 (by rfl) ⟨4638986, by rfl⟩ : syracuseStep 6185315 = 9277973) B9277973
theorem B10043747 : Blo 1447543 10043747 := bstep (se 1 (by rfl) ⟨7532810, by rfl⟩ : syracuseStep 10043747 = 15065621) B15065621
theorem B3260771 : Blo 1447543 3260771 := bstep (se 1 (by rfl) ⟨2445578, by rfl⟩ : syracuseStep 3260771 = 4891157) B4891157
theorem B1630579 : Blo 1447543 1630579 := bstep (se 1 (by rfl) ⟨1222934, by rfl⟩ : syracuseStep 1630579 = 2445869) B2445869
theorem B2171315 : Blo 1447543 2171315 := bstep (se 1 (by rfl) ⟨1628486, by rfl⟩ : syracuseStep 2171315 = 3256973) B3256973
theorem B4178371 : Blo 1447543 4178371 := bstep (se 1 (by rfl) ⟨3133778, by rfl⟩ : syracuseStep 4178371 = 6267557) B6267557
theorem B2171345 : Blo 1447543 2171345 := bstep (se 2 (by rfl) ⟨814254, by rfl⟩ : syracuseStep 2171345 = 1628509) B1628509
theorem B2318801 : Blo 1447543 2318801 := bstep (se 2 (by rfl) ⟨869550, by rfl⟩ : syracuseStep 2318801 = 1739101) B1739101
theorem B2171363 : Blo 1447543 2171363 := bstep (se 1 (by rfl) ⟨1628522, by rfl⟩ : syracuseStep 2171363 = 3257045) B3257045
theorem B5022179 : Blo 1447543 5022179 := bstep (se 1 (by rfl) ⟨3766634, by rfl⟩ : syracuseStep 5022179 = 7533269) B7533269
theorem B2171393 : Blo 1447543 2171393 := bstep (se 2 (by rfl) ⟨814272, by rfl⟩ : syracuseStep 2171393 = 1628545) B1628545
theorem B1630723 : Blo 1447543 1630723 := bstep (se 1 (by rfl) ⟨1223042, by rfl⟩ : syracuseStep 1630723 = 2446085) B2446085
theorem B2171411 : Blo 1447543 2171411 := bstep (se 1 (by rfl) ⟨1628558, by rfl⟩ : syracuseStep 2171411 = 3257117) B3257117
theorem B2171441 : Blo 1447543 2171441 := bstep (se 2 (by rfl) ⟨814290, by rfl⟩ : syracuseStep 2171441 = 1628581) B1628581
theorem B2171459 : Blo 1447543 2171459 := bstep (se 1 (by rfl) ⟨1628594, by rfl⟩ : syracuseStep 2171459 = 3257189) B3257189
theorem B2171489 : Blo 1447543 2171489 := bstep (se 2 (by rfl) ⟨814308, by rfl⟩ : syracuseStep 2171489 = 1628617) B1628617
theorem B3261041 : Blo 1447543 3261041 := bstep (se 2 (by rfl) ⟨1222890, by rfl⟩ : syracuseStep 3261041 = 2445781) B2445781
theorem B2171507 : Blo 1447543 2171507 := bstep (se 1 (by rfl) ⟨1628630, by rfl⟩ : syracuseStep 2171507 = 3257261) B3257261
theorem B3261059 : Blo 1447543 3261059 := bstep (se 1 (by rfl) ⟨2445794, by rfl⟩ : syracuseStep 3261059 = 4891589) B4891589
theorem B2171537 : Blo 1447543 2171537 := bstep (se 2 (by rfl) ⟨814326, by rfl⟩ : syracuseStep 2171537 = 1628653) B1628653
theorem B2171555 : Blo 1447543 2171555 := bstep (se 1 (by rfl) ⟨1628666, by rfl⟩ : syracuseStep 2171555 = 3257333) B3257333
theorem B2171585 : Blo 1447543 2171585 := bstep (se 2 (by rfl) ⟨814344, by rfl⟩ : syracuseStep 2171585 = 1628689) B1628689
theorem B2171603 : Blo 1447543 2171603 := bstep (se 1 (by rfl) ⟨1628702, by rfl⟩ : syracuseStep 2171603 = 3257405) B3257405
theorem B5497571 : Blo 1447543 5497571 := bstep (se 1 (by rfl) ⟨4123178, by rfl⟩ : syracuseStep 5497571 = 8246357) B8246357
theorem B3916525 : Blo 1447543 3916525 := bstep (se 3 (by rfl) ⟨734348, by rfl⟩ : syracuseStep 3916525 = 1468697) B1468697
theorem B4891373 : Blo 1447543 4891373 := bstep (se 3 (by rfl) ⟨917132, by rfl⟩ : syracuseStep 4891373 = 1834265) B1834265
theorem B2171633 : Blo 1447543 2171633 := bstep (se 2 (by rfl) ⟨814362, by rfl⟩ : syracuseStep 2171633 = 1628725) B1628725
theorem B2171651 : Blo 1447543 2171651 := bstep (se 1 (by rfl) ⟨1628738, by rfl⟩ : syracuseStep 2171651 = 3257477) B3257477
theorem B2171681 : Blo 1447543 2171681 := bstep (se 2 (by rfl) ⟨814380, by rfl⟩ : syracuseStep 2171681 = 1628761) B1628761
theorem B4891427 : Blo 1447543 4891427 := bstep (se 1 (by rfl) ⟨3668570, by rfl⟩ : syracuseStep 4891427 = 7337141) B7337141
theorem B2171699 : Blo 1447543 2171699 := bstep (se 1 (by rfl) ⟨1628774, by rfl⟩ : syracuseStep 2171699 = 3257549) B3257549
theorem B2171729 : Blo 1447543 2171729 := bstep (se 2 (by rfl) ⟨814398, by rfl⟩ : syracuseStep 2171729 = 1628797) B1628797
theorem B2171747 : Blo 1447543 2171747 := bstep (se 1 (by rfl) ⟨1628810, by rfl⟩ : syracuseStep 2171747 = 3257621) B3257621
theorem B2171777 : Blo 1447543 2171777 := bstep (se 2 (by rfl) ⟨814416, by rfl⟩ : syracuseStep 2171777 = 1628833) B1628833
theorem B214344589 : Blo 1447543 214344589 := bstep (se 3 (by rfl) ⟨40189610, by rfl⟩ : syracuseStep 214344589 = 80379221) B80379221
theorem B3261329 : Blo 1447543 3261329 := bstep (se 2 (by rfl) ⟨1222998, by rfl⟩ : syracuseStep 3261329 = 2445997) B2445997
theorem B2171795 : Blo 1447543 2171795 := bstep (se 1 (by rfl) ⟨1628846, by rfl⟩ : syracuseStep 2171795 = 3257693) B3257693
theorem B8250275 : Blo 1447543 8250275 := bstep (se 1 (by rfl) ⟨6187706, by rfl⟩ : syracuseStep 8250275 = 12375413) B12375413
theorem B3261347 : Blo 1447543 3261347 := bstep (se 1 (by rfl) ⟨2446010, by rfl⟩ : syracuseStep 3261347 = 4892021) B4892021
theorem B2171825 : Blo 1447543 2171825 := bstep (se 2 (by rfl) ⟨814434, by rfl⟩ : syracuseStep 2171825 = 1628869) B1628869
theorem B2171843 : Blo 1447543 2171843 := bstep (se 1 (by rfl) ⟨1628882, by rfl⟩ : syracuseStep 2171843 = 3257765) B3257765
theorem B2171873 : Blo 1447543 2171873 := bstep (se 2 (by rfl) ⟨814452, by rfl⟩ : syracuseStep 2171873 = 1628905) B1628905
theorem B2171891 : Blo 1447543 2171891 := bstep (se 1 (by rfl) ⟨1628918, by rfl⟩ : syracuseStep 2171891 = 3257837) B3257837
theorem B2171921 : Blo 1447543 2171921 := bstep (se 2 (by rfl) ⟨814470, by rfl⟩ : syracuseStep 2171921 = 1628941) B1628941
theorem B4637731 : Blo 1447543 4637731 := bstep (se 1 (by rfl) ⟨3478298, by rfl⟩ : syracuseStep 4637731 = 6956597) B6956597
theorem B2171939 : Blo 1447543 2171939 := bstep (se 1 (by rfl) ⟨1628954, by rfl⟩ : syracuseStep 2171939 = 3257909) B3257909
theorem B4891697 : Blo 1447543 4891697 := bstep (se 2 (by rfl) ⟨1834386, by rfl⟩ : syracuseStep 4891697 = 3668773) B3668773
theorem B2171969 : Blo 1447543 2171969 := bstep (se 2 (by rfl) ⟨814488, by rfl⟩ : syracuseStep 2171969 = 1628977) B1628977
theorem B2171987 : Blo 1447543 2171987 := bstep (se 1 (by rfl) ⟨1628990, by rfl⟩ : syracuseStep 2171987 = 3257981) B3257981
theorem B2172017 : Blo 1447543 2172017 := bstep (se 2 (by rfl) ⟨814506, by rfl⟩ : syracuseStep 2172017 = 1629013) B1629013
theorem B2172035 : Blo 1447543 2172035 := bstep (se 1 (by rfl) ⟨1629026, by rfl⟩ : syracuseStep 2172035 = 3258053) B3258053
theorem B2172065 : Blo 1447543 2172065 := bstep (se 2 (by rfl) ⟨814524, by rfl⟩ : syracuseStep 2172065 = 1629049) B1629049
theorem B2172083 : Blo 1447543 2172083 := bstep (se 1 (by rfl) ⟨1629062, by rfl⟩ : syracuseStep 2172083 = 3258125) B3258125
theorem B2172113 : Blo 1447543 2172113 := bstep (se 2 (by rfl) ⟨814542, by rfl⟩ : syracuseStep 2172113 = 1629085) B1629085
theorem B2172131 : Blo 1447543 2172131 := bstep (se 1 (by rfl) ⟨1629098, by rfl⟩ : syracuseStep 2172131 = 3258197) B3258197
theorem B7333091 : Blo 1447543 7333091 := bstep (se 1 (by rfl) ⟨5499818, by rfl⟩ : syracuseStep 7333091 = 10999637) B10999637
theorem B2172161 : Blo 1447543 2172161 := bstep (se 2 (by rfl) ⟨814560, by rfl⟩ : syracuseStep 2172161 = 1629121) B1629121
theorem B2172179 : Blo 1447543 2172179 := bstep (se 1 (by rfl) ⟨1629134, by rfl⟩ : syracuseStep 2172179 = 3258269) B3258269
theorem B2172209 : Blo 1447543 2172209 := bstep (se 2 (by rfl) ⟨814578, by rfl⟩ : syracuseStep 2172209 = 1629157) B1629157
theorem B2172227 : Blo 1447543 2172227 := bstep (se 1 (by rfl) ⟨1629170, by rfl⟩ : syracuseStep 2172227 = 3258341) B3258341
theorem B2172257 : Blo 1447543 2172257 := bstep (se 2 (by rfl) ⟨814596, by rfl⟩ : syracuseStep 2172257 = 1629193) B1629193
theorem B5498225 : Blo 1447543 5498225 := bstep (se 2 (by rfl) ⟨2061834, by rfl⟩ : syracuseStep 5498225 = 4123669) B4123669
theorem B2172275 : Blo 1447543 2172275 := bstep (se 1 (by rfl) ⟨1629206, by rfl⟩ : syracuseStep 2172275 = 3258413) B3258413
theorem B2172305 : Blo 1447543 2172305 := bstep (se 2 (by rfl) ⟨814614, by rfl⟩ : syracuseStep 2172305 = 1629229) B1629229
theorem B2090387 : Blo 1447543 2090387 := bstep (se 1 (by rfl) ⟨1567790, by rfl⟩ : syracuseStep 2090387 = 3135581) B3135581
theorem B3302819 : Blo 1447543 3302819 := bstep (se 1 (by rfl) ⟨2477114, by rfl⟩ : syracuseStep 3302819 = 4954229) B4954229
theorem B2172323 : Blo 1447543 2172323 := bstep (se 1 (by rfl) ⟨1629242, by rfl⟩ : syracuseStep 2172323 = 3258485) B3258485
theorem B2172353 : Blo 1447543 2172353 := bstep (se 2 (by rfl) ⟨814632, by rfl⟩ : syracuseStep 2172353 = 1629265) B1629265
theorem B2172371 : Blo 1447543 2172371 := bstep (se 1 (by rfl) ⟨1629278, by rfl⟩ : syracuseStep 2172371 = 3258557) B3258557
theorem B2442737 : Blo 1447543 2442737 := bstep (se 2 (by rfl) ⟨916026, by rfl⟩ : syracuseStep 2442737 = 1832053) B1832053
theorem B2172401 : Blo 1447543 2172401 := bstep (se 2 (by rfl) ⟨814650, by rfl⟩ : syracuseStep 2172401 = 1629301) B1629301
theorem B2172419 : Blo 1447543 2172419 := bstep (se 1 (by rfl) ⟨1629314, by rfl⟩ : syracuseStep 2172419 = 3258629) B3258629
theorem B2172449 : Blo 1447543 2172449 := bstep (se 2 (by rfl) ⟨814668, by rfl⟩ : syracuseStep 2172449 = 1629337) B1629337
theorem B2172467 : Blo 1447543 2172467 := bstep (se 1 (by rfl) ⟨1629350, by rfl⟩ : syracuseStep 2172467 = 3258701) B3258701
theorem B2172497 : Blo 1447543 2172497 := bstep (se 2 (by rfl) ⟨814686, by rfl⟩ : syracuseStep 2172497 = 1629373) B1629373
theorem B4122211 : Blo 1447543 4122211 := bstep (se 1 (by rfl) ⟨3091658, by rfl⟩ : syracuseStep 4122211 = 6183317) B6183317
theorem B2172515 : Blo 1447543 2172515 := bstep (se 1 (by rfl) ⟨1629386, by rfl⟩ : syracuseStep 2172515 = 3258773) B3258773
theorem B2442865 : Blo 1447543 2442865 := bstep (se 2 (by rfl) ⟨916074, by rfl⟩ : syracuseStep 2442865 = 1832149) B1832149
theorem B2172545 : Blo 1447543 2172545 := bstep (se 2 (by rfl) ⟨814704, by rfl⟩ : syracuseStep 2172545 = 1629409) B1629409
theorem B2442899 : Blo 1447543 2442899 := bstep (se 1 (by rfl) ⟨1832174, by rfl⟩ : syracuseStep 2442899 = 3664349) B3664349
theorem B2172563 : Blo 1447543 2172563 := bstep (se 1 (by rfl) ⟨1629422, by rfl⟩ : syracuseStep 2172563 = 3258845) B3258845
theorem B2172593 : Blo 1447543 2172593 := bstep (se 2 (by rfl) ⟨814722, by rfl⟩ : syracuseStep 2172593 = 1629445) B1629445
theorem B2172611 : Blo 1447543 2172611 := bstep (se 1 (by rfl) ⟨1629458, by rfl⟩ : syracuseStep 2172611 = 3258917) B3258917
theorem B2172641 : Blo 1447543 2172641 := bstep (se 2 (by rfl) ⟨814740, by rfl⟩ : syracuseStep 2172641 = 1629481) B1629481
theorem B2172659 : Blo 1447543 2172659 := bstep (se 1 (by rfl) ⟨1629494, by rfl⟩ : syracuseStep 2172659 = 3258989) B3258989
theorem B2172689 : Blo 1447543 2172689 := bstep (se 2 (by rfl) ⟨814758, by rfl⟩ : syracuseStep 2172689 = 1629517) B1629517
theorem B2443027 : Blo 1447543 2443027 := bstep (se 1 (by rfl) ⟨1832270, by rfl⟩ : syracuseStep 2443027 = 3664541) B3664541
theorem B2172707 : Blo 1447543 2172707 := bstep (se 1 (by rfl) ⟨1629530, by rfl⟩ : syracuseStep 2172707 = 3259061) B3259061
theorem B2172737 : Blo 1447543 2172737 := bstep (se 2 (by rfl) ⟨814776, by rfl⟩ : syracuseStep 2172737 = 1629553) B1629553
theorem B9283405 : Blo 1447543 9283405 := bstep (se 3 (by rfl) ⟨1740638, by rfl⟩ : syracuseStep 9283405 = 3481277) B3481277
theorem B2320211 : Blo 1447543 2320211 := bstep (se 1 (by rfl) ⟨1740158, by rfl⟩ : syracuseStep 2320211 = 3480317) B3480317
theorem B2172755 : Blo 1447543 2172755 := bstep (se 1 (by rfl) ⟨1629566, by rfl⟩ : syracuseStep 2172755 = 3259133) B3259133
theorem B2172785 : Blo 1447543 2172785 := bstep (se 2 (by rfl) ⟨814794, by rfl⟩ : syracuseStep 2172785 = 1629589) B1629589
theorem B2172803 : Blo 1447543 2172803 := bstep (se 1 (by rfl) ⟨1629602, by rfl⟩ : syracuseStep 2172803 = 3259205) B3259205
theorem B11913101 : Blo 1447543 11913101 := bstep (se 3 (by rfl) ⟨2233706, by rfl⟩ : syracuseStep 11913101 = 4467413) B4467413
theorem B2443169 : Blo 1447543 2443169 := bstep (se 2 (by rfl) ⟨916188, by rfl⟩ : syracuseStep 2443169 = 1832377) B1832377
theorem B2172833 : Blo 1447543 2172833 := bstep (se 2 (by rfl) ⟨814812, by rfl⟩ : syracuseStep 2172833 = 1629625) B1629625
theorem B2172851 : Blo 1447543 2172851 := bstep (se 1 (by rfl) ⟨1629638, by rfl⟩ : syracuseStep 2172851 = 3259277) B3259277
theorem B2172881 : Blo 1447543 2172881 := bstep (se 2 (by rfl) ⟨814830, by rfl⟩ : syracuseStep 2172881 = 1629661) B1629661
theorem B2172899 : Blo 1447543 2172899 := bstep (se 1 (by rfl) ⟨1629674, by rfl⟩ : syracuseStep 2172899 = 3259349) B3259349
theorem B2172929 : Blo 1447543 2172929 := bstep (se 2 (by rfl) ⟨814848, by rfl⟩ : syracuseStep 2172929 = 1629697) B1629697
theorem B7333901 : Blo 1447543 7333901 := bstep (se 3 (by rfl) ⟨1375106, by rfl⟩ : syracuseStep 7333901 = 2750213) B2750213
theorem B2172947 : Blo 1447543 2172947 := bstep (se 1 (by rfl) ⟨1629710, by rfl⟩ : syracuseStep 2172947 = 3259421) B3259421
theorem B2443297 : Blo 1447543 2443297 := bstep (se 2 (by rfl) ⟨916236, by rfl⟩ : syracuseStep 2443297 = 1832473) B1832473
theorem B2172977 : Blo 1447543 2172977 := bstep (se 2 (by rfl) ⟨814866, by rfl⟩ : syracuseStep 2172977 = 1629733) B1629733
theorem B2443331 : Blo 1447543 2443331 := bstep (se 1 (by rfl) ⟨1832498, by rfl⟩ : syracuseStep 2443331 = 3664997) B3664997
theorem B2172995 : Blo 1447543 2172995 := bstep (se 1 (by rfl) ⟨1629746, by rfl⟩ : syracuseStep 2172995 = 3259493) B3259493
theorem B4122701 : Blo 1447543 4122701 := bstep (se 3 (by rfl) ⟨773006, by rfl⟩ : syracuseStep 4122701 = 1546013) B1546013
theorem B2173025 : Blo 1447543 2173025 := bstep (se 2 (by rfl) ⟨814884, by rfl⟩ : syracuseStep 2173025 = 1629769) B1629769
theorem B4638833 : Blo 1447543 4638833 := bstep (se 2 (by rfl) ⟨1739562, by rfl⟩ : syracuseStep 4638833 = 3479125) B3479125
theorem B2173043 : Blo 1447543 2173043 := bstep (se 1 (by rfl) ⟨1629782, by rfl⟩ : syracuseStep 2173043 = 3259565) B3259565
theorem B18827405 : Blo 1447543 18827405 := bstep (se 3 (by rfl) ⟨3530138, by rfl⟩ : syracuseStep 18827405 = 7060277) B7060277
theorem B2173073 : Blo 1447543 2173073 := bstep (se 2 (by rfl) ⟨814902, by rfl⟩ : syracuseStep 2173073 = 1629805) B1629805
theorem B2173091 : Blo 1447543 2173091 := bstep (se 1 (by rfl) ⟨1629818, by rfl⟩ : syracuseStep 2173091 = 3259637) B3259637
theorem B2173121 : Blo 1447543 2173121 := bstep (se 2 (by rfl) ⟨814920, by rfl⟩ : syracuseStep 2173121 = 1629841) B1629841
theorem B2443459 : Blo 1447543 2443459 := bstep (se 1 (by rfl) ⟨1832594, by rfl⟩ : syracuseStep 2443459 = 3665189) B3665189
theorem B2173139 : Blo 1447543 2173139 := bstep (se 1 (by rfl) ⟨1629854, by rfl⟩ : syracuseStep 2173139 = 3259709) B3259709
theorem B89163989 : Blo 1447543 89163989 := bstep (se 7 (by rfl) ⟨1044890, by rfl⟩ : syracuseStep 89163989 = 2089781) B2089781
theorem B7833827 : Blo 1447543 7833827 := bstep (se 1 (by rfl) ⟨5875370, by rfl⟩ : syracuseStep 7833827 = 11750741) B11750741
theorem B4638961 : Blo 1447543 4638961 := bstep (se 2 (by rfl) ⟨1739610, by rfl⟩ : syracuseStep 4638961 = 3479221) B3479221
theorem B13920497 : Blo 1447543 13920497 := bstep (se 2 (by rfl) ⟨5220186, by rfl⟩ : syracuseStep 13920497 = 10440373) B10440373
theorem B2173169 : Blo 1447543 2173169 := bstep (se 2 (by rfl) ⟨814938, by rfl⟩ : syracuseStep 2173169 = 1629877) B1629877
theorem B2173187 : Blo 1447543 2173187 := bstep (se 1 (by rfl) ⟨1629890, by rfl⟩ : syracuseStep 2173187 = 3259781) B3259781
theorem B2173217 : Blo 1447543 2173217 := bstep (se 2 (by rfl) ⟨814956, by rfl⟩ : syracuseStep 2173217 = 1629913) B1629913
theorem B3918125 : Blo 1447543 3918125 := bstep (se 3 (by rfl) ⟨734648, by rfl⟩ : syracuseStep 3918125 = 1469297) B1469297
theorem B2173235 : Blo 1447543 2173235 := bstep (se 1 (by rfl) ⟨1629926, by rfl⟩ : syracuseStep 2173235 = 3259853) B3259853
theorem B2443601 : Blo 1447543 2443601 := bstep (se 2 (by rfl) ⟨916350, by rfl⟩ : syracuseStep 2443601 = 1832701) B1832701
theorem B2173265 : Blo 1447543 2173265 := bstep (se 2 (by rfl) ⟨814974, by rfl⟩ : syracuseStep 2173265 = 1629949) B1629949
theorem B2173283 : Blo 1447543 2173283 := bstep (se 1 (by rfl) ⟨1629962, by rfl⟩ : syracuseStep 2173283 = 3259925) B3259925
theorem B2173313 : Blo 1447543 2173313 := bstep (se 2 (by rfl) ⟨814992, by rfl⟩ : syracuseStep 2173313 = 1629985) B1629985
theorem B2173331 : Blo 1447543 2173331 := bstep (se 1 (by rfl) ⟨1629998, by rfl⟩ : syracuseStep 2173331 = 3259997) B3259997
theorem B3303857 : Blo 1447543 3303857 := bstep (se 2 (by rfl) ⟨1238946, by rfl⟩ : syracuseStep 3303857 = 2477893) B2477893
theorem B2173361 : Blo 1447543 2173361 := bstep (se 2 (by rfl) ⟨815010, by rfl⟩ : syracuseStep 2173361 = 1630021) B1630021
theorem B2173379 : Blo 1447543 2173379 := bstep (se 1 (by rfl) ⟨1630034, by rfl⟩ : syracuseStep 2173379 = 3260069) B3260069
theorem B2443729 : Blo 1447543 2443729 := bstep (se 2 (by rfl) ⟨916398, by rfl⟩ : syracuseStep 2443729 = 1832797) B1832797
theorem B2173409 : Blo 1447543 2173409 := bstep (se 2 (by rfl) ⟨815028, by rfl⟩ : syracuseStep 2173409 = 1630057) B1630057
theorem B2443763 : Blo 1447543 2443763 := bstep (se 1 (by rfl) ⟨1832822, by rfl⟩ : syracuseStep 2443763 = 3665645) B3665645
theorem B2173427 : Blo 1447543 2173427 := bstep (se 1 (by rfl) ⟨1630070, by rfl⟩ : syracuseStep 2173427 = 3260141) B3260141
theorem B2173457 : Blo 1447543 2173457 := bstep (se 2 (by rfl) ⟨815046, by rfl⟩ : syracuseStep 2173457 = 1630093) B1630093
theorem B2173475 : Blo 1447543 2173475 := bstep (se 1 (by rfl) ⟨1630106, by rfl⟩ : syracuseStep 2173475 = 3260213) B3260213
theorem B18565685 : Blo 1447543 18565685 := bstep (se 5 (by rfl) ⟨870266, by rfl⟩ : syracuseStep 18565685 = 1740533) B1740533
theorem B2173505 : Blo 1447543 2173505 := bstep (se 2 (by rfl) ⟨815064, by rfl⟩ : syracuseStep 2173505 = 1630129) B1630129
theorem B2091587 : Blo 1447543 2091587 := bstep (se 1 (by rfl) ⟨1568690, by rfl⟩ : syracuseStep 2091587 = 3137381) B3137381
theorem B2173523 : Blo 1447543 2173523 := bstep (se 1 (by rfl) ⟨1630142, by rfl⟩ : syracuseStep 2173523 = 3260285) B3260285
theorem B2173553 : Blo 1447543 2173553 := bstep (se 2 (by rfl) ⟨815082, by rfl⟩ : syracuseStep 2173553 = 1630165) B1630165
theorem B9914993 : Blo 1447543 9914993 := bstep (se 2 (by rfl) ⟨3718122, by rfl⟩ : syracuseStep 9914993 = 7436245) B7436245
theorem B2443891 : Blo 1447543 2443891 := bstep (se 1 (by rfl) ⟨1832918, by rfl⟩ : syracuseStep 2443891 = 3665837) B3665837
theorem B2476675 : Blo 1447543 2476675 := bstep (se 1 (by rfl) ⟨1857506, by rfl⟩ : syracuseStep 2476675 = 3715013) B3715013
theorem B2173571 : Blo 1447543 2173571 := bstep (se 1 (by rfl) ⟨1630178, by rfl⟩ : syracuseStep 2173571 = 3260357) B3260357
theorem B2321057 : Blo 1447543 2321057 := bstep (se 2 (by rfl) ⟨870396, by rfl⟩ : syracuseStep 2321057 = 1740793) B1740793
theorem B2173601 : Blo 1447543 2173601 := bstep (se 2 (by rfl) ⟨815100, by rfl⟩ : syracuseStep 2173601 = 1630201) B1630201
theorem B3664561 : Blo 1447543 3664561 := bstep (se 2 (by rfl) ⟨1374210, by rfl⟩ : syracuseStep 3664561 = 2748421) B2748421
theorem B2173619 : Blo 1447543 2173619 := bstep (se 1 (by rfl) ⟨1630214, by rfl⟩ : syracuseStep 2173619 = 3260429) B3260429
theorem B16714421 : Blo 1447543 16714421 := bstep (se 5 (by rfl) ⟨783488, by rfl⟩ : syracuseStep 16714421 = 1566977) B1566977
theorem B2173649 : Blo 1447543 2173649 := bstep (se 2 (by rfl) ⟨815118, by rfl⟩ : syracuseStep 2173649 = 1630237) B1630237
theorem B31763171 : Blo 1447543 31763171 := bstep (se 1 (by rfl) ⟨23822378, by rfl⟩ : syracuseStep 31763171 = 47644757) B47644757
theorem B2173667 : Blo 1447543 2173667 := bstep (se 1 (by rfl) ⟨1630250, by rfl⟩ : syracuseStep 2173667 = 3260501) B3260501
theorem B2444033 : Blo 1447543 2444033 := bstep (se 2 (by rfl) ⟨916512, by rfl⟩ : syracuseStep 2444033 = 1833025) B1833025
theorem B2173697 : Blo 1447543 2173697 := bstep (se 2 (by rfl) ⟨815136, by rfl⟩ : syracuseStep 2173697 = 1630273) B1630273
theorem B12372749 : Blo 1447543 12372749 := bstep (se 3 (by rfl) ⟨2319890, by rfl⟩ : syracuseStep 12372749 = 4639781) B4639781
theorem B2173715 : Blo 1447543 2173715 := bstep (se 1 (by rfl) ⟨1630286, by rfl⟩ : syracuseStep 2173715 = 3260573) B3260573
theorem B5499683 : Blo 1447543 5499683 := bstep (se 1 (by rfl) ⟨4124762, by rfl⟩ : syracuseStep 5499683 = 8249525) B8249525
theorem B5499697 : Blo 1447543 5499697 := bstep (se 2 (by rfl) ⟨2062386, by rfl⟩ : syracuseStep 5499697 = 4124773) B4124773
theorem B2173745 : Blo 1447543 2173745 := bstep (se 2 (by rfl) ⟨815154, by rfl⟩ : syracuseStep 2173745 = 1630309) B1630309
theorem B2173763 : Blo 1447543 2173763 := bstep (se 1 (by rfl) ⟨1630322, by rfl⟩ : syracuseStep 2173763 = 3260645) B3260645
theorem B2173793 : Blo 1447543 2173793 := bstep (se 2 (by rfl) ⟨815172, by rfl⟩ : syracuseStep 2173793 = 1630345) B1630345
theorem B2173811 : Blo 1447543 2173811 := bstep (se 1 (by rfl) ⟨1630358, by rfl⟩ : syracuseStep 2173811 = 3260717) B3260717
theorem B2444161 : Blo 1447543 2444161 := bstep (se 2 (by rfl) ⟨916560, by rfl⟩ : syracuseStep 2444161 = 1833121) B1833121
theorem B2173841 : Blo 1447543 2173841 := bstep (se 2 (by rfl) ⟨815190, by rfl⟩ : syracuseStep 2173841 = 1630381) B1630381
theorem B2444195 : Blo 1447543 2444195 := bstep (se 1 (by rfl) ⟨1833146, by rfl⟩ : syracuseStep 2444195 = 3666293) B3666293
theorem B2173859 : Blo 1447543 2173859 := bstep (se 1 (by rfl) ⟨1630394, by rfl⟩ : syracuseStep 2173859 = 3260789) B3260789
theorem B2173889 : Blo 1447543 2173889 := bstep (se 2 (by rfl) ⟨815208, by rfl⟩ : syracuseStep 2173889 = 1630417) B1630417
theorem B3664835 : Blo 1447543 3664835 := bstep (se 1 (by rfl) ⟨2748626, by rfl⟩ : syracuseStep 3664835 = 5497253) B5497253
theorem B2173907 : Blo 1447543 2173907 := bstep (se 1 (by rfl) ⟨1630430, by rfl⟩ : syracuseStep 2173907 = 3260861) B3260861
theorem B10996721 : Blo 1447543 10996721 := bstep (se 2 (by rfl) ⟨4123770, by rfl⟩ : syracuseStep 10996721 = 8247541) B8247541
theorem B2173937 : Blo 1447543 2173937 := bstep (se 2 (by rfl) ⟨815226, by rfl⟩ : syracuseStep 2173937 = 1630453) B1630453
theorem B2173955 : Blo 1447543 2173955 := bstep (se 1 (by rfl) ⟨1630466, by rfl⟩ : syracuseStep 2173955 = 3260933) B3260933
theorem B2173985 : Blo 1447543 2173985 := bstep (se 2 (by rfl) ⟨815244, by rfl⟩ : syracuseStep 2173985 = 1630489) B1630489
theorem B2444323 : Blo 1447543 2444323 := bstep (se 1 (by rfl) ⟨1833242, by rfl⟩ : syracuseStep 2444323 = 3666485) B3666485
theorem B1739827 : Blo 1447543 1739827 := bstep (se 1 (by rfl) ⟨1304870, by rfl⟩ : syracuseStep 1739827 = 2609741) B2609741
theorem B2174003 : Blo 1447543 2174003 := bstep (se 1 (by rfl) ⟨1630502, by rfl⟩ : syracuseStep 2174003 = 3261005) B3261005
theorem B2174033 : Blo 1447543 2174033 := bstep (se 2 (by rfl) ⟨815262, by rfl⟩ : syracuseStep 2174033 = 1630525) B1630525
theorem B2174051 : Blo 1447543 2174051 := bstep (se 1 (by rfl) ⟨1630538, by rfl⟩ : syracuseStep 2174051 = 3261077) B3261077
theorem B7056497 : Blo 1447543 7056497 := bstep (se 2 (by rfl) ⟨2646186, by rfl⟩ : syracuseStep 7056497 = 5292373) B5292373
theorem B31755377 : Blo 1447543 31755377 := bstep (se 2 (by rfl) ⟨11908266, by rfl⟩ : syracuseStep 31755377 = 23816533) B23816533
theorem B2174081 : Blo 1447543 2174081 := bstep (se 2 (by rfl) ⟨815280, by rfl⟩ : syracuseStep 2174081 = 1630561) B1630561
theorem B3665027 : Blo 1447543 3665027 := bstep (se 1 (by rfl) ⟨2748770, by rfl⟩ : syracuseStep 3665027 = 5497541) B5497541
theorem B4885649 : Blo 1447543 4885649 := bstep (se 2 (by rfl) ⟨1832118, by rfl⟩ : syracuseStep 4885649 = 3664237) B3664237
theorem B2174099 : Blo 1447543 2174099 := bstep (se 1 (by rfl) ⟨1630574, by rfl⟩ : syracuseStep 2174099 = 3261149) B3261149
theorem B2321569 : Blo 1447543 2321569 := bstep (se 2 (by rfl) ⟨870588, by rfl⟩ : syracuseStep 2321569 = 1741177) B1741177
theorem B2444465 : Blo 1447543 2444465 := bstep (se 2 (by rfl) ⟨916674, by rfl⟩ : syracuseStep 2444465 = 1833349) B1833349
theorem B2174129 : Blo 1447543 2174129 := bstep (se 2 (by rfl) ⟨815298, by rfl⟩ : syracuseStep 2174129 = 1630597) B1630597
theorem B2174147 : Blo 1447543 2174147 := bstep (se 1 (by rfl) ⟨1630610, by rfl⟩ : syracuseStep 2174147 = 3261221) B3261221
theorem B4639949 : Blo 1447543 4639949 := bstep (se 3 (by rfl) ⟨869990, by rfl⟩ : syracuseStep 4639949 = 1739981) B1739981
theorem B2174177 : Blo 1447543 2174177 := bstep (se 2 (by rfl) ⟨815316, by rfl⟩ : syracuseStep 2174177 = 1630633) B1630633
theorem B4123885 : Blo 1447543 4123885 := bstep (se 3 (by rfl) ⟨773228, by rfl⟩ : syracuseStep 4123885 = 1546457) B1546457
theorem B5573873 : Blo 1447543 5573873 := bstep (se 2 (by rfl) ⟨2090202, by rfl⟩ : syracuseStep 5573873 = 4180405) B4180405
theorem B2174195 : Blo 1447543 2174195 := bstep (se 1 (by rfl) ⟨1630646, by rfl⟩ : syracuseStep 2174195 = 3261293) B3261293
theorem B1789171 : Blo 1447543 1789171 := bstep (se 1 (by rfl) ⟨1341878, by rfl⟩ : syracuseStep 1789171 = 2683757) B2683757
theorem B2174225 : Blo 1447543 2174225 := bstep (se 2 (by rfl) ⟨815334, by rfl⟩ : syracuseStep 2174225 = 1630669) B1630669
theorem B2174243 : Blo 1447543 2174243 := bstep (se 1 (by rfl) ⟨1630682, by rfl⟩ : syracuseStep 2174243 = 3261365) B3261365
theorem B2444593 : Blo 1447543 2444593 := bstep (se 2 (by rfl) ⟨916722, by rfl⟩ : syracuseStep 2444593 = 1833445) B1833445
theorem B7154993 : Blo 1447543 7154993 := bstep (se 2 (by rfl) ⟨2683122, by rfl⟩ : syracuseStep 7154993 = 5366245) B5366245
theorem B2174273 : Blo 1447543 2174273 := bstep (se 2 (by rfl) ⟨815352, by rfl⟩ : syracuseStep 2174273 = 1630705) B1630705
theorem B2444627 : Blo 1447543 2444627 := bstep (se 1 (by rfl) ⟨1833470, by rfl⟩ : syracuseStep 2444627 = 3666941) B3666941
theorem B2174291 : Blo 1447543 2174291 := bstep (se 1 (by rfl) ⟨1630718, by rfl⟩ : syracuseStep 2174291 = 3261437) B3261437
theorem B4402637 : Blo 1447543 4402637 := bstep (se 3 (by rfl) ⟨825494, by rfl⟩ : syracuseStep 4402637 = 1650989) B1650989
theorem B2444755 : Blo 1447543 2444755 := bstep (se 1 (by rfl) ⟨1833566, by rfl⟩ : syracuseStep 2444755 = 3667133) B3667133
theorem B7826993 : Blo 1447543 7826993 := bstep (se 2 (by rfl) ⟨2935122, by rfl⟩ : syracuseStep 7826993 = 5870245) B5870245
theorem B2444897 : Blo 1447543 2444897 := bstep (se 2 (by rfl) ⟨916836, by rfl⟩ : syracuseStep 2444897 = 1833673) B1833673
theorem B20868749 : Blo 1447543 20868749 := bstep (se 3 (by rfl) ⟨3912890, by rfl⟩ : syracuseStep 20868749 = 7825781) B7825781
theorem B8244899 : Blo 1447543 8244899 := bstep (se 1 (by rfl) ⟨6183674, by rfl⟩ : syracuseStep 8244899 = 12367349) B12367349
theorem B4886189 : Blo 1447543 4886189 := bstep (se 3 (by rfl) ⟨916160, by rfl⟩ : syracuseStep 4886189 = 1832321) B1832321
theorem B2445025 : Blo 1447543 2445025 := bstep (se 2 (by rfl) ⟨916884, by rfl⟩ : syracuseStep 2445025 = 1833769) B1833769
theorem B4886243 : Blo 1447543 4886243 := bstep (se 1 (by rfl) ⟨3664682, by rfl⟩ : syracuseStep 4886243 = 7329365) B7329365
theorem B2748163 : Blo 1447543 2748163 := bstep (se 1 (by rfl) ⟨2061122, by rfl⟩ : syracuseStep 2748163 = 4122245) B4122245
theorem B2445059 : Blo 1447543 2445059 := bstep (se 1 (by rfl) ⟨1833794, by rfl⟩ : syracuseStep 2445059 = 3667589) B3667589
theorem B2477873 : Blo 1447543 2477873 := bstep (se 2 (by rfl) ⟨929202, by rfl⟩ : syracuseStep 2477873 = 1858405) B1858405
theorem B2445187 : Blo 1447543 2445187 := bstep (se 1 (by rfl) ⟨1833890, by rfl⟩ : syracuseStep 2445187 = 3667781) B3667781
theorem B2748323 : Blo 1447543 2748323 := bstep (se 1 (by rfl) ⟨2061242, by rfl⟩ : syracuseStep 2748323 = 4122485) B4122485
theorem B4886513 : Blo 1447543 4886513 := bstep (se 2 (by rfl) ⟨1832442, by rfl⟩ : syracuseStep 4886513 = 3664885) B3664885
theorem B9285637 : Blo 1447543 9285637 := bstep (se 4 (by rfl) ⟨870528, by rfl⟩ : syracuseStep 9285637 = 1741057) B1741057
theorem B2445329 : Blo 1447543 2445329 := bstep (se 2 (by rfl) ⟨916998, by rfl⟩ : syracuseStep 2445329 = 1833997) B1833997
theorem B3665969 : Blo 1447543 3665969 := bstep (se 2 (by rfl) ⟨1374738, by rfl⟩ : syracuseStep 3665969 = 2749477) B2749477
theorem B3666019 : Blo 1447543 3666019 := bstep (se 1 (by rfl) ⟨2749514, by rfl⟩ : syracuseStep 3666019 = 5499029) B5499029
theorem B2445457 : Blo 1447543 2445457 := bstep (se 2 (by rfl) ⟨917046, by rfl⟩ : syracuseStep 2445457 = 1834093) B1834093
theorem B2445491 : Blo 1447543 2445491 := bstep (se 1 (by rfl) ⟨1834118, by rfl⟩ : syracuseStep 2445491 = 3668237) B3668237
theorem B7827683 : Blo 1447543 7827683 := bstep (se 1 (by rfl) ⟨5870762, by rfl⟩ : syracuseStep 7827683 = 11741525) B11741525
theorem B5501155 : Blo 1447543 5501155 := bstep (se 1 (by rfl) ⟨4125866, by rfl⟩ : syracuseStep 5501155 = 8251733) B8251733
theorem B3666161 : Blo 1447543 3666161 := bstep (se 2 (by rfl) ⟨1374810, by rfl⟩ : syracuseStep 3666161 = 2749621) B2749621
theorem B4124945 : Blo 1447543 4124945 := bstep (se 2 (by rfl) ⟨1546854, by rfl⟩ : syracuseStep 4124945 = 3093709) B3093709
theorem B6189347 : Blo 1447543 6189347 := bstep (se 1 (by rfl) ⟨4642010, by rfl⟩ : syracuseStep 6189347 = 9284021) B9284021
theorem B2445619 : Blo 1447543 2445619 := bstep (se 1 (by rfl) ⟨1834214, by rfl⟩ : syracuseStep 2445619 = 3668429) B3668429
theorem B3305873 : Blo 1447543 3305873 := bstep (se 2 (by rfl) ⟨1239702, by rfl⟩ : syracuseStep 3305873 = 2479405) B2479405
theorem B2478529 : Blo 1447543 2478529 := bstep (se 2 (by rfl) ⟨929448, by rfl⟩ : syracuseStep 2478529 = 1858897) B1858897
theorem B2445761 : Blo 1447543 2445761 := bstep (se 2 (by rfl) ⟨917160, by rfl⟩ : syracuseStep 2445761 = 1834321) B1834321
theorem B8811013 : Blo 1447543 8811013 := bstep (se 4 (by rfl) ⟨826032, by rfl⟩ : syracuseStep 8811013 = 1652065) B1652065
theorem B4887053 : Blo 1447543 4887053 := bstep (se 3 (by rfl) ⟨916322, by rfl⟩ : syracuseStep 4887053 = 1832645) B1832645
theorem B4641293 : Blo 1447543 4641293 := bstep (se 3 (by rfl) ⟨870242, by rfl⟩ : syracuseStep 4641293 = 1740485) B1740485
theorem B2445889 : Blo 1447543 2445889 := bstep (se 2 (by rfl) ⟨917208, by rfl⟩ : syracuseStep 2445889 = 1834417) B1834417
theorem B4887107 : Blo 1447543 4887107 := bstep (se 1 (by rfl) ⟨3665330, by rfl⟩ : syracuseStep 4887107 = 7330661) B7330661
theorem B2445923 : Blo 1447543 2445923 := bstep (se 1 (by rfl) ⟨1834442, by rfl⟩ : syracuseStep 2445923 = 3668885) B3668885
theorem B8245901 : Blo 1447543 8245901 := bstep (se 3 (by rfl) ⟨1546106, by rfl⟩ : syracuseStep 8245901 = 3092213) B3092213
theorem B2478755 : Blo 1447543 2478755 := bstep (se 1 (by rfl) ⟨1859066, by rfl⟩ : syracuseStep 2478755 = 3718133) B3718133
theorem B3257009 : Blo 1447543 3257009 := bstep (se 2 (by rfl) ⟨1221378, by rfl⟩ : syracuseStep 3257009 = 2442757) B2442757
theorem B3257027 : Blo 1447543 3257027 := bstep (se 1 (by rfl) ⟨2442770, by rfl⟩ : syracuseStep 3257027 = 4885541) B4885541
theorem B11899619 : Blo 1447543 11899619 := bstep (se 1 (by rfl) ⟨8924714, by rfl⟩ : syracuseStep 11899619 = 17849429) B17849429
theorem B2446051 : Blo 1447543 2446051 := bstep (se 1 (by rfl) ⟨1834538, by rfl⟩ : syracuseStep 2446051 = 3669077) B3669077
theorem B4887377 : Blo 1447543 4887377 := bstep (se 2 (by rfl) ⟨1832766, by rfl⟩ : syracuseStep 4887377 = 3665533) B3665533
theorem B7336817 : Blo 1447543 7336817 := bstep (se 2 (by rfl) ⟨2751306, by rfl⟩ : syracuseStep 7336817 = 5502613) B5502613
theorem B4125617 : Blo 1447543 4125617 := bstep (se 2 (by rfl) ⟨1547106, by rfl⟩ : syracuseStep 4125617 = 3094213) B3094213
theorem B7328717 : Blo 1447543 7328717 := bstep (se 3 (by rfl) ⟨1374134, by rfl⟩ : syracuseStep 7328717 = 2748269) B2748269
theorem B3257297 : Blo 1447543 3257297 := bstep (se 2 (by rfl) ⟨1221486, by rfl⟩ : syracuseStep 3257297 = 2442973) B2442973
theorem B2749393 : Blo 1447543 2749393 := bstep (se 2 (by rfl) ⟨1031022, by rfl⟩ : syracuseStep 2749393 = 2062045) B2062045
theorem B3257315 : Blo 1447543 3257315 := bstep (se 1 (by rfl) ⟨2442986, by rfl⟩ : syracuseStep 3257315 = 4885973) B4885973
theorem B2061379 : Blo 1447543 2061379 := bstep (se 1 (by rfl) ⟨1546034, by rfl⟩ : syracuseStep 2061379 = 3092069) B3092069
theorem B2479187 : Blo 1447543 2479187 := bstep (se 1 (by rfl) ⟨1859390, by rfl⟩ : syracuseStep 2479187 = 3718781) B3718781
theorem B12375139 : Blo 1447543 12375139 := bstep (se 1 (by rfl) ⟨9281354, by rfl⟩ : syracuseStep 12375139 = 18562709) B18562709
theorem B5289101 : Blo 1447543 5289101 := bstep (se 3 (by rfl) ⟨991706, by rfl⟩ : syracuseStep 5289101 = 1983413) B1983413
theorem B2610353 : Blo 1447543 2610353 := bstep (se 2 (by rfl) ⟨978882, by rfl⟩ : syracuseStep 2610353 = 1957765) B1957765
theorem B3667153 : Blo 1447543 3667153 := bstep (se 2 (by rfl) ⟨1375182, by rfl⟩ : syracuseStep 3667153 = 2750365) B2750365
theorem B3257585 : Blo 1447543 3257585 := bstep (se 2 (by rfl) ⟨1221594, by rfl⟩ : syracuseStep 3257585 = 2443189) B2443189
theorem B3257603 : Blo 1447543 3257603 := bstep (se 1 (by rfl) ⟨2443202, by rfl⟩ : syracuseStep 3257603 = 4886405) B4886405
theorem B4887917 : Blo 1447543 4887917 := bstep (se 3 (by rfl) ⟨916484, by rfl⟩ : syracuseStep 4887917 = 1832969) B1832969
theorem B2061715 : Blo 1447543 2061715 := bstep (se 1 (by rfl) ⟨1546286, by rfl⟩ : syracuseStep 2061715 = 3092573) B3092573
theorem B4887971 : Blo 1447543 4887971 := bstep (se 1 (by rfl) ⟨3665978, by rfl⟩ : syracuseStep 4887971 = 7331957) B7331957
theorem B3667427 : Blo 1447543 3667427 := bstep (se 1 (by rfl) ⟨2750570, by rfl⟩ : syracuseStep 3667427 = 5501141) B5501141
theorem B6190577 : Blo 1447543 6190577 := bstep (se 2 (by rfl) ⟨2321466, by rfl⟩ : syracuseStep 6190577 = 4642933) B4642933
theorem B3257873 : Blo 1447543 3257873 := bstep (se 2 (by rfl) ⟨1221702, by rfl⟩ : syracuseStep 3257873 = 2443405) B2443405
theorem B1832483 : Blo 1447543 1832483 := bstep (se 1 (by rfl) ⟨1374362, by rfl⟩ : syracuseStep 1832483 = 2748725) B2748725
theorem B3257891 : Blo 1447543 3257891 := bstep (se 1 (by rfl) ⟨2443418, by rfl⟩ : syracuseStep 3257891 = 4886837) B4886837
theorem B3094051 : Blo 1447543 3094051 := bstep (se 1 (by rfl) ⟨2320538, by rfl⟩ : syracuseStep 3094051 = 4641077) B4641077
theorem B6035057 : Blo 1447543 6035057 := bstep (se 2 (by rfl) ⟨2263146, by rfl⟩ : syracuseStep 6035057 = 4526293) B4526293
theorem B1447555 : Blo 1447543 1447555 := bstep (se 1 (by rfl) ⟨1085666, by rfl⟩ : syracuseStep 1447555 = 2171333) B2171333
theorem B1447571 : Blo 1447543 1447571 := bstep (se 1 (by rfl) ⟨1085678, by rfl⟩ : syracuseStep 1447571 = 2171357) B2171357
theorem B1447587 : Blo 1447543 1447587 := bstep (se 1 (by rfl) ⟨1085690, by rfl⟩ : syracuseStep 1447587 = 2171381) B2171381
theorem B3667619 : Blo 1447543 3667619 := bstep (se 1 (by rfl) ⟨2750714, by rfl⟩ : syracuseStep 3667619 = 5501429) B5501429
theorem B4888241 : Blo 1447543 4888241 := bstep (se 2 (by rfl) ⟨1833090, by rfl⟩ : syracuseStep 4888241 = 3666181) B3666181
theorem B1447603 : Blo 1447543 1447603 := bstep (se 1 (by rfl) ⟨1085702, by rfl⟩ : syracuseStep 1447603 = 2171405) B2171405
theorem B1447619 : Blo 1447543 1447619 := bstep (se 1 (by rfl) ⟨1085714, by rfl⟩ : syracuseStep 1447619 = 2171429) B2171429
theorem B4126403 : Blo 1447543 4126403 := bstep (se 1 (by rfl) ⟨3094802, by rfl⟩ : syracuseStep 4126403 = 6189605) B6189605
theorem B1447635 : Blo 1447543 1447635 := bstep (se 1 (by rfl) ⟨1085726, by rfl⟩ : syracuseStep 1447635 = 2171453) B2171453
theorem B1447651 : Blo 1447543 1447651 := bstep (se 1 (by rfl) ⟨1085738, by rfl⟩ : syracuseStep 1447651 = 2171477) B2171477
theorem B1447667 : Blo 1447543 1447667 := bstep (se 1 (by rfl) ⟨1085750, by rfl⟩ : syracuseStep 1447667 = 2171501) B2171501
theorem B1447683 : Blo 1447543 1447683 := bstep (se 1 (by rfl) ⟨1085762, by rfl⟩ : syracuseStep 1447683 = 2171525) B2171525
theorem B1447699 : Blo 1447543 1447699 := bstep (se 1 (by rfl) ⟨1085774, by rfl⟩ : syracuseStep 1447699 = 2171549) B2171549
theorem B1447715 : Blo 1447543 1447715 := bstep (se 1 (by rfl) ⟨1085786, by rfl⟩ : syracuseStep 1447715 = 2171573) B2171573
theorem B3258161 : Blo 1447543 3258161 := bstep (se 2 (by rfl) ⟨1221810, by rfl⟩ : syracuseStep 3258161 = 2443621) B2443621
theorem B1447731 : Blo 1447543 1447731 := bstep (se 1 (by rfl) ⟨1085798, by rfl⟩ : syracuseStep 1447731 = 2171597) B2171597
theorem B1447747 : Blo 1447543 1447747 := bstep (se 1 (by rfl) ⟨1085810, by rfl⟩ : syracuseStep 1447747 = 2171621) B2171621
theorem B3258179 : Blo 1447543 3258179 := bstep (se 1 (by rfl) ⟨2443634, by rfl⟩ : syracuseStep 3258179 = 4887269) B4887269
theorem B1447763 : Blo 1447543 1447763 := bstep (se 1 (by rfl) ⟨1085822, by rfl⟩ : syracuseStep 1447763 = 2171645) B2171645
theorem B1447779 : Blo 1447543 1447779 := bstep (se 1 (by rfl) ⟨1085834, by rfl⟩ : syracuseStep 1447779 = 2171669) B2171669
theorem B4462445 : Blo 1447543 4462445 := bstep (se 3 (by rfl) ⟨836708, by rfl⟩ : syracuseStep 4462445 = 1673417) B1673417
theorem B10590065 : Blo 1447543 10590065 := bstep (se 2 (by rfl) ⟨3971274, by rfl⟩ : syracuseStep 10590065 = 7942549) B7942549
theorem B1447795 : Blo 1447543 1447795 := bstep (se 1 (by rfl) ⟨1085846, by rfl⟩ : syracuseStep 1447795 = 2171693) B2171693
theorem B1447811 : Blo 1447543 1447811 := bstep (se 1 (by rfl) ⟨1085858, by rfl⟩ : syracuseStep 1447811 = 2171717) B2171717
theorem B1447827 : Blo 1447543 1447827 := bstep (se 1 (by rfl) ⟨1085870, by rfl⟩ : syracuseStep 1447827 = 2171741) B2171741
theorem B1447843 : Blo 1447543 1447843 := bstep (se 1 (by rfl) ⟨1085882, by rfl⟩ : syracuseStep 1447843 = 2171765) B2171765
theorem B1447859 : Blo 1447543 1447859 := bstep (se 1 (by rfl) ⟨1085894, by rfl⟩ : syracuseStep 1447859 = 2171789) B2171789
theorem B2062273 : Blo 1447543 2062273 := bstep (se 2 (by rfl) ⟨773352, by rfl⟩ : syracuseStep 2062273 = 1546705) B1546705
theorem B1447875 : Blo 1447543 1447875 := bstep (se 1 (by rfl) ⟨1085906, by rfl⟩ : syracuseStep 1447875 = 2171813) B2171813
theorem B1447891 : Blo 1447543 1447891 := bstep (se 1 (by rfl) ⟨1085918, by rfl⟩ : syracuseStep 1447891 = 2171837) B2171837
theorem B1447907 : Blo 1447543 1447907 := bstep (se 1 (by rfl) ⟨1085930, by rfl⟩ : syracuseStep 1447907 = 2171861) B2171861
theorem B2062307 : Blo 1447543 2062307 := bstep (se 1 (by rfl) ⟨1546730, by rfl⟩ : syracuseStep 2062307 = 3093461) B3093461
theorem B2750449 : Blo 1447543 2750449 := bstep (se 2 (by rfl) ⟨1031418, by rfl⟩ : syracuseStep 2750449 = 2062837) B2062837
theorem B1447923 : Blo 1447543 1447923 := bstep (se 1 (by rfl) ⟨1085942, by rfl⟩ : syracuseStep 1447923 = 2171885) B2171885
theorem B1447939 : Blo 1447543 1447939 := bstep (se 1 (by rfl) ⟨1085954, by rfl⟩ : syracuseStep 1447939 = 2171909) B2171909
theorem B4126733 : Blo 1447543 4126733 := bstep (se 3 (by rfl) ⟨773762, by rfl⟩ : syracuseStep 4126733 = 1547525) B1547525
theorem B1447955 : Blo 1447543 1447955 := bstep (se 1 (by rfl) ⟨1085966, by rfl⟩ : syracuseStep 1447955 = 2171933) B2171933
theorem B1447971 : Blo 1447543 1447971 := bstep (se 1 (by rfl) ⟨1085978, by rfl⟩ : syracuseStep 1447971 = 2171957) B2171957
theorem B1447987 : Blo 1447543 1447987 := bstep (se 1 (by rfl) ⟨1085990, by rfl⟩ : syracuseStep 1447987 = 2171981) B2171981
theorem B1448003 : Blo 1447543 1448003 := bstep (se 1 (by rfl) ⟨1086002, by rfl⟩ : syracuseStep 1448003 = 2172005) B2172005
theorem B4642883 : Blo 1447543 4642883 := bstep (se 1 (by rfl) ⟨3482162, by rfl⟩ : syracuseStep 4642883 = 6964325) B6964325
theorem B3258449 : Blo 1447543 3258449 := bstep (se 2 (by rfl) ⟨1221918, by rfl⟩ : syracuseStep 3258449 = 2443837) B2443837
theorem B4126801 : Blo 1447543 4126801 := bstep (se 2 (by rfl) ⟨1547550, by rfl⟩ : syracuseStep 4126801 = 3095101) B3095101
theorem B1448019 : Blo 1447543 1448019 := bstep (se 1 (by rfl) ⟨1086014, by rfl⟩ : syracuseStep 1448019 = 2172029) B2172029
theorem B1448035 : Blo 1447543 1448035 := bstep (se 1 (by rfl) ⟨1086026, by rfl⟩ : syracuseStep 1448035 = 2172053) B2172053
theorem B3258467 : Blo 1447543 3258467 := bstep (se 1 (by rfl) ⟨2443850, by rfl⟩ : syracuseStep 3258467 = 4887701) B4887701
theorem B1448051 : Blo 1447543 1448051 := bstep (se 1 (by rfl) ⟨1086038, by rfl⟩ : syracuseStep 1448051 = 2172077) B2172077
theorem B1448067 : Blo 1447543 1448067 := bstep (se 1 (by rfl) ⟨1086050, by rfl⟩ : syracuseStep 1448067 = 2172101) B2172101
theorem B13924493 : Blo 1447543 13924493 := bstep (se 3 (by rfl) ⟨2610842, by rfl⟩ : syracuseStep 13924493 = 5221685) B5221685
theorem B1448083 : Blo 1447543 1448083 := bstep (se 1 (by rfl) ⟨1086062, by rfl⟩ : syracuseStep 1448083 = 2172125) B2172125
theorem B1448099 : Blo 1447543 1448099 := bstep (se 1 (by rfl) ⟨1086074, by rfl⟩ : syracuseStep 1448099 = 2172149) B2172149
theorem B1448115 : Blo 1447543 1448115 := bstep (se 1 (by rfl) ⟨1086086, by rfl⟩ : syracuseStep 1448115 = 2172173) B2172173
theorem B1448131 : Blo 1447543 1448131 := bstep (se 1 (by rfl) ⟨1086098, by rfl⟩ : syracuseStep 1448131 = 2172197) B2172197
theorem B4888781 : Blo 1447543 4888781 := bstep (se 3 (by rfl) ⟨916646, by rfl⟩ : syracuseStep 4888781 = 1833293) B1833293
theorem B1448147 : Blo 1447543 1448147 := bstep (se 1 (by rfl) ⟨1086110, by rfl⟩ : syracuseStep 1448147 = 2172221) B2172221
theorem B928225493 : Blo 1447543 928225493 := bstep (se 7 (by rfl) ⟨10877642, by rfl⟩ : syracuseStep 928225493 = 21755285) B21755285
theorem B1857763 : Blo 1447543 1857763 := bstep (se 1 (by rfl) ⟨1393322, by rfl⟩ : syracuseStep 1857763 = 2786645) B2786645
theorem B1448163 : Blo 1447543 1448163 := bstep (se 1 (by rfl) ⟨1086122, by rfl⟩ : syracuseStep 1448163 = 2172245) B2172245
theorem B1833187 : Blo 1447543 1833187 := bstep (se 1 (by rfl) ⟨1374890, by rfl⟩ : syracuseStep 1833187 = 2749781) B2749781
theorem B1448179 : Blo 1447543 1448179 := bstep (se 1 (by rfl) ⟨1086134, by rfl⟩ : syracuseStep 1448179 = 2172269) B2172269
theorem B1448195 : Blo 1447543 1448195 := bstep (se 1 (by rfl) ⟨1086146, by rfl⟩ : syracuseStep 1448195 = 2172293) B2172293
theorem B4888835 : Blo 1447543 4888835 := bstep (se 1 (by rfl) ⟨3666626, by rfl⟩ : syracuseStep 4888835 = 7333253) B7333253
theorem B1448211 : Blo 1447543 1448211 := bstep (se 1 (by rfl) ⟨1086158, by rfl⟩ : syracuseStep 1448211 = 2172317) B2172317
theorem B1448227 : Blo 1447543 1448227 := bstep (se 1 (by rfl) ⟨1086170, by rfl⟩ : syracuseStep 1448227 = 2172341) B2172341
theorem B7338275 : Blo 1447543 7338275 := bstep (se 1 (by rfl) ⟨5503706, by rfl⟩ : syracuseStep 7338275 = 11007413) B11007413
theorem B1448243 : Blo 1447543 1448243 := bstep (se 1 (by rfl) ⟨1086182, by rfl⟩ : syracuseStep 1448243 = 2172365) B2172365
theorem B2201921 : Blo 1447543 2201921 := bstep (se 2 (by rfl) ⟨825720, by rfl⟩ : syracuseStep 2201921 = 1651441) B1651441
theorem B1448259 : Blo 1447543 1448259 := bstep (se 1 (by rfl) ⟨1086194, by rfl⟩ : syracuseStep 1448259 = 2172389) B2172389
theorem B1833283 : Blo 1447543 1833283 := bstep (se 1 (by rfl) ⟨1374962, by rfl⟩ : syracuseStep 1833283 = 2749925) B2749925
theorem B1448275 : Blo 1447543 1448275 := bstep (se 1 (by rfl) ⟨1086206, by rfl⟩ : syracuseStep 1448275 = 2172413) B2172413
theorem B1448291 : Blo 1447543 1448291 := bstep (se 1 (by rfl) ⟨1086218, by rfl⟩ : syracuseStep 1448291 = 2172437) B2172437
theorem B4127075 : Blo 1447543 4127075 := bstep (se 1 (by rfl) ⟨3095306, by rfl⟩ : syracuseStep 4127075 = 6190613) B6190613
theorem B3258737 : Blo 1447543 3258737 := bstep (se 2 (by rfl) ⟨1222026, by rfl⟩ : syracuseStep 3258737 = 2444053) B2444053
theorem B1448307 : Blo 1447543 1448307 := bstep (se 1 (by rfl) ⟨1086230, by rfl⟩ : syracuseStep 1448307 = 2172461) B2172461
theorem B1448323 : Blo 1447543 1448323 := bstep (se 1 (by rfl) ⟨1086242, by rfl⟩ : syracuseStep 1448323 = 2172485) B2172485
theorem B3258755 : Blo 1447543 3258755 := bstep (se 1 (by rfl) ⟨2444066, by rfl⟩ : syracuseStep 3258755 = 4888133) B4888133
theorem B2750851 : Blo 1447543 2750851 := bstep (se 1 (by rfl) ⟨2063138, by rfl⟩ : syracuseStep 2750851 = 4126277) B4126277
theorem B11745677 : Blo 1447543 11745677 := bstep (se 3 (by rfl) ⟨2202314, by rfl⟩ : syracuseStep 11745677 = 4404629) B4404629
theorem B5503373 : Blo 1447543 5503373 := bstep (se 3 (by rfl) ⟨1031882, by rfl⟩ : syracuseStep 5503373 = 2063765) B2063765
theorem B1628563 : Blo 1447543 1628563 := bstep (se 1 (by rfl) ⟨1221422, by rfl⟩ : syracuseStep 1628563 = 2442845) B2442845
theorem B1448339 : Blo 1447543 1448339 := bstep (se 1 (by rfl) ⟨1086254, by rfl⟩ : syracuseStep 1448339 = 2172509) B2172509
theorem B1448355 : Blo 1447543 1448355 := bstep (se 1 (by rfl) ⟨1086266, by rfl⟩ : syracuseStep 1448355 = 2172533) B2172533
theorem B2750897 : Blo 1447543 2750897 := bstep (se 2 (by rfl) ⟨1031586, by rfl⟩ : syracuseStep 2750897 = 2063173) B2063173
theorem B7059889 : Blo 1447543 7059889 := bstep (se 2 (by rfl) ⟨2647458, by rfl⟩ : syracuseStep 7059889 = 5294917) B5294917
theorem B1448371 : Blo 1447543 1448371 := bstep (se 1 (by rfl) ⟨1086278, by rfl⟩ : syracuseStep 1448371 = 2172557) B2172557
theorem B1448387 : Blo 1447543 1448387 := bstep (se 1 (by rfl) ⟨1086290, by rfl⟩ : syracuseStep 1448387 = 2172581) B2172581
theorem B3914189 : Blo 1447543 3914189 := bstep (se 3 (by rfl) ⟨733910, by rfl⟩ : syracuseStep 3914189 = 1467821) B1467821
theorem B1448403 : Blo 1447543 1448403 := bstep (se 1 (by rfl) ⟨1086302, by rfl⟩ : syracuseStep 1448403 = 2172605) B2172605
theorem B1448419 : Blo 1447543 1448419 := bstep (se 1 (by rfl) ⟨1086314, by rfl⟩ : syracuseStep 1448419 = 2172629) B2172629
theorem B1448435 : Blo 1447543 1448435 := bstep (se 1 (by rfl) ⟨1086326, by rfl⟩ : syracuseStep 1448435 = 2172653) B2172653
theorem B1448451 : Blo 1447543 1448451 := bstep (se 1 (by rfl) ⟨1086338, by rfl⟩ : syracuseStep 1448451 = 2172677) B2172677
theorem B4889105 : Blo 1447543 4889105 := bstep (se 2 (by rfl) ⟨1833414, by rfl⟩ : syracuseStep 4889105 = 3666829) B3666829
theorem B1448467 : Blo 1447543 1448467 := bstep (se 1 (by rfl) ⟨1086350, by rfl⟩ : syracuseStep 1448467 = 2172701) B2172701
theorem B2062865 : Blo 1447543 2062865 := bstep (se 2 (by rfl) ⟨773574, by rfl⟩ : syracuseStep 2062865 = 1547149) B1547149
theorem B1628707 : Blo 1447543 1628707 := bstep (se 1 (by rfl) ⟨1221530, by rfl⟩ : syracuseStep 1628707 = 2443061) B2443061
theorem B1448483 : Blo 1447543 1448483 := bstep (se 1 (by rfl) ⟨1086362, by rfl⟩ : syracuseStep 1448483 = 2172725) B2172725
theorem B1448499 : Blo 1447543 1448499 := bstep (se 1 (by rfl) ⟨1086374, by rfl⟩ : syracuseStep 1448499 = 2172749) B2172749
theorem B1448515 : Blo 1447543 1448515 := bstep (se 1 (by rfl) ⟨1086386, by rfl⟩ : syracuseStep 1448515 = 2172773) B2172773
theorem B3668561 : Blo 1447543 3668561 := bstep (se 2 (by rfl) ⟨1375710, by rfl⟩ : syracuseStep 3668561 = 2751421) B2751421
theorem B1448531 : Blo 1447543 1448531 := bstep (se 1 (by rfl) ⟨1086398, by rfl⟩ : syracuseStep 1448531 = 2172797) B2172797
theorem B2062945 : Blo 1447543 2062945 := bstep (se 2 (by rfl) ⟨773604, by rfl⟩ : syracuseStep 2062945 = 1547209) B1547209
theorem B13916771 : Blo 1447543 13916771 := bstep (se 1 (by rfl) ⟨10437578, by rfl⟩ : syracuseStep 13916771 = 20875157) B20875157
theorem B1448547 : Blo 1447543 1448547 := bstep (se 1 (by rfl) ⟨1086410, by rfl⟩ : syracuseStep 1448547 = 2172821) B2172821
theorem B1546867 : Blo 1447543 1546867 := bstep (se 1 (by rfl) ⟨1160150, by rfl⟩ : syracuseStep 1546867 = 2320301) B2320301
theorem B1448563 : Blo 1447543 1448563 := bstep (se 1 (by rfl) ⟨1086422, by rfl⟩ : syracuseStep 1448563 = 2172845) B2172845
theorem B1448579 : Blo 1447543 1448579 := bstep (se 1 (by rfl) ⟨1086434, by rfl⟩ : syracuseStep 1448579 = 2172869) B2172869
theorem B3668611 : Blo 1447543 3668611 := bstep (se 1 (by rfl) ⟨2751458, by rfl⟩ : syracuseStep 3668611 = 5502917) B5502917
theorem B3259025 : Blo 1447543 3259025 := bstep (se 2 (by rfl) ⟨1222134, by rfl⟩ : syracuseStep 3259025 = 2444269) B2444269
theorem B1448595 : Blo 1447543 1448595 := bstep (se 1 (by rfl) ⟨1086446, by rfl⟩ : syracuseStep 1448595 = 2172893) B2172893
theorem B3259043 : Blo 1447543 3259043 := bstep (se 1 (by rfl) ⟨2444282, by rfl⟩ : syracuseStep 3259043 = 4888565) B4888565
theorem B1448611 : Blo 1447543 1448611 := bstep (se 1 (by rfl) ⟨1086458, by rfl⟩ : syracuseStep 1448611 = 2172917) B2172917
theorem B1628851 : Blo 1447543 1628851 := bstep (se 1 (by rfl) ⟨1221638, by rfl⟩ : syracuseStep 1628851 = 2443277) B2443277
theorem B1448627 : Blo 1447543 1448627 := bstep (se 1 (by rfl) ⟨1086470, by rfl⟩ : syracuseStep 1448627 = 2172941) B2172941
theorem B1448643 : Blo 1447543 1448643 := bstep (se 1 (by rfl) ⟨1086482, by rfl⟩ : syracuseStep 1448643 = 2172965) B2172965
theorem B2751185 : Blo 1447543 2751185 := bstep (se 2 (by rfl) ⟨1031694, by rfl⟩ : syracuseStep 2751185 = 2063389) B2063389
theorem B1448659 : Blo 1447543 1448659 := bstep (se 1 (by rfl) ⟨1086494, by rfl⟩ : syracuseStep 1448659 = 2172989) B2172989
theorem B1448675 : Blo 1447543 1448675 := bstep (se 1 (by rfl) ⟨1086506, by rfl⟩ : syracuseStep 1448675 = 2173013) B2173013
theorem B2611939 : Blo 1447543 2611939 := bstep (se 1 (by rfl) ⟨1958954, by rfl⟩ : syracuseStep 2611939 = 3917909) B3917909
theorem B1448691 : Blo 1447543 1448691 := bstep (se 1 (by rfl) ⟨1086518, by rfl⟩ : syracuseStep 1448691 = 2173037) B2173037
theorem B1448707 : Blo 1447543 1448707 := bstep (se 1 (by rfl) ⟨1086530, by rfl⟩ : syracuseStep 1448707 = 2173061) B2173061
theorem B3668753 : Blo 1447543 3668753 := bstep (se 2 (by rfl) ⟨1375782, by rfl⟩ : syracuseStep 3668753 = 2751565) B2751565
theorem B1448723 : Blo 1447543 1448723 := bstep (se 1 (by rfl) ⟨1086542, by rfl⟩ : syracuseStep 1448723 = 2173085) B2173085
theorem B1448739 : Blo 1447543 1448739 := bstep (se 1 (by rfl) ⟨1086554, by rfl⟩ : syracuseStep 1448739 = 2173109) B2173109
theorem B1448755 : Blo 1447543 1448755 := bstep (se 1 (by rfl) ⟨1086566, by rfl⟩ : syracuseStep 1448755 = 2173133) B2173133
theorem B1833779 : Blo 1447543 1833779 := bstep (se 1 (by rfl) ⟨1375334, by rfl⟩ : syracuseStep 1833779 = 2750669) B2750669
theorem B1628995 : Blo 1447543 1628995 := bstep (se 1 (by rfl) ⟨1221746, by rfl⟩ : syracuseStep 1628995 = 2443493) B2443493
theorem B1448771 : Blo 1447543 1448771 := bstep (se 1 (by rfl) ⟨1086578, by rfl⟩ : syracuseStep 1448771 = 2173157) B2173157
theorem B4643651 : Blo 1447543 4643651 := bstep (se 1 (by rfl) ⟨3482738, by rfl⟩ : syracuseStep 4643651 = 6965477) B6965477
theorem B1448787 : Blo 1447543 1448787 := bstep (se 1 (by rfl) ⟨1086590, by rfl⟩ : syracuseStep 1448787 = 2173181) B2173181
theorem B1448803 : Blo 1447543 1448803 := bstep (se 1 (by rfl) ⟨1086602, by rfl⟩ : syracuseStep 1448803 = 2173205) B2173205
theorem B1448819 : Blo 1447543 1448819 := bstep (se 1 (by rfl) ⟨1086614, by rfl⟩ : syracuseStep 1448819 = 2173229) B2173229
theorem B1448835 : Blo 1447543 1448835 := bstep (se 1 (by rfl) ⟨1086626, by rfl⟩ : syracuseStep 1448835 = 2173253) B2173253
theorem B13220749 : Blo 1447543 13220749 := bstep (se 3 (by rfl) ⟨2478890, by rfl⟩ : syracuseStep 13220749 = 4957781) B4957781
theorem B1448851 : Blo 1447543 1448851 := bstep (se 1 (by rfl) ⟨1086638, by rfl⟩ : syracuseStep 1448851 = 2173277) B2173277
theorem B1448867 : Blo 1447543 1448867 := bstep (se 1 (by rfl) ⟨1086650, by rfl⟩ : syracuseStep 1448867 = 2173301) B2173301
theorem B9280433 : Blo 1447543 9280433 := bstep (se 2 (by rfl) ⟨3480162, by rfl⟩ : syracuseStep 9280433 = 6960325) B6960325
theorem B3259313 : Blo 1447543 3259313 := bstep (se 2 (by rfl) ⟨1222242, by rfl⟩ : syracuseStep 3259313 = 2444485) B2444485
theorem B1448883 : Blo 1447543 1448883 := bstep (se 1 (by rfl) ⟨1086662, by rfl⟩ : syracuseStep 1448883 = 2173325) B2173325
theorem B1956803 : Blo 1447543 1956803 := bstep (se 1 (by rfl) ⟨1467602, by rfl⟩ : syracuseStep 1956803 = 2935205) B2935205
theorem B3259331 : Blo 1447543 3259331 := bstep (se 1 (by rfl) ⟨2444498, by rfl⟩ : syracuseStep 3259331 = 4888997) B4888997
theorem B1448899 : Blo 1447543 1448899 := bstep (se 1 (by rfl) ⟨1086674, by rfl⟩ : syracuseStep 1448899 = 2173349) B2173349
theorem B1629139 : Blo 1447543 1629139 := bstep (se 1 (by rfl) ⟨1221854, by rfl⟩ : syracuseStep 1629139 = 2443709) B2443709
theorem B1448915 : Blo 1447543 1448915 := bstep (se 1 (by rfl) ⟨1086686, by rfl⟩ : syracuseStep 1448915 = 2173373) B2173373
theorem B1956835 : Blo 1447543 1956835 := bstep (se 1 (by rfl) ⟨1467626, by rfl⟩ : syracuseStep 1956835 = 2935253) B2935253
theorem B1448931 : Blo 1447543 1448931 := bstep (se 1 (by rfl) ⟨1086698, by rfl⟩ : syracuseStep 1448931 = 2173397) B2173397
theorem B1448947 : Blo 1447543 1448947 := bstep (se 1 (by rfl) ⟨1086710, by rfl⟩ : syracuseStep 1448947 = 2173421) B2173421
theorem B1448963 : Blo 1447543 1448963 := bstep (se 1 (by rfl) ⟨1086722, by rfl⟩ : syracuseStep 1448963 = 2173445) B2173445
theorem B1448979 : Blo 1447543 1448979 := bstep (se 1 (by rfl) ⟨1086734, by rfl⟩ : syracuseStep 1448979 = 2173469) B2173469
theorem B1547299 : Blo 1447543 1547299 := bstep (se 1 (by rfl) ⟨1160474, by rfl⟩ : syracuseStep 1547299 = 2320949) B2320949
theorem B1448995 : Blo 1447543 1448995 := bstep (se 1 (by rfl) ⟨1086746, by rfl⟩ : syracuseStep 1448995 = 2173493) B2173493
theorem B4889645 : Blo 1447543 4889645 := bstep (se 3 (by rfl) ⟨916808, by rfl⟩ : syracuseStep 4889645 = 1833617) B1833617
theorem B1449011 : Blo 1447543 1449011 := bstep (se 1 (by rfl) ⟨1086758, by rfl⟩ : syracuseStep 1449011 = 2173517) B2173517
theorem B1449027 : Blo 1447543 1449027 := bstep (se 1 (by rfl) ⟨1086770, by rfl⟩ : syracuseStep 1449027 = 2173541) B2173541
theorem B1449043 : Blo 1447543 1449043 := bstep (se 1 (by rfl) ⟨1086782, by rfl⟩ : syracuseStep 1449043 = 2173565) B2173565
theorem B1629283 : Blo 1447543 1629283 := bstep (se 1 (by rfl) ⟨1221962, by rfl⟩ : syracuseStep 1629283 = 2443925) B2443925
theorem B4889699 : Blo 1447543 4889699 := bstep (se 1 (by rfl) ⟨3667274, by rfl⟩ : syracuseStep 4889699 = 7334549) B7334549
theorem B1449059 : Blo 1447543 1449059 := bstep (se 1 (by rfl) ⟨1086794, by rfl⟩ : syracuseStep 1449059 = 2173589) B2173589
theorem B1449075 : Blo 1447543 1449075 := bstep (se 1 (by rfl) ⟨1086806, by rfl⟩ : syracuseStep 1449075 = 2173613) B2173613
theorem B1449091 : Blo 1447543 1449091 := bstep (se 1 (by rfl) ⟨1086818, by rfl⟩ : syracuseStep 1449091 = 2173637) B2173637
theorem B1449107 : Blo 1447543 1449107 := bstep (se 1 (by rfl) ⟨1086830, by rfl⟩ : syracuseStep 1449107 = 2173661) B2173661
theorem B1449123 : Blo 1447543 1449123 := bstep (se 1 (by rfl) ⟨1086842, by rfl⟩ : syracuseStep 1449123 = 2173685) B2173685
theorem B1449139 : Blo 1447543 1449139 := bstep (se 1 (by rfl) ⟨1086854, by rfl⟩ : syracuseStep 1449139 = 2173709) B2173709
theorem B1449155 : Blo 1447543 1449155 := bstep (se 1 (by rfl) ⟨1086866, by rfl⟩ : syracuseStep 1449155 = 2173733) B2173733
theorem B3259601 : Blo 1447543 3259601 := bstep (se 2 (by rfl) ⟨1222350, by rfl⟩ : syracuseStep 3259601 = 2444701) B2444701
theorem B1449171 : Blo 1447543 1449171 := bstep (se 1 (by rfl) ⟨1086878, by rfl⟩ : syracuseStep 1449171 = 2173757) B2173757
theorem B3259619 : Blo 1447543 3259619 := bstep (se 1 (by rfl) ⟨2444714, by rfl⟩ : syracuseStep 3259619 = 4889429) B4889429
theorem B1449187 : Blo 1447543 1449187 := bstep (se 1 (by rfl) ⟨1086890, by rfl⟩ : syracuseStep 1449187 = 2173781) B2173781
theorem B1629427 : Blo 1447543 1629427 := bstep (se 1 (by rfl) ⟨1222070, by rfl⟩ : syracuseStep 1629427 = 2444141) B2444141
theorem B1449203 : Blo 1447543 1449203 := bstep (se 1 (by rfl) ⟨1086902, by rfl⟩ : syracuseStep 1449203 = 2173805) B2173805
theorem B1449219 : Blo 1447543 1449219 := bstep (se 1 (by rfl) ⟨1086914, by rfl⟩ : syracuseStep 1449219 = 2173829) B2173829
theorem B1449235 : Blo 1447543 1449235 := bstep (se 1 (by rfl) ⟨1086926, by rfl⟩ : syracuseStep 1449235 = 2173853) B2173853
theorem B1449251 : Blo 1447543 1449251 := bstep (se 1 (by rfl) ⟨1086938, by rfl⟩ : syracuseStep 1449251 = 2173877) B2173877
theorem B1449267 : Blo 1447543 1449267 := bstep (se 1 (by rfl) ⟨1086950, by rfl⟩ : syracuseStep 1449267 = 2173901) B2173901
theorem B1449283 : Blo 1447543 1449283 := bstep (se 1 (by rfl) ⟨1086962, by rfl⟩ : syracuseStep 1449283 = 2173925) B2173925
theorem B1449299 : Blo 1447543 1449299 := bstep (se 1 (by rfl) ⟨1086974, by rfl⟩ : syracuseStep 1449299 = 2173949) B2173949
theorem B1449315 : Blo 1447543 1449315 := bstep (se 1 (by rfl) ⟨1086986, by rfl⟩ : syracuseStep 1449315 = 2173973) B2173973
theorem B4889969 : Blo 1447543 4889969 := bstep (se 2 (by rfl) ⟨1833738, by rfl⟩ : syracuseStep 4889969 = 3667477) B3667477
theorem B1449331 : Blo 1447543 1449331 := bstep (se 1 (by rfl) ⟨1086998, by rfl⟩ : syracuseStep 1449331 = 2173997) B2173997
theorem B2063731 : Blo 1447543 2063731 := bstep (se 1 (by rfl) ⟨1547798, by rfl⟩ : syracuseStep 2063731 = 3095597) B3095597
theorem B1629571 : Blo 1447543 1629571 := bstep (se 1 (by rfl) ⟨1222178, by rfl⟩ : syracuseStep 1629571 = 2444357) B2444357
theorem B1449347 : Blo 1447543 1449347 := bstep (se 1 (by rfl) ⟨1087010, by rfl⟩ : syracuseStep 1449347 = 2174021) B2174021
theorem B1957267 : Blo 1447543 1957267 := bstep (se 1 (by rfl) ⟨1467950, by rfl⟩ : syracuseStep 1957267 = 2935901) B2935901
theorem B1449363 : Blo 1447543 1449363 := bstep (se 1 (by rfl) ⟨1087022, by rfl⟩ : syracuseStep 1449363 = 2174045) B2174045
theorem B1449379 : Blo 1447543 1449379 := bstep (se 1 (by rfl) ⟨1087034, by rfl⟩ : syracuseStep 1449379 = 2174069) B2174069
theorem B1449395 : Blo 1447543 1449395 := bstep (se 1 (by rfl) ⟨1087046, by rfl⟩ : syracuseStep 1449395 = 2174093) B2174093
theorem B1449411 : Blo 1447543 1449411 := bstep (se 1 (by rfl) ⟨1087058, by rfl⟩ : syracuseStep 1449411 = 2174117) B2174117
theorem B1449427 : Blo 1447543 1449427 := bstep (se 1 (by rfl) ⟨1087070, by rfl⟩ : syracuseStep 1449427 = 2174141) B2174141
theorem B18808291 : Blo 1447543 18808291 := bstep (se 1 (by rfl) ⟨14106218, by rfl⟩ : syracuseStep 18808291 = 28212437) B28212437
theorem B1449443 : Blo 1447543 1449443 := bstep (se 1 (by rfl) ⟨1087082, by rfl⟩ : syracuseStep 1449443 = 2174165) B2174165
theorem B8248817 : Blo 1447543 8248817 := bstep (se 2 (by rfl) ⟨3093306, by rfl⟩ : syracuseStep 8248817 = 6186613) B6186613
theorem B3259889 : Blo 1447543 3259889 := bstep (se 2 (by rfl) ⟨1222458, by rfl⟩ : syracuseStep 3259889 = 2444917) B2444917
theorem B1449459 : Blo 1447543 1449459 := bstep (se 1 (by rfl) ⟨1087094, by rfl⟩ : syracuseStep 1449459 = 2174189) B2174189
theorem B1834483 : Blo 1447543 1834483 := bstep (se 1 (by rfl) ⟨1375862, by rfl⟩ : syracuseStep 1834483 = 2751725) B2751725
theorem B3259907 : Blo 1447543 3259907 := bstep (se 1 (by rfl) ⟨2444930, by rfl⟩ : syracuseStep 3259907 = 4889861) B4889861
theorem B1449475 : Blo 1447543 1449475 := bstep (se 1 (by rfl) ⟨1087106, by rfl⟩ : syracuseStep 1449475 = 2174213) B2174213
theorem B1629715 : Blo 1447543 1629715 := bstep (se 1 (by rfl) ⟨1222286, by rfl⟩ : syracuseStep 1629715 = 2444573) B2444573
theorem B1449491 : Blo 1447543 1449491 := bstep (se 1 (by rfl) ⟨1087118, by rfl⟩ : syracuseStep 1449491 = 2174237) B2174237
theorem B1859107 : Blo 1447543 1859107 := bstep (se 1 (by rfl) ⟨1394330, by rfl⟩ : syracuseStep 1859107 = 2788661) B2788661
theorem B1449507 : Blo 1447543 1449507 := bstep (se 1 (by rfl) ⟨1087130, by rfl⟩ : syracuseStep 1449507 = 2174261) B2174261
theorem B1449523 : Blo 1447543 1449523 := bstep (se 1 (by rfl) ⟨1087142, by rfl⟩ : syracuseStep 1449523 = 2174285) B2174285
theorem B1957441 : Blo 1447543 1957441 := bstep (se 2 (by rfl) ⟨734040, by rfl⟩ : syracuseStep 1957441 = 1468081) B1468081
theorem B1449539 : Blo 1447543 1449539 := bstep (se 1 (by rfl) ⟨1087154, by rfl⟩ : syracuseStep 1449539 = 2174309) B2174309
theorem B1834579 : Blo 1447543 1834579 := bstep (se 1 (by rfl) ⟨1375934, by rfl⟩ : syracuseStep 1834579 = 2751869) B2751869
theorem B1629859 : Blo 1447543 1629859 := bstep (se 1 (by rfl) ⟨1222394, by rfl⟩ : syracuseStep 1629859 = 2444789) B2444789
theorem B4406957 : Blo 1447543 4406957 := bstep (se 3 (by rfl) ⟨826304, by rfl⟩ : syracuseStep 4406957 = 1652609) B1652609
theorem B3260177 : Blo 1447543 3260177 := bstep (se 2 (by rfl) ⟨1222566, by rfl⟩ : syracuseStep 3260177 = 2445133) B2445133
theorem B3260195 : Blo 1447543 3260195 := bstep (se 1 (by rfl) ⟨2445146, by rfl⟩ : syracuseStep 3260195 = 4890293) B4890293
theorem B7331633 : Blo 1447543 7331633 := bstep (se 2 (by rfl) ⟨2749362, by rfl⟩ : syracuseStep 7331633 = 5498725) B5498725
theorem B3481393 : Blo 1447543 3481393 := bstep (se 2 (by rfl) ⟨1305522, by rfl⟩ : syracuseStep 3481393 = 2611045) B2611045
theorem B1630003 : Blo 1447543 1630003 := bstep (se 1 (by rfl) ⟨1222502, by rfl⟩ : syracuseStep 1630003 = 2445005) B2445005
theorem B4890509 : Blo 1447543 4890509 := bstep (se 3 (by rfl) ⟨916970, by rfl⟩ : syracuseStep 4890509 = 1833941) B1833941
theorem B1630147 : Blo 1447543 1630147 := bstep (se 1 (by rfl) ⟨1222610, by rfl⟩ : syracuseStep 1630147 = 2445221) B2445221
theorem B4890563 : Blo 1447543 4890563 := bstep (se 1 (by rfl) ⟨3667922, by rfl⟩ : syracuseStep 4890563 = 7335845) B7335845
theorem B5496781 : Blo 1447543 5496781 := bstep (se 3 (by rfl) ⟨1030646, by rfl⟩ : syracuseStep 5496781 = 2061293) B2061293
theorem B23486435 : Blo 1447543 23486435 := bstep (se 1 (by rfl) ⟨17614826, by rfl⟩ : syracuseStep 23486435 = 35229653) B35229653
theorem B1957873 : Blo 1447543 1957873 := bstep (se 2 (by rfl) ⟨734202, by rfl⟩ : syracuseStep 1957873 = 1468405) B1468405
theorem B1630219 : Blo 1447543 1630219 := bstep (se 1 (by rfl) ⟨1222664, by rfl⟩ : syracuseStep 1630219 = 2445329) B2445329
theorem B1630327 : Blo 1447543 1630327 := bstep (se 1 (by rfl) ⟨1222745, by rfl⟩ : syracuseStep 1630327 = 2445491) B2445491
theorem B3260555 : Blo 1447543 3260555 := bstep (se 1 (by rfl) ⟨2445416, by rfl⟩ : syracuseStep 3260555 = 4890833) B4890833
theorem B3260609 : Blo 1447543 3260609 := bstep (se 2 (by rfl) ⟨1222728, by rfl⟩ : syracuseStep 3260609 = 2445457) B2445457
theorem B7635161 : Blo 1447543 7635161 := bstep (se 2 (by rfl) ⟨2863185, by rfl⟩ : syracuseStep 7635161 = 5726371) B5726371
theorem B6611165 : Blo 1447543 6611165 := bstep (se 3 (by rfl) ⟨1239593, by rfl⟩ : syracuseStep 6611165 = 2479187) B2479187
theorem B1630507 : Blo 1447543 1630507 := bstep (se 1 (by rfl) ⟨1222880, by rfl⟩ : syracuseStep 1630507 = 2445761) B2445761
theorem B18817325 : Blo 1447543 18817325 := bstep (se 3 (by rfl) ⟨3528248, by rfl⟩ : syracuseStep 18817325 = 7056497) B7056497
theorem B6185281 : Blo 1447543 6185281 := bstep (se 2 (by rfl) ⟨2319480, by rfl⟩ : syracuseStep 6185281 = 4638961) B4638961
theorem B1630615 : Blo 1447543 1630615 := bstep (se 1 (by rfl) ⟨1222961, by rfl⟩ : syracuseStep 1630615 = 2445923) B2445923
theorem B3260825 : Blo 1447543 3260825 := bstep (se 2 (by rfl) ⟨1222809, by rfl⟩ : syracuseStep 3260825 = 2445619) B2445619
theorem B5497267 : Blo 1447543 5497267 := bstep (se 1 (by rfl) ⟨4122950, by rfl⟩ : syracuseStep 5497267 = 8245901) B8245901
theorem B2171339 : Blo 1447543 2171339 := bstep (se 1 (by rfl) ⟨1628504, by rfl⟩ : syracuseStep 2171339 = 3257009) B3257009
theorem B2171351 : Blo 1447543 2171351 := bstep (se 1 (by rfl) ⟨1628513, by rfl⟩ : syracuseStep 2171351 = 3257027) B3257027
theorem B3260915 : Blo 1447543 3260915 := bstep (se 1 (by rfl) ⟨2445686, by rfl⟩ : syracuseStep 3260915 = 4891373) B4891373
theorem B3260951 : Blo 1447543 3260951 := bstep (se 1 (by rfl) ⟨2445713, by rfl⟩ : syracuseStep 3260951 = 4891427) B4891427
theorem B2171417 : Blo 1447543 2171417 := bstep (se 2 (by rfl) ⟨814281, by rfl⟩ : syracuseStep 2171417 = 1628563) B1628563
theorem B9413185 : Blo 1447543 9413185 := bstep (se 2 (by rfl) ⟨3529944, by rfl⟩ : syracuseStep 9413185 = 7059889) B7059889
theorem B4891211 : Blo 1447543 4891211 := bstep (se 1 (by rfl) ⟨3668408, by rfl⟩ : syracuseStep 4891211 = 7336817) B7336817
theorem B5571161 : Blo 1447543 5571161 := bstep (se 2 (by rfl) ⟨2089185, by rfl⟩ : syracuseStep 5571161 = 4178371) B4178371
theorem B8249957 : Blo 1447543 8249957 := bstep (se 4 (by rfl) ⟨773433, by rfl⟩ : syracuseStep 8249957 = 1546867) B1546867
theorem B2171531 : Blo 1447543 2171531 := bstep (se 1 (by rfl) ⟨1628648, by rfl⟩ : syracuseStep 2171531 = 3257297) B3257297
theorem B2171543 : Blo 1447543 2171543 := bstep (se 1 (by rfl) ⟨1628657, by rfl⟩ : syracuseStep 2171543 = 3257315) B3257315
theorem B11748017 : Blo 1447543 11748017 := bstep (se 2 (by rfl) ⟨4405506, by rfl⟩ : syracuseStep 11748017 = 8811013) B8811013
theorem B3261131 : Blo 1447543 3261131 := bstep (se 1 (by rfl) ⟨2445848, by rfl⟩ : syracuseStep 3261131 = 4891697) B4891697
theorem B2171609 : Blo 1447543 2171609 := bstep (se 2 (by rfl) ⟨814353, by rfl⟩ : syracuseStep 2171609 = 1628707) B1628707
theorem B3261185 : Blo 1447543 3261185 := bstep (se 2 (by rfl) ⟨1222944, by rfl⟩ : syracuseStep 3261185 = 2445889) B2445889
theorem B19079981 : Blo 1447543 19079981 := bstep (se 3 (by rfl) ⟨3577496, by rfl⟩ : syracuseStep 19079981 = 7154993) B7154993
theorem B2171723 : Blo 1447543 2171723 := bstep (se 1 (by rfl) ⟨1628792, by rfl⟩ : syracuseStep 2171723 = 3257585) B3257585
theorem B2171735 : Blo 1447543 2171735 := bstep (se 1 (by rfl) ⟨1628801, by rfl⟩ : syracuseStep 2171735 = 3257603) B3257603
theorem B4891481 : Blo 1447543 4891481 := bstep (se 2 (by rfl) ⟨1834305, by rfl⟩ : syracuseStep 4891481 = 3668611) B3668611
theorem B2171801 : Blo 1447543 2171801 := bstep (se 2 (by rfl) ⟨814425, by rfl⟩ : syracuseStep 2171801 = 1628851) B1628851
theorem B3482585 : Blo 1447543 3482585 := bstep (se 2 (by rfl) ⟨1305969, by rfl⟩ : syracuseStep 3482585 = 2611939) B2611939
theorem B3261401 : Blo 1447543 3261401 := bstep (se 2 (by rfl) ⟨1223025, by rfl⟩ : syracuseStep 3261401 = 2446051) B2446051
theorem B2171915 : Blo 1447543 2171915 := bstep (se 1 (by rfl) ⟨1628936, by rfl⟩ : syracuseStep 2171915 = 3257873) B3257873
theorem B2171927 : Blo 1447543 2171927 := bstep (se 1 (by rfl) ⟨1628945, by rfl⟩ : syracuseStep 2171927 = 3257891) B3257891
theorem B8815661 : Blo 1447543 8815661 := bstep (se 3 (by rfl) ⟨1652936, by rfl⟩ : syracuseStep 8815661 = 3305873) B3305873
theorem B7332929 : Blo 1447543 7332929 := bstep (se 2 (by rfl) ⟨2749848, by rfl⟩ : syracuseStep 7332929 = 5499697) B5499697
theorem B4023371 : Blo 1447543 4023371 := bstep (se 1 (by rfl) ⟨3017528, by rfl⟩ : syracuseStep 4023371 = 6035057) B6035057
theorem B2171993 : Blo 1447543 2171993 := bstep (se 2 (by rfl) ⟨814497, by rfl⟩ : syracuseStep 2171993 = 1628995) B1628995
theorem B2172107 : Blo 1447543 2172107 := bstep (se 1 (by rfl) ⟨1629080, by rfl⟩ : syracuseStep 2172107 = 3258161) B3258161
theorem B2172119 : Blo 1447543 2172119 := bstep (se 1 (by rfl) ⟨1629089, by rfl⟩ : syracuseStep 2172119 = 3258179) B3258179
theorem B2974963 : Blo 1447543 2974963 := bstep (se 1 (by rfl) ⟨2231222, by rfl⟩ : syracuseStep 2974963 = 4462445) B4462445
theorem B2172185 : Blo 1447543 2172185 := bstep (se 2 (by rfl) ⟨814569, by rfl⟩ : syracuseStep 2172185 = 1629139) B1629139
theorem B2172299 : Blo 1447543 2172299 := bstep (se 1 (by rfl) ⟨1629224, by rfl⟩ : syracuseStep 2172299 = 3258449) B3258449
theorem B2172311 : Blo 1447543 2172311 := bstep (se 1 (by rfl) ⟨1629233, by rfl⟩ : syracuseStep 2172311 = 3258467) B3258467
theorem B2319769 : Blo 1447543 2319769 := bstep (se 2 (by rfl) ⟨869913, by rfl⟩ : syracuseStep 2319769 = 1739827) B1739827
theorem B9282995 : Blo 1447543 9282995 := bstep (se 1 (by rfl) ⟨6962246, by rfl⟩ : syracuseStep 9282995 = 13924493) B13924493
theorem B12551603 : Blo 1447543 12551603 := bstep (se 1 (by rfl) ⟨9413702, by rfl⟩ : syracuseStep 12551603 = 18827405) B18827405
theorem B2172377 : Blo 1447543 2172377 := bstep (se 2 (by rfl) ⟨814641, by rfl⟩ : syracuseStep 2172377 = 1629283) B1629283
theorem B16500185 : Blo 1447543 16500185 := bstep (se 2 (by rfl) ⟨6187569, by rfl⟩ : syracuseStep 16500185 = 12375139) B12375139
theorem B59442659 : Blo 1447543 59442659 := bstep (se 1 (by rfl) ⟨44581994, by rfl⟩ : syracuseStep 59442659 = 89163989) B89163989
theorem B618816995 : Blo 1447543 618816995 := bstep (se 1 (by rfl) ⟨464112746, by rfl⟩ : syracuseStep 618816995 = 928225493) B928225493
theorem B4892183 : Blo 1447543 4892183 := bstep (se 1 (by rfl) ⟨3669137, by rfl⟩ : syracuseStep 4892183 = 7338275) B7338275
theorem B1467947 : Blo 1447543 1467947 := bstep (se 1 (by rfl) ⟨1100960, by rfl⟩ : syracuseStep 1467947 = 2201921) B2201921
theorem B2172491 : Blo 1447543 2172491 := bstep (se 1 (by rfl) ⟨1629368, by rfl⟩ : syracuseStep 2172491 = 3258737) B3258737
theorem B2172503 : Blo 1447543 2172503 := bstep (se 1 (by rfl) ⟨1629377, by rfl⟩ : syracuseStep 2172503 = 3258755) B3258755
theorem B5498513 : Blo 1447543 5498513 := bstep (se 2 (by rfl) ⟨2061942, by rfl⟩ : syracuseStep 5498513 = 4123885) B4123885
theorem B2172569 : Blo 1447543 2172569 := bstep (se 2 (by rfl) ⟨814713, by rfl⟩ : syracuseStep 2172569 = 1629427) B1629427
theorem B2172683 : Blo 1447543 2172683 := bstep (se 1 (by rfl) ⟨1629512, by rfl⟩ : syracuseStep 2172683 = 3259025) B3259025
theorem B2172695 : Blo 1447543 2172695 := bstep (se 1 (by rfl) ⟨1629521, by rfl⟩ : syracuseStep 2172695 = 3259043) B3259043
theorem B11142947 : Blo 1447543 11142947 := bstep (se 1 (by rfl) ⟨8357210, by rfl⟩ : syracuseStep 11142947 = 16714421) B16714421
theorem B2172761 : Blo 1447543 2172761 := bstep (se 2 (by rfl) ⟨814785, by rfl⟩ : syracuseStep 2172761 = 1629571) B1629571
theorem B6186955 : Blo 1447543 6186955 := bstep (se 1 (by rfl) ⟨4640216, by rfl⟩ : syracuseStep 6186955 = 9280433) B9280433
theorem B2172875 : Blo 1447543 2172875 := bstep (se 1 (by rfl) ⟨1629656, by rfl⟩ : syracuseStep 2172875 = 3259313) B3259313
theorem B2443223 : Blo 1447543 2443223 := bstep (se 1 (by rfl) ⟨1832417, by rfl⟩ : syracuseStep 2443223 = 3664835) B3664835
theorem B2172887 : Blo 1447543 2172887 := bstep (se 1 (by rfl) ⟨1629665, by rfl⟩ : syracuseStep 2172887 = 3259331) B3259331
theorem B25077721 : Blo 1447543 25077721 := bstep (se 2 (by rfl) ⟨9404145, by rfl⟩ : syracuseStep 25077721 = 18808291) B18808291
theorem B2172953 : Blo 1447543 2172953 := bstep (se 2 (by rfl) ⟨814857, by rfl⟩ : syracuseStep 2172953 = 1629715) B1629715
theorem B21170251 : Blo 1447543 21170251 := bstep (se 1 (by rfl) ⟨15877688, by rfl⟩ : syracuseStep 21170251 = 31755377) B31755377
theorem B2443351 : Blo 1447543 2443351 := bstep (se 1 (by rfl) ⟨1832513, by rfl⟩ : syracuseStep 2443351 = 3665027) B3665027
theorem B10438757 : Blo 1447543 10438757 := bstep (se 4 (by rfl) ⟨978633, by rfl⟩ : syracuseStep 10438757 = 1957267) B1957267
theorem B2173067 : Blo 1447543 2173067 := bstep (se 1 (by rfl) ⟨1629800, by rfl⟩ : syracuseStep 2173067 = 3259601) B3259601
theorem B2173079 : Blo 1447543 2173079 := bstep (se 1 (by rfl) ⟨1629809, by rfl⟩ : syracuseStep 2173079 = 3259619) B3259619
theorem B2173145 : Blo 1447543 2173145 := bstep (se 2 (by rfl) ⟨814929, by rfl⟩ : syracuseStep 2173145 = 1629859) B1629859
theorem B6187229 : Blo 1447543 6187229 := bstep (se 3 (by rfl) ⟨1160105, by rfl⟩ : syracuseStep 6187229 = 2320211) B2320211
theorem B2935091 : Blo 1447543 2935091 := bstep (se 1 (by rfl) ⟨2201318, by rfl⟩ : syracuseStep 2935091 = 4402637) B4402637
theorem B5499211 : Blo 1447543 5499211 := bstep (se 1 (by rfl) ⟨4124408, by rfl⟩ : syracuseStep 5499211 = 8248817) B8248817
theorem B2173259 : Blo 1447543 2173259 := bstep (se 1 (by rfl) ⟨1629944, by rfl⟩ : syracuseStep 2173259 = 3259889) B3259889
theorem B2173271 : Blo 1447543 2173271 := bstep (se 1 (by rfl) ⟨1629953, by rfl⟩ : syracuseStep 2173271 = 3259907) B3259907
theorem B3664217 : Blo 1447543 3664217 := bstep (se 2 (by rfl) ⟨1374081, by rfl⟩ : syracuseStep 3664217 = 2748163) B2748163
theorem B83495285 : Blo 1447543 83495285 := bstep (se 5 (by rfl) ⟨3913841, by rfl⟩ : syracuseStep 83495285 = 7827683) B7827683
theorem B38168981 : Blo 1447543 38168981 := bstep (se 6 (by rfl) ⟨894585, by rfl⟩ : syracuseStep 38168981 = 1789171) B1789171
theorem B2173337 : Blo 1447543 2173337 := bstep (se 2 (by rfl) ⟨815001, by rfl⟩ : syracuseStep 2173337 = 1630003) B1630003
theorem B13912499 : Blo 1447543 13912499 := bstep (se 1 (by rfl) ⟨10434374, by rfl⟩ : syracuseStep 13912499 = 20868749) B20868749
theorem B2173451 : Blo 1447543 2173451 := bstep (se 1 (by rfl) ⟨1630088, by rfl⟩ : syracuseStep 2173451 = 3260177) B3260177
theorem B2173463 : Blo 1447543 2173463 := bstep (se 1 (by rfl) ⟨1630097, by rfl⟩ : syracuseStep 2173463 = 3260195) B3260195
theorem B2173529 : Blo 1447543 2173529 := bstep (se 2 (by rfl) ⟨815073, by rfl⟩ : syracuseStep 2173529 = 1630147) B1630147
theorem B5499485 : Blo 1447543 5499485 := bstep (se 3 (by rfl) ⟨1031153, by rfl⟩ : syracuseStep 5499485 = 2062307) B2062307
theorem B15657623 : Blo 1447543 15657623 := bstep (se 1 (by rfl) ⟨11743217, by rfl⟩ : syracuseStep 15657623 = 23486435) B23486435
theorem B12380849 : Blo 1447543 12380849 := bstep (se 2 (by rfl) ⟨4642818, by rfl⟩ : syracuseStep 12380849 = 9285637) B9285637
theorem B4123315 : Blo 1447543 4123315 := bstep (se 1 (by rfl) ⟨3092486, by rfl⟩ : syracuseStep 4123315 = 6184973) B6184973
theorem B2443979 : Blo 1447543 2443979 := bstep (se 1 (by rfl) ⟨1832984, by rfl⟩ : syracuseStep 2443979 = 3665969) B3665969
theorem B2173643 : Blo 1447543 2173643 := bstep (se 1 (by rfl) ⟨1630232, by rfl⟩ : syracuseStep 2173643 = 3260465) B3260465
theorem B2173655 : Blo 1447543 2173655 := bstep (se 1 (by rfl) ⟨1630241, by rfl⟩ : syracuseStep 2173655 = 3260483) B3260483
theorem B2173721 : Blo 1447543 2173721 := bstep (se 2 (by rfl) ⟨815145, by rfl⟩ : syracuseStep 2173721 = 1630291) B1630291
theorem B2444107 : Blo 1447543 2444107 := bstep (se 1 (by rfl) ⟨1833080, by rfl⟩ : syracuseStep 2444107 = 3666161) B3666161
theorem B9284483 : Blo 1447543 9284483 := bstep (se 1 (by rfl) ⟨6963362, by rfl⟩ : syracuseStep 9284483 = 13926725) B13926725
theorem B2173835 : Blo 1447543 2173835 := bstep (se 1 (by rfl) ⟨1630376, by rfl⟩ : syracuseStep 2173835 = 3260753) B3260753
theorem B4123543 : Blo 1447543 4123543 := bstep (se 1 (by rfl) ⟨3092657, by rfl⟩ : syracuseStep 4123543 = 6185315) B6185315
theorem B6695831 : Blo 1447543 6695831 := bstep (se 1 (by rfl) ⟨5021873, by rfl⟩ : syracuseStep 6695831 = 10043747) B10043747
theorem B2173847 : Blo 1447543 2173847 := bstep (se 1 (by rfl) ⟨1630385, by rfl⟩ : syracuseStep 2173847 = 3260771) B3260771
theorem B2477017 : Blo 1447543 2477017 := bstep (se 2 (by rfl) ⟨928881, by rfl⟩ : syracuseStep 2477017 = 1857763) B1857763
theorem B2444249 : Blo 1447543 2444249 := bstep (se 2 (by rfl) ⟨916593, by rfl⟩ : syracuseStep 2444249 = 1833187) B1833187
theorem B7334873 : Blo 1447543 7334873 := bstep (se 2 (by rfl) ⟨2750577, by rfl⟩ : syracuseStep 7334873 = 5501155) B5501155
theorem B2173913 : Blo 1447543 2173913 := bstep (se 2 (by rfl) ⟨815217, by rfl⟩ : syracuseStep 2173913 = 1630435) B1630435
theorem B2174027 : Blo 1447543 2174027 := bstep (se 1 (by rfl) ⟨1630520, by rfl⟩ : syracuseStep 2174027 = 3261041) B3261041
theorem B2174039 : Blo 1447543 2174039 := bstep (se 1 (by rfl) ⟨1630529, by rfl⟩ : syracuseStep 2174039 = 3261059) B3261059
theorem B2444377 : Blo 1447543 2444377 := bstep (se 2 (by rfl) ⟨916641, by rfl⟩ : syracuseStep 2444377 = 1833283) B1833283
theorem B7933079 : Blo 1447543 7933079 := bstep (se 1 (by rfl) ⟨5949809, by rfl⟩ : syracuseStep 7933079 = 11899619) B11899619
theorem B3665047 : Blo 1447543 3665047 := bstep (se 1 (by rfl) ⟨2748785, by rfl⟩ : syracuseStep 3665047 = 5497571) B5497571
theorem B2174105 : Blo 1447543 2174105 := bstep (se 2 (by rfl) ⟨815289, by rfl⟩ : syracuseStep 2174105 = 1630579) B1630579
theorem B2174219 : Blo 1447543 2174219 := bstep (se 1 (by rfl) ⟨1630664, by rfl⟩ : syracuseStep 2174219 = 3261329) B3261329
theorem B5500183 : Blo 1447543 5500183 := bstep (se 1 (by rfl) ⟨4125137, by rfl⟩ : syracuseStep 5500183 = 8250275) B8250275
theorem B2174231 : Blo 1447543 2174231 := bstep (se 1 (by rfl) ⟨1630673, by rfl⟩ : syracuseStep 2174231 = 3261347) B3261347
theorem B4885811 : Blo 1447543 4885811 := bstep (se 1 (by rfl) ⟨3664358, by rfl⟩ : syracuseStep 4885811 = 7328717) B7328717
theorem B2174297 : Blo 1447543 2174297 := bstep (se 2 (by rfl) ⟨815361, by rfl⟩ : syracuseStep 2174297 = 1630723) B1630723
theorem B13208933 : Blo 1447543 13208933 := bstep (se 4 (by rfl) ⟨1238337, by rfl⟩ : syracuseStep 13208933 = 2476675) B2476675
theorem B22310261 : Blo 1447543 22310261 := bstep (se 5 (by rfl) ⟨1045793, by rfl⟩ : syracuseStep 22310261 = 2091587) B2091587
theorem B3526067 : Blo 1447543 3526067 := bstep (se 1 (by rfl) ⟨2644550, by rfl⟩ : syracuseStep 3526067 = 5289101) B5289101
theorem B4886081 : Blo 1447543 4886081 := bstep (se 2 (by rfl) ⟨1832280, by rfl⟩ : syracuseStep 4886081 = 3664561) B3664561
theorem B3665483 : Blo 1447543 3665483 := bstep (se 1 (by rfl) ⟨2749112, by rfl⟩ : syracuseStep 3665483 = 5498225) B5498225
theorem B5222033 : Blo 1447543 5222033 := bstep (se 2 (by rfl) ⟨1958262, by rfl⟩ : syracuseStep 5222033 = 3916525) B3916525
theorem B2444951 : Blo 1447543 2444951 := bstep (se 1 (by rfl) ⟨1833713, by rfl⟩ : syracuseStep 2444951 = 3667427) B3667427
theorem B5574365 : Blo 1447543 5574365 := bstep (se 3 (by rfl) ⟨1045193, by rfl⟩ : syracuseStep 5574365 = 2090387) B2090387
theorem B2445079 : Blo 1447543 2445079 := bstep (se 1 (by rfl) ⟨1833809, by rfl⟩ : syracuseStep 2445079 = 3667619) B3667619
theorem B7942067 : Blo 1447543 7942067 := bstep (se 1 (by rfl) ⟨5956550, by rfl⟩ : syracuseStep 7942067 = 11913101) B11913101
theorem B3665857 : Blo 1447543 3665857 := bstep (se 2 (by rfl) ⟨1374696, by rfl⟩ : syracuseStep 3665857 = 2749393) B2749393
theorem B2609113 : Blo 1447543 2609113 := bstep (se 2 (by rfl) ⟨978417, by rfl⟩ : syracuseStep 2609113 = 1956835) B1956835
theorem B5500973 : Blo 1447543 5500973 := bstep (se 3 (by rfl) ⟨1031432, by rfl⟩ : syracuseStep 5500973 = 2062865) B2062865
theorem B2748467 : Blo 1447543 2748467 := bstep (se 1 (by rfl) ⟨2061350, by rfl⟩ : syracuseStep 2748467 = 4122701) B4122701
theorem B3092555 : Blo 1447543 3092555 := bstep (se 1 (by rfl) ⟨2319416, by rfl⟩ : syracuseStep 3092555 = 4638833) B4638833
theorem B2748505 : Blo 1447543 2748505 := bstep (se 2 (by rfl) ⟨1030689, by rfl⟩ : syracuseStep 2748505 = 2061379) B2061379
theorem B4886621 : Blo 1447543 4886621 := bstep (se 3 (by rfl) ⟨916241, by rfl⟩ : syracuseStep 4886621 = 1832483) B1832483
theorem B5222551 : Blo 1447543 5222551 := bstep (se 1 (by rfl) ⟨3916913, by rfl⟩ : syracuseStep 5222551 = 7833827) B7833827
theorem B2609459 : Blo 1447543 2609459 := bstep (se 1 (by rfl) ⟨1957094, by rfl⟩ : syracuseStep 2609459 = 3914189) B3914189
theorem B2445707 : Blo 1447543 2445707 := bstep (se 1 (by rfl) ⟨1834280, by rfl⟩ : syracuseStep 2445707 = 3668561) B3668561
theorem B9277847 : Blo 1447543 9277847 := bstep (se 1 (by rfl) ⟨6958385, by rfl⟩ : syracuseStep 9277847 = 13916771) B13916771
theorem B2445835 : Blo 1447543 2445835 := bstep (se 1 (by rfl) ⟨1834376, by rfl⟩ : syracuseStep 2445835 = 3668753) B3668753
theorem B3666455 : Blo 1447543 3666455 := bstep (se 1 (by rfl) ⟨2749841, by rfl⟩ : syracuseStep 3666455 = 5499683) B5499683
theorem B2748953 : Blo 1447543 2748953 := bstep (se 2 (by rfl) ⟨1030857, by rfl⟩ : syracuseStep 2748953 = 2061715) B2061715
theorem B7336493 : Blo 1447543 7336493 := bstep (se 3 (by rfl) ⟨1375592, by rfl⟩ : syracuseStep 7336493 = 2751185) B2751185
theorem B2445977 : Blo 1447543 2445977 := bstep (se 2 (by rfl) ⟨917241, by rfl⟩ : syracuseStep 2445977 = 1834483) B1834483
theorem B4125401 : Blo 1447543 4125401 := bstep (se 2 (by rfl) ⟨1547025, by rfl⟩ : syracuseStep 4125401 = 3094051) B3094051
theorem B2478809 : Blo 1447543 2478809 := bstep (se 2 (by rfl) ⟨929553, by rfl⟩ : syracuseStep 2478809 = 1859107) B1859107
theorem B2609921 : Blo 1447543 2609921 := bstep (se 2 (by rfl) ⟨978720, by rfl⟩ : syracuseStep 2609921 = 1957441) B1957441
theorem B3257099 : Blo 1447543 3257099 := bstep (se 1 (by rfl) ⟨2442824, by rfl⟩ : syracuseStep 3257099 = 4885649) B4885649
theorem B2446105 : Blo 1447543 2446105 := bstep (se 2 (by rfl) ⟨917289, by rfl⟩ : syracuseStep 2446105 = 1834579) B1834579
theorem B3093299 : Blo 1447543 3093299 := bstep (se 1 (by rfl) ⟨2319974, by rfl⟩ : syracuseStep 3093299 = 4639949) B4639949
theorem B3257153 : Blo 1447543 3257153 := bstep (se 2 (by rfl) ⟨1221432, by rfl⟩ : syracuseStep 3257153 = 2442865) B2442865
theorem B3715915 : Blo 1447543 3715915 := bstep (se 1 (by rfl) ⟨2786936, by rfl⟩ : syracuseStep 3715915 = 5573873) B5573873
theorem B13218821 : Blo 1447543 13218821 := bstep (se 4 (by rfl) ⟨1239264, by rfl⟩ : syracuseStep 13218821 = 2478529) B2478529
theorem B3257369 : Blo 1447543 3257369 := bstep (se 2 (by rfl) ⟨1221513, by rfl⟩ : syracuseStep 3257369 = 2443027) B2443027
theorem B4641857 : Blo 1447543 4641857 := bstep (se 2 (by rfl) ⟨1740696, by rfl⟩ : syracuseStep 4641857 = 3481393) B3481393
theorem B3257459 : Blo 1447543 3257459 := bstep (se 1 (by rfl) ⟨2443094, by rfl⟩ : syracuseStep 3257459 = 4886189) B4886189
theorem B2937971 : Blo 1447543 2937971 := bstep (se 1 (by rfl) ⟨2203478, by rfl⟩ : syracuseStep 2937971 = 4406957) B4406957
theorem B3257495 : Blo 1447543 3257495 := bstep (se 1 (by rfl) ⟨2443121, by rfl⟩ : syracuseStep 3257495 = 4886243) B4886243
theorem B4887755 : Blo 1447543 4887755 := bstep (se 1 (by rfl) ⟨3665816, by rfl⟩ : syracuseStep 4887755 = 7331633) B7331633
theorem B1651915 : Blo 1447543 1651915 := bstep (se 1 (by rfl) ⟨1238936, by rfl⟩ : syracuseStep 1651915 = 2477873) B2477873
theorem B2749697 : Blo 1447543 2749697 := bstep (se 2 (by rfl) ⟨1031136, by rfl⟩ : syracuseStep 2749697 = 2062273) B2062273
theorem B7329041 : Blo 1447543 7329041 := bstep (se 2 (by rfl) ⟨2748390, by rfl⟩ : syracuseStep 7329041 = 5496781) B5496781
theorem B1832215 : Blo 1447543 1832215 := bstep (se 1 (by rfl) ⟨1374161, by rfl⟩ : syracuseStep 1832215 = 2748323) B2748323
theorem B2610497 : Blo 1447543 2610497 := bstep (se 2 (by rfl) ⟨978936, by rfl⟩ : syracuseStep 2610497 = 1957873) B1957873
theorem B3667265 : Blo 1447543 3667265 := bstep (se 2 (by rfl) ⟨1375224, by rfl⟩ : syracuseStep 3667265 = 2750449) B2750449
theorem B3257675 : Blo 1447543 3257675 := bstep (se 1 (by rfl) ⟨2443256, by rfl⟩ : syracuseStep 3257675 = 4886513) B4886513
theorem B3257729 : Blo 1447543 3257729 := bstep (se 2 (by rfl) ⟨1221648, by rfl⟩ : syracuseStep 3257729 = 2443297) B2443297
theorem B7329203 : Blo 1447543 7329203 := bstep (se 1 (by rfl) ⟨5496902, by rfl⟩ : syracuseStep 7329203 = 10993805) B10993805
theorem B3478963 : Blo 1447543 3478963 := bstep (se 1 (by rfl) ⟨2609222, by rfl⟩ : syracuseStep 3478963 = 5218445) B5218445
theorem B5502401 : Blo 1447543 5502401 := bstep (se 2 (by rfl) ⟨2063400, by rfl⟩ : syracuseStep 5502401 = 4126801) B4126801
theorem B4888025 : Blo 1447543 4888025 := bstep (se 2 (by rfl) ⟨1833009, by rfl⟩ : syracuseStep 4888025 = 3666019) B3666019
theorem B2749963 : Blo 1447543 2749963 := bstep (se 1 (by rfl) ⟨2062472, by rfl⟩ : syracuseStep 2749963 = 4124945) B4124945
theorem B4126231 : Blo 1447543 4126231 := bstep (se 1 (by rfl) ⟨3094673, by rfl⟩ : syracuseStep 4126231 = 6189347) B6189347
theorem B3257945 : Blo 1447543 3257945 := bstep (se 2 (by rfl) ⟨1221729, by rfl⟩ : syracuseStep 3257945 = 2443459) B2443459
theorem B10442333 : Blo 1447543 10442333 := bstep (se 3 (by rfl) ⟨1957937, by rfl⟩ : syracuseStep 10442333 = 3915875) B3915875
theorem B1447543 : Blo 1447543 1447543 := bstep (se 1 (by rfl) ⟨1085657, by rfl⟩ : syracuseStep 1447543 = 2171315) B2171315
theorem B1447563 : Blo 1447543 1447563 := bstep (se 1 (by rfl) ⟨1085672, by rfl⟩ : syracuseStep 1447563 = 2171345) B2171345
theorem B1447575 : Blo 1447543 1447575 := bstep (se 1 (by rfl) ⟨1085681, by rfl⟩ : syracuseStep 1447575 = 2171363) B2171363
theorem B3348119 : Blo 1447543 3348119 := bstep (se 1 (by rfl) ⟨2511089, by rfl⟩ : syracuseStep 3348119 = 5022179) B5022179
theorem B1447595 : Blo 1447543 1447595 := bstep (se 1 (by rfl) ⟨1085696, by rfl⟩ : syracuseStep 1447595 = 2171393) B2171393
theorem B3258035 : Blo 1447543 3258035 := bstep (se 1 (by rfl) ⟨2443526, by rfl⟩ : syracuseStep 3258035 = 4887053) B4887053
theorem B3094195 : Blo 1447543 3094195 := bstep (se 1 (by rfl) ⟨2320646, by rfl⟩ : syracuseStep 3094195 = 4641293) B4641293
theorem B1447607 : Blo 1447543 1447607 := bstep (se 1 (by rfl) ⟨1085705, by rfl⟩ : syracuseStep 1447607 = 2171411) B2171411
theorem B1447627 : Blo 1447543 1447627 := bstep (se 1 (by rfl) ⟨1085720, by rfl⟩ : syracuseStep 1447627 = 2171441) B2171441
theorem B1447639 : Blo 1447543 1447639 := bstep (se 1 (by rfl) ⟨1085729, by rfl⟩ : syracuseStep 1447639 = 2171459) B2171459
theorem B3258071 : Blo 1447543 3258071 := bstep (se 1 (by rfl) ⟨2443553, by rfl⟩ : syracuseStep 3258071 = 4887107) B4887107
theorem B1447659 : Blo 1447543 1447659 := bstep (se 1 (by rfl) ⟨1085744, by rfl⟩ : syracuseStep 1447659 = 2171489) B2171489
theorem B1447671 : Blo 1447543 1447671 := bstep (se 1 (by rfl) ⟨1085753, by rfl⟩ : syracuseStep 1447671 = 2171507) B2171507
theorem B1447691 : Blo 1447543 1447691 := bstep (se 1 (by rfl) ⟨1085768, by rfl⟩ : syracuseStep 1447691 = 2171537) B2171537
theorem B1447703 : Blo 1447543 1447703 := bstep (se 1 (by rfl) ⟨1085777, by rfl⟩ : syracuseStep 1447703 = 2171555) B2171555
theorem B1652503 : Blo 1447543 1652503 := bstep (se 1 (by rfl) ⟨1239377, by rfl⟩ : syracuseStep 1652503 = 2478755) B2478755
theorem B1447723 : Blo 1447543 1447723 := bstep (se 1 (by rfl) ⟨1085792, by rfl⟩ : syracuseStep 1447723 = 2171585) B2171585
theorem B6960941 : Blo 1447543 6960941 := bstep (se 3 (by rfl) ⟨1305176, by rfl⟩ : syracuseStep 6960941 = 2610353) B2610353
theorem B1447735 : Blo 1447543 1447735 := bstep (se 1 (by rfl) ⟨1085801, by rfl⟩ : syracuseStep 1447735 = 2171603) B2171603
theorem B1447755 : Blo 1447543 1447755 := bstep (se 1 (by rfl) ⟨1085816, by rfl⟩ : syracuseStep 1447755 = 2171633) B2171633
theorem B1447767 : Blo 1447543 1447767 := bstep (se 1 (by rfl) ⟨1085825, by rfl⟩ : syracuseStep 1447767 = 2171651) B2171651
theorem B3667801 : Blo 1447543 3667801 := bstep (se 2 (by rfl) ⟨1375425, by rfl⟩ : syracuseStep 3667801 = 2750851) B2750851
theorem B1447787 : Blo 1447543 1447787 := bstep (se 1 (by rfl) ⟨1085840, by rfl⟩ : syracuseStep 1447787 = 2171681) B2171681
theorem B1447799 : Blo 1447543 1447799 := bstep (se 1 (by rfl) ⟨1085849, by rfl⟩ : syracuseStep 1447799 = 2171699) B2171699
theorem B1447819 : Blo 1447543 1447819 := bstep (se 1 (by rfl) ⟨1085864, by rfl⟩ : syracuseStep 1447819 = 2171729) B2171729
theorem B3258251 : Blo 1447543 3258251 := bstep (se 1 (by rfl) ⟨2443688, by rfl⟩ : syracuseStep 3258251 = 4887377) B4887377
theorem B1447831 : Blo 1447543 1447831 := bstep (se 1 (by rfl) ⟨1085873, by rfl⟩ : syracuseStep 1447831 = 2171747) B2171747
theorem B1447851 : Blo 1447543 1447851 := bstep (se 1 (by rfl) ⟨1085888, by rfl⟩ : syracuseStep 1447851 = 2171777) B2171777
theorem B1447863 : Blo 1447543 1447863 := bstep (se 1 (by rfl) ⟨1085897, by rfl⟩ : syracuseStep 1447863 = 2171795) B2171795
theorem B3258305 : Blo 1447543 3258305 := bstep (se 2 (by rfl) ⟨1221864, by rfl⟩ : syracuseStep 3258305 = 2443729) B2443729
theorem B1447883 : Blo 1447543 1447883 := bstep (se 1 (by rfl) ⟨1085912, by rfl⟩ : syracuseStep 1447883 = 2171825) B2171825
theorem B2750411 : Blo 1447543 2750411 := bstep (se 1 (by rfl) ⟨2062808, by rfl⟩ : syracuseStep 2750411 = 4125617) B4125617
theorem B1447895 : Blo 1447543 1447895 := bstep (se 1 (by rfl) ⟨1085921, by rfl⟩ : syracuseStep 1447895 = 2171843) B2171843
theorem B1447915 : Blo 1447543 1447915 := bstep (se 1 (by rfl) ⟨1085936, by rfl⟩ : syracuseStep 1447915 = 2171873) B2171873
theorem B1447927 : Blo 1447543 1447927 := bstep (se 1 (by rfl) ⟨1085945, by rfl⟩ : syracuseStep 1447927 = 2171891) B2171891
theorem B1447947 : Blo 1447543 1447947 := bstep (se 1 (by rfl) ⟨1085960, by rfl⟩ : syracuseStep 1447947 = 2171921) B2171921
theorem B1447959 : Blo 1447543 1447959 := bstep (se 1 (by rfl) ⟨1085969, by rfl⟩ : syracuseStep 1447959 = 2171939) B2171939
theorem B1447979 : Blo 1447543 1447979 := bstep (se 1 (by rfl) ⟨1085984, by rfl⟩ : syracuseStep 1447979 = 2171969) B2171969
theorem B1447991 : Blo 1447543 1447991 := bstep (se 1 (by rfl) ⟨1085993, by rfl⟩ : syracuseStep 1447991 = 2171987) B2171987
theorem B1448011 : Blo 1447543 1448011 := bstep (se 1 (by rfl) ⟨1086008, by rfl⟩ : syracuseStep 1448011 = 2172017) B2172017
theorem B1448023 : Blo 1447543 1448023 := bstep (se 1 (by rfl) ⟨1086017, by rfl⟩ : syracuseStep 1448023 = 2172035) B2172035
theorem B1448043 : Blo 1447543 1448043 := bstep (se 1 (by rfl) ⟨1086032, by rfl⟩ : syracuseStep 1448043 = 2172065) B2172065
theorem B1448055 : Blo 1447543 1448055 := bstep (se 1 (by rfl) ⟨1086041, by rfl⟩ : syracuseStep 1448055 = 2172083) B2172083
theorem B2750593 : Blo 1447543 2750593 := bstep (se 2 (by rfl) ⟨1031472, by rfl⟩ : syracuseStep 2750593 = 2062945) B2062945
theorem B1448075 : Blo 1447543 1448075 := bstep (se 1 (by rfl) ⟨1086056, by rfl⟩ : syracuseStep 1448075 = 2172113) B2172113
theorem B1448087 : Blo 1447543 1448087 := bstep (se 1 (by rfl) ⟨1086065, by rfl⟩ : syracuseStep 1448087 = 2172131) B2172131
theorem B4888727 : Blo 1447543 4888727 := bstep (se 1 (by rfl) ⟨3666545, by rfl⟩ : syracuseStep 4888727 = 7333091) B7333091
theorem B3258521 : Blo 1447543 3258521 := bstep (se 2 (by rfl) ⟨1221945, by rfl⟩ : syracuseStep 3258521 = 2443891) B2443891
theorem B1448107 : Blo 1447543 1448107 := bstep (se 1 (by rfl) ⟨1086080, by rfl⟩ : syracuseStep 1448107 = 2172161) B2172161
theorem B1448119 : Blo 1447543 1448119 := bstep (se 1 (by rfl) ⟨1086089, by rfl⟩ : syracuseStep 1448119 = 2172179) B2172179
theorem B1448139 : Blo 1447543 1448139 := bstep (se 1 (by rfl) ⟨1086104, by rfl⟩ : syracuseStep 1448139 = 2172209) B2172209
theorem B1448151 : Blo 1447543 1448151 := bstep (se 1 (by rfl) ⟨1086113, by rfl⟩ : syracuseStep 1448151 = 2172227) B2172227
theorem B1448171 : Blo 1447543 1448171 := bstep (se 1 (by rfl) ⟨1086128, by rfl⟩ : syracuseStep 1448171 = 2172257) B2172257
theorem B3258611 : Blo 1447543 3258611 := bstep (se 1 (by rfl) ⟨2443958, by rfl⟩ : syracuseStep 3258611 = 4887917) B4887917
theorem B1448183 : Blo 1447543 1448183 := bstep (se 1 (by rfl) ⟨1086137, by rfl⟩ : syracuseStep 1448183 = 2172275) B2172275
theorem B1448203 : Blo 1447543 1448203 := bstep (se 1 (by rfl) ⟨1086152, by rfl⟩ : syracuseStep 1448203 = 2172305) B2172305
theorem B2201879 : Blo 1447543 2201879 := bstep (se 1 (by rfl) ⟨1651409, by rfl⟩ : syracuseStep 2201879 = 3302819) B3302819
theorem B1448215 : Blo 1447543 1448215 := bstep (se 1 (by rfl) ⟨1086161, by rfl⟩ : syracuseStep 1448215 = 2172323) B2172323
theorem B3258647 : Blo 1447543 3258647 := bstep (se 1 (by rfl) ⟨2443985, by rfl⟩ : syracuseStep 3258647 = 4887971) B4887971
theorem B1448235 : Blo 1447543 1448235 := bstep (se 1 (by rfl) ⟨1086176, by rfl⟩ : syracuseStep 1448235 = 2172353) B2172353
theorem B1448247 : Blo 1447543 1448247 := bstep (se 1 (by rfl) ⟨1086185, by rfl⟩ : syracuseStep 1448247 = 2172371) B2172371
theorem B1628491 : Blo 1447543 1628491 := bstep (se 1 (by rfl) ⟨1221368, by rfl⟩ : syracuseStep 1628491 = 2442737) B2442737
theorem B1448267 : Blo 1447543 1448267 := bstep (se 1 (by rfl) ⟨1086200, by rfl⟩ : syracuseStep 1448267 = 2172401) B2172401
theorem B4127051 : Blo 1447543 4127051 := bstep (se 1 (by rfl) ⟨3095288, by rfl⟩ : syracuseStep 4127051 = 6190577) B6190577
theorem B1448279 : Blo 1447543 1448279 := bstep (se 1 (by rfl) ⟨1086209, by rfl⟩ : syracuseStep 1448279 = 2172419) B2172419
theorem B1448299 : Blo 1447543 1448299 := bstep (se 1 (by rfl) ⟨1086224, by rfl⟩ : syracuseStep 1448299 = 2172449) B2172449
theorem B1448311 : Blo 1447543 1448311 := bstep (se 1 (by rfl) ⟨1086233, by rfl⟩ : syracuseStep 1448311 = 2172467) B2172467
theorem B1448331 : Blo 1447543 1448331 := bstep (se 1 (by rfl) ⟨1086248, by rfl⟩ : syracuseStep 1448331 = 2172497) B2172497
theorem B1448343 : Blo 1447543 1448343 := bstep (se 1 (by rfl) ⟨1086257, by rfl⟩ : syracuseStep 1448343 = 2172515) B2172515
theorem B1448363 : Blo 1447543 1448363 := bstep (se 1 (by rfl) ⟨1086272, by rfl⟩ : syracuseStep 1448363 = 2172545) B2172545
theorem B1448375 : Blo 1447543 1448375 := bstep (se 1 (by rfl) ⟨1086281, by rfl⟩ : syracuseStep 1448375 = 2172563) B2172563
theorem B1628599 : Blo 1447543 1628599 := bstep (se 1 (by rfl) ⟨1221449, by rfl⟩ : syracuseStep 1628599 = 2442899) B2442899
theorem B3258827 : Blo 1447543 3258827 := bstep (se 1 (by rfl) ⟨2444120, by rfl⟩ : syracuseStep 3258827 = 4888241) B4888241
theorem B1448395 : Blo 1447543 1448395 := bstep (se 1 (by rfl) ⟨1086296, by rfl⟩ : syracuseStep 1448395 = 2172593) B2172593
theorem B1448407 : Blo 1447543 1448407 := bstep (se 1 (by rfl) ⟨1086305, by rfl⟩ : syracuseStep 1448407 = 2172611) B2172611
theorem B2750935 : Blo 1447543 2750935 := bstep (se 1 (by rfl) ⟨2063201, by rfl⟩ : syracuseStep 2750935 = 4126403) B4126403
theorem B1448427 : Blo 1447543 1448427 := bstep (se 1 (by rfl) ⟨1086320, by rfl⟩ : syracuseStep 1448427 = 2172641) B2172641
theorem B1448439 : Blo 1447543 1448439 := bstep (se 1 (by rfl) ⟨1086329, by rfl⟩ : syracuseStep 1448439 = 2172659) B2172659
theorem B3258881 : Blo 1447543 3258881 := bstep (se 2 (by rfl) ⟨1222080, by rfl⟩ : syracuseStep 3258881 = 2444161) B2444161
theorem B1448459 : Blo 1447543 1448459 := bstep (se 1 (by rfl) ⟨1086344, by rfl⟩ : syracuseStep 1448459 = 2172689) B2172689
theorem B285792785 : Blo 1447543 285792785 := bstep (se 2 (by rfl) ⟨107172294, by rfl⟩ : syracuseStep 285792785 = 214344589) B214344589
theorem B1448471 : Blo 1447543 1448471 := bstep (se 1 (by rfl) ⟨1086353, by rfl⟩ : syracuseStep 1448471 = 2172707) B2172707
theorem B17627665 : Blo 1447543 17627665 := bstep (se 2 (by rfl) ⟨6610374, by rfl⟩ : syracuseStep 17627665 = 13220749) B13220749
theorem B1448491 : Blo 1447543 1448491 := bstep (se 1 (by rfl) ⟨1086368, by rfl⟩ : syracuseStep 1448491 = 2172737) B2172737
theorem B6183469 : Blo 1447543 6183469 := bstep (se 3 (by rfl) ⟨1159400, by rfl⟩ : syracuseStep 6183469 = 2318801) B2318801
theorem B1448503 : Blo 1447543 1448503 := bstep (se 1 (by rfl) ⟨1086377, by rfl⟩ : syracuseStep 1448503 = 2172755) B2172755
theorem B1448523 : Blo 1447543 1448523 := bstep (se 1 (by rfl) ⟨1086392, by rfl⟩ : syracuseStep 1448523 = 2172785) B2172785
theorem B7060043 : Blo 1447543 7060043 := bstep (se 1 (by rfl) ⟨5295032, by rfl⟩ : syracuseStep 7060043 = 10590065) B10590065
theorem B1448535 : Blo 1447543 1448535 := bstep (se 1 (by rfl) ⟨1086401, by rfl⟩ : syracuseStep 1448535 = 2172803) B2172803
theorem B1628779 : Blo 1447543 1628779 := bstep (se 1 (by rfl) ⟨1221584, by rfl⟩ : syracuseStep 1628779 = 2443169) B2443169
theorem B1448555 : Blo 1447543 1448555 := bstep (se 1 (by rfl) ⟨1086416, by rfl⟩ : syracuseStep 1448555 = 2172833) B2172833
theorem B1448567 : Blo 1447543 1448567 := bstep (se 1 (by rfl) ⟨1086425, by rfl⟩ : syracuseStep 1448567 = 2172851) B2172851
theorem B1448587 : Blo 1447543 1448587 := bstep (se 1 (by rfl) ⟨1086440, by rfl⟩ : syracuseStep 1448587 = 2172881) B2172881
theorem B1448599 : Blo 1447543 1448599 := bstep (se 1 (by rfl) ⟨1086449, by rfl⟩ : syracuseStep 1448599 = 2172899) B2172899
theorem B1448619 : Blo 1447543 1448619 := bstep (se 1 (by rfl) ⟨1086464, by rfl⟩ : syracuseStep 1448619 = 2172929) B2172929
theorem B4889267 : Blo 1447543 4889267 := bstep (se 1 (by rfl) ⟨3666950, by rfl⟩ : syracuseStep 4889267 = 7333901) B7333901
theorem B1448631 : Blo 1447543 1448631 := bstep (se 1 (by rfl) ⟨1086473, by rfl⟩ : syracuseStep 1448631 = 2172947) B2172947
theorem B2751155 : Blo 1447543 2751155 := bstep (se 1 (by rfl) ⟨2063366, by rfl⟩ : syracuseStep 2751155 = 4126733) B4126733
theorem B1448651 : Blo 1447543 1448651 := bstep (se 1 (by rfl) ⟨1086488, by rfl⟩ : syracuseStep 1448651 = 2172977) B2172977
theorem B1628887 : Blo 1447543 1628887 := bstep (se 1 (by rfl) ⟨1221665, by rfl⟩ : syracuseStep 1628887 = 2443331) B2443331
theorem B1448663 : Blo 1447543 1448663 := bstep (se 1 (by rfl) ⟨1086497, by rfl⟩ : syracuseStep 1448663 = 2172995) B2172995
theorem B6183641 : Blo 1447543 6183641 := bstep (se 2 (by rfl) ⟨2318865, by rfl⟩ : syracuseStep 6183641 = 4637731) B4637731
theorem B3259097 : Blo 1447543 3259097 := bstep (se 2 (by rfl) ⟨1222161, by rfl⟩ : syracuseStep 3259097 = 2444323) B2444323
theorem B2063065 : Blo 1447543 2063065 := bstep (se 2 (by rfl) ⟨773649, by rfl⟩ : syracuseStep 2063065 = 1547299) B1547299
theorem B3095255 : Blo 1447543 3095255 := bstep (se 1 (by rfl) ⟨2321441, by rfl⟩ : syracuseStep 3095255 = 4642883) B4642883
theorem B1448683 : Blo 1447543 1448683 := bstep (se 1 (by rfl) ⟨1086512, by rfl⟩ : syracuseStep 1448683 = 2173025) B2173025
theorem B1448695 : Blo 1447543 1448695 := bstep (se 1 (by rfl) ⟨1086521, by rfl⟩ : syracuseStep 1448695 = 2173043) B2173043
theorem B1448715 : Blo 1447543 1448715 := bstep (se 1 (by rfl) ⟨1086536, by rfl⟩ : syracuseStep 1448715 = 2173073) B2173073
theorem B1448727 : Blo 1447543 1448727 := bstep (se 1 (by rfl) ⟨1086545, by rfl⟩ : syracuseStep 1448727 = 2173091) B2173091
theorem B1448747 : Blo 1447543 1448747 := bstep (se 1 (by rfl) ⟨1086560, by rfl⟩ : syracuseStep 1448747 = 2173121) B2173121
theorem B3259187 : Blo 1447543 3259187 := bstep (se 1 (by rfl) ⟨2444390, by rfl⟩ : syracuseStep 3259187 = 4888781) B4888781
theorem B1448759 : Blo 1447543 1448759 := bstep (se 1 (by rfl) ⟨1086569, by rfl⟩ : syracuseStep 1448759 = 2173139) B2173139
theorem B9280331 : Blo 1447543 9280331 := bstep (se 1 (by rfl) ⟨6960248, by rfl⟩ : syracuseStep 9280331 = 13920497) B13920497
theorem B1448779 : Blo 1447543 1448779 := bstep (se 1 (by rfl) ⟨1086584, by rfl⟩ : syracuseStep 1448779 = 2173169) B2173169
theorem B3259223 : Blo 1447543 3259223 := bstep (se 1 (by rfl) ⟨2444417, by rfl⟩ : syracuseStep 3259223 = 4888835) B4888835
theorem B1448791 : Blo 1447543 1448791 := bstep (se 1 (by rfl) ⟨1086593, by rfl⟩ : syracuseStep 1448791 = 2173187) B2173187
theorem B1448811 : Blo 1447543 1448811 := bstep (se 1 (by rfl) ⟨1086608, by rfl⟩ : syracuseStep 1448811 = 2173217) B2173217
theorem B2612083 : Blo 1447543 2612083 := bstep (se 1 (by rfl) ⟨1959062, by rfl⟩ : syracuseStep 2612083 = 3918125) B3918125
theorem B1448823 : Blo 1447543 1448823 := bstep (se 1 (by rfl) ⟨1086617, by rfl⟩ : syracuseStep 1448823 = 2173235) B2173235
theorem B3095425 : Blo 1447543 3095425 := bstep (se 2 (by rfl) ⟨1160784, by rfl⟩ : syracuseStep 3095425 = 2321569) B2321569
theorem B1629067 : Blo 1447543 1629067 := bstep (se 1 (by rfl) ⟨1221800, by rfl⟩ : syracuseStep 1629067 = 2443601) B2443601
theorem B1448843 : Blo 1447543 1448843 := bstep (se 1 (by rfl) ⟨1086632, by rfl⟩ : syracuseStep 1448843 = 2173265) B2173265
theorem B1448855 : Blo 1447543 1448855 := bstep (se 1 (by rfl) ⟨1086641, by rfl⟩ : syracuseStep 1448855 = 2173283) B2173283
theorem B2751383 : Blo 1447543 2751383 := bstep (se 1 (by rfl) ⟨2063537, by rfl⟩ : syracuseStep 2751383 = 4127075) B4127075
theorem B1448875 : Blo 1447543 1448875 := bstep (se 1 (by rfl) ⟨1086656, by rfl⟩ : syracuseStep 1448875 = 2173313) B2173313
theorem B7830451 : Blo 1447543 7830451 := bstep (se 1 (by rfl) ⟨5872838, by rfl⟩ : syracuseStep 7830451 = 11745677) B11745677
theorem B3668915 : Blo 1447543 3668915 := bstep (se 1 (by rfl) ⟨2751686, by rfl⟩ : syracuseStep 3668915 = 5503373) B5503373
theorem B1448887 : Blo 1447543 1448887 := bstep (se 1 (by rfl) ⟨1086665, by rfl⟩ : syracuseStep 1448887 = 2173331) B2173331
theorem B4889537 : Blo 1447543 4889537 := bstep (se 2 (by rfl) ⟨1833576, by rfl⟩ : syracuseStep 4889537 = 3667153) B3667153
theorem B2202571 : Blo 1447543 2202571 := bstep (se 1 (by rfl) ⟨1651928, by rfl⟩ : syracuseStep 2202571 = 3303857) B3303857
theorem B1448907 : Blo 1447543 1448907 := bstep (se 1 (by rfl) ⟨1086680, by rfl⟩ : syracuseStep 1448907 = 2173361) B2173361
theorem B1833931 : Blo 1447543 1833931 := bstep (se 1 (by rfl) ⟨1375448, by rfl⟩ : syracuseStep 1833931 = 2750897) B2750897
theorem B1448919 : Blo 1447543 1448919 := bstep (se 1 (by rfl) ⟨1086689, by rfl⟩ : syracuseStep 1448919 = 2173379) B2173379
theorem B1448939 : Blo 1447543 1448939 := bstep (se 1 (by rfl) ⟨1086704, by rfl⟩ : syracuseStep 1448939 = 2173409) B2173409
theorem B1629175 : Blo 1447543 1629175 := bstep (se 1 (by rfl) ⟨1221881, by rfl⟩ : syracuseStep 1629175 = 2443763) B2443763
theorem B1448951 : Blo 1447543 1448951 := bstep (se 1 (by rfl) ⟨1086713, by rfl⟩ : syracuseStep 1448951 = 2173427) B2173427
theorem B3259403 : Blo 1447543 3259403 := bstep (se 1 (by rfl) ⟨2444552, by rfl⟩ : syracuseStep 3259403 = 4889105) B4889105
theorem B1448971 : Blo 1447543 1448971 := bstep (se 1 (by rfl) ⟨1086728, by rfl⟩ : syracuseStep 1448971 = 2173457) B2173457
theorem B1448983 : Blo 1447543 1448983 := bstep (se 1 (by rfl) ⟨1086737, by rfl⟩ : syracuseStep 1448983 = 2173475) B2173475
theorem B12377123 : Blo 1447543 12377123 := bstep (se 1 (by rfl) ⟨9282842, by rfl⟩ : syracuseStep 12377123 = 18565685) B18565685
theorem B1449003 : Blo 1447543 1449003 := bstep (se 1 (by rfl) ⟨1086752, by rfl⟩ : syracuseStep 1449003 = 2173505) B2173505
theorem B1449015 : Blo 1447543 1449015 := bstep (se 1 (by rfl) ⟨1086761, by rfl⟩ : syracuseStep 1449015 = 2173523) B2173523
theorem B3259457 : Blo 1447543 3259457 := bstep (se 2 (by rfl) ⟨1222296, by rfl⟩ : syracuseStep 3259457 = 2444593) B2444593
theorem B1449035 : Blo 1447543 1449035 := bstep (se 1 (by rfl) ⟨1086776, by rfl⟩ : syracuseStep 1449035 = 2173553) B2173553
theorem B6609995 : Blo 1447543 6609995 := bstep (se 1 (by rfl) ⟨4957496, by rfl⟩ : syracuseStep 6609995 = 9914993) B9914993
theorem B1449047 : Blo 1447543 1449047 := bstep (se 1 (by rfl) ⟨1086785, by rfl⟩ : syracuseStep 1449047 = 2173571) B2173571
theorem B1547371 : Blo 1447543 1547371 := bstep (se 1 (by rfl) ⟨1160528, by rfl⟩ : syracuseStep 1547371 = 2321057) B2321057
theorem B1449067 : Blo 1447543 1449067 := bstep (se 1 (by rfl) ⟨1086800, by rfl⟩ : syracuseStep 1449067 = 2173601) B2173601
theorem B1449079 : Blo 1447543 1449079 := bstep (se 1 (by rfl) ⟨1086809, by rfl⟩ : syracuseStep 1449079 = 2173619) B2173619
theorem B1449099 : Blo 1447543 1449099 := bstep (se 1 (by rfl) ⟨1086824, by rfl⟩ : syracuseStep 1449099 = 2173649) B2173649
theorem B21175447 : Blo 1447543 21175447 := bstep (se 1 (by rfl) ⟨15881585, by rfl⟩ : syracuseStep 21175447 = 31763171) B31763171
theorem B1449111 : Blo 1447543 1449111 := bstep (se 1 (by rfl) ⟨1086833, by rfl⟩ : syracuseStep 1449111 = 2173667) B2173667
theorem B2751641 : Blo 1447543 2751641 := bstep (se 2 (by rfl) ⟨1031865, by rfl⟩ : syracuseStep 2751641 = 2063731) B2063731
theorem B1629355 : Blo 1447543 1629355 := bstep (se 1 (by rfl) ⟨1222016, by rfl⟩ : syracuseStep 1629355 = 2444033) B2444033
theorem B1449131 : Blo 1447543 1449131 := bstep (se 1 (by rfl) ⟨1086848, by rfl⟩ : syracuseStep 1449131 = 2173697) B2173697
theorem B8248499 : Blo 1447543 8248499 := bstep (se 1 (by rfl) ⟨6186374, by rfl⟩ : syracuseStep 8248499 = 12372749) B12372749
theorem B1449143 : Blo 1447543 1449143 := bstep (se 1 (by rfl) ⟨1086857, by rfl⟩ : syracuseStep 1449143 = 2173715) B2173715
theorem B1449163 : Blo 1447543 1449163 := bstep (se 1 (by rfl) ⟨1086872, by rfl⟩ : syracuseStep 1449163 = 2173745) B2173745
theorem B1449175 : Blo 1447543 1449175 := bstep (se 1 (by rfl) ⟨1086881, by rfl⟩ : syracuseStep 1449175 = 2173763) B2173763
theorem B3095767 : Blo 1447543 3095767 := bstep (se 1 (by rfl) ⟨2321825, by rfl⟩ : syracuseStep 3095767 = 4643651) B4643651
theorem B1449195 : Blo 1447543 1449195 := bstep (se 1 (by rfl) ⟨1086896, by rfl⟩ : syracuseStep 1449195 = 2173793) B2173793
theorem B1449207 : Blo 1447543 1449207 := bstep (se 1 (by rfl) ⟨1086905, by rfl⟩ : syracuseStep 1449207 = 2173811) B2173811
theorem B1449227 : Blo 1447543 1449227 := bstep (se 1 (by rfl) ⟨1086920, by rfl⟩ : syracuseStep 1449227 = 2173841) B2173841
theorem B1629463 : Blo 1447543 1629463 := bstep (se 1 (by rfl) ⟨1222097, by rfl⟩ : syracuseStep 1629463 = 2444195) B2444195
theorem B3259673 : Blo 1447543 3259673 := bstep (se 2 (by rfl) ⟨1222377, by rfl⟩ : syracuseStep 3259673 = 2444755) B2444755
theorem B1449239 : Blo 1447543 1449239 := bstep (se 1 (by rfl) ⟨1086929, by rfl⟩ : syracuseStep 1449239 = 2173859) B2173859
theorem B1449259 : Blo 1447543 1449259 := bstep (se 1 (by rfl) ⟨1086944, by rfl⟩ : syracuseStep 1449259 = 2173889) B2173889
theorem B1449271 : Blo 1447543 1449271 := bstep (se 1 (by rfl) ⟨1086953, by rfl⟩ : syracuseStep 1449271 = 2173907) B2173907
theorem B7331147 : Blo 1447543 7331147 := bstep (se 1 (by rfl) ⟨5498360, by rfl⟩ : syracuseStep 7331147 = 10996721) B10996721
theorem B1449291 : Blo 1447543 1449291 := bstep (se 1 (by rfl) ⟨1086968, by rfl⟩ : syracuseStep 1449291 = 2173937) B2173937
theorem B1449303 : Blo 1447543 1449303 := bstep (se 1 (by rfl) ⟨1086977, by rfl⟩ : syracuseStep 1449303 = 2173955) B2173955
theorem B1449323 : Blo 1447543 1449323 := bstep (se 1 (by rfl) ⟨1086992, by rfl⟩ : syracuseStep 1449323 = 2173985) B2173985
theorem B3259763 : Blo 1447543 3259763 := bstep (se 1 (by rfl) ⟨2444822, by rfl⟩ : syracuseStep 3259763 = 4889645) B4889645
theorem B1449335 : Blo 1447543 1449335 := bstep (se 1 (by rfl) ⟨1087001, by rfl⟩ : syracuseStep 1449335 = 2174003) B2174003
theorem B1449355 : Blo 1447543 1449355 := bstep (se 1 (by rfl) ⟨1087016, by rfl⟩ : syracuseStep 1449355 = 2174033) B2174033
theorem B3259799 : Blo 1447543 3259799 := bstep (se 1 (by rfl) ⟨2444849, by rfl⟩ : syracuseStep 3259799 = 4889699) B4889699
theorem B1449367 : Blo 1447543 1449367 := bstep (se 1 (by rfl) ⟨1087025, by rfl⟩ : syracuseStep 1449367 = 2174051) B2174051
theorem B1449387 : Blo 1447543 1449387 := bstep (se 1 (by rfl) ⟨1087040, by rfl⟩ : syracuseStep 1449387 = 2174081) B2174081
theorem B1449399 : Blo 1447543 1449399 := bstep (se 1 (by rfl) ⟨1087049, by rfl⟩ : syracuseStep 1449399 = 2174099) B2174099
theorem B1629643 : Blo 1447543 1629643 := bstep (se 1 (by rfl) ⟨1222232, by rfl⟩ : syracuseStep 1629643 = 2444465) B2444465
theorem B1449419 : Blo 1447543 1449419 := bstep (se 1 (by rfl) ⟨1087064, by rfl⟩ : syracuseStep 1449419 = 2174129) B2174129
theorem B1449431 : Blo 1447543 1449431 := bstep (se 1 (by rfl) ⟨1087073, by rfl⟩ : syracuseStep 1449431 = 2174147) B2174147
theorem B5496281 : Blo 1447543 5496281 := bstep (se 2 (by rfl) ⟨2061105, by rfl⟩ : syracuseStep 5496281 = 4122211) B4122211
theorem B4890077 : Blo 1447543 4890077 := bstep (se 3 (by rfl) ⟨916889, by rfl⟩ : syracuseStep 4890077 = 1833779) B1833779
theorem B1449451 : Blo 1447543 1449451 := bstep (se 1 (by rfl) ⟨1087088, by rfl⟩ : syracuseStep 1449451 = 2174177) B2174177
theorem B1449463 : Blo 1447543 1449463 := bstep (se 1 (by rfl) ⟨1087097, by rfl⟩ : syracuseStep 1449463 = 2174195) B2174195
theorem B1449483 : Blo 1447543 1449483 := bstep (se 1 (by rfl) ⟨1087112, by rfl⟩ : syracuseStep 1449483 = 2174225) B2174225
theorem B1449495 : Blo 1447543 1449495 := bstep (se 1 (by rfl) ⟨1087121, by rfl⟩ : syracuseStep 1449495 = 2174243) B2174243
theorem B1449515 : Blo 1447543 1449515 := bstep (se 1 (by rfl) ⟨1087136, by rfl⟩ : syracuseStep 1449515 = 2174273) B2174273
theorem B1629751 : Blo 1447543 1629751 := bstep (se 1 (by rfl) ⟨1222313, by rfl⟩ : syracuseStep 1629751 = 2444627) B2444627
theorem B1449527 : Blo 1447543 1449527 := bstep (se 1 (by rfl) ⟨1087145, by rfl⟩ : syracuseStep 1449527 = 2174291) B2174291
theorem B3259979 : Blo 1447543 3259979 := bstep (se 1 (by rfl) ⟨2444984, by rfl⟩ : syracuseStep 3259979 = 4889969) B4889969
theorem B3260033 : Blo 1447543 3260033 := bstep (se 2 (by rfl) ⟨1222512, by rfl⟩ : syracuseStep 3260033 = 2445025) B2445025
theorem B5217995 : Blo 1447543 5217995 := bstep (se 1 (by rfl) ⟨3913496, by rfl⟩ : syracuseStep 5217995 = 7826993) B7826993
theorem B1629931 : Blo 1447543 1629931 := bstep (se 1 (by rfl) ⟨1222448, by rfl⟩ : syracuseStep 1629931 = 2444897) B2444897
theorem B12377873 : Blo 1447543 12377873 := bstep (se 2 (by rfl) ⟨4641702, by rfl⟩ : syracuseStep 12377873 = 9283405) B9283405
theorem B5496599 : Blo 1447543 5496599 := bstep (se 1 (by rfl) ⟨4122449, by rfl⟩ : syracuseStep 5496599 = 8244899) B8244899
theorem B1630039 : Blo 1447543 1630039 := bstep (se 1 (by rfl) ⟨1222529, by rfl⟩ : syracuseStep 1630039 = 2445059) B2445059
theorem B3260249 : Blo 1447543 3260249 := bstep (se 2 (by rfl) ⟨1222593, by rfl⟩ : syracuseStep 3260249 = 2445187) B2445187
theorem B5218141 : Blo 1447543 5218141 := bstep (se 3 (by rfl) ⟨978401, by rfl⟩ : syracuseStep 5218141 = 1956803) B1956803
theorem B3260339 : Blo 1447543 3260339 := bstep (se 1 (by rfl) ⟨2445254, by rfl⟩ : syracuseStep 3260339 = 4890509) B4890509
theorem B3260375 : Blo 1447543 3260375 := bstep (se 1 (by rfl) ⟨2445281, by rfl⟩ : syracuseStep 3260375 = 4890563) B4890563
theorem B4407443 : Blo 1447543 4407443 := bstep (se 1 (by rfl) ⟨3305582, by rfl⟩ : syracuseStep 4407443 = 6611165) B6611165
theorem B6963401 : Blo 1447543 6963401 := bstep (se 2 (by rfl) ⟨2611275, by rfl⟩ : syracuseStep 6963401 = 5222551) B5222551
theorem B1630471 : Blo 1447543 1630471 := bstep (se 1 (by rfl) ⟨1222853, by rfl⟩ : syracuseStep 1630471 = 2445707) B2445707
theorem B6185231 : Blo 1447543 6185231 := bstep (se 1 (by rfl) ⟨4638923, by rfl⟩ : syracuseStep 6185231 = 9277847) B9277847
theorem B4890995 : Blo 1447543 4890995 := bstep (se 1 (by rfl) ⟨3668246, by rfl⟩ : syracuseStep 4890995 = 7336493) B7336493
theorem B3260807 : Blo 1447543 3260807 := bstep (se 1 (by rfl) ⟨2445605, by rfl⟩ : syracuseStep 3260807 = 4891211) B4891211
theorem B2171321 : Blo 1447543 2171321 := bstep (se 2 (by rfl) ⟨814245, by rfl⟩ : syracuseStep 2171321 = 1628491) B1628491
theorem B7332281 : Blo 1447543 7332281 := bstep (se 2 (by rfl) ⟨2749605, by rfl⟩ : syracuseStep 7332281 = 5499211) B5499211
theorem B1630651 : Blo 1447543 1630651 := bstep (se 1 (by rfl) ⟨1222988, by rfl⟩ : syracuseStep 1630651 = 2445977) B2445977
theorem B7832011 : Blo 1447543 7832011 := bstep (se 1 (by rfl) ⟨5874008, by rfl⟩ : syracuseStep 7832011 = 11748017) B11748017
theorem B2171399 : Blo 1447543 2171399 := bstep (se 1 (by rfl) ⟨1628549, by rfl⟩ : syracuseStep 2171399 = 3257099) B3257099
theorem B2171435 : Blo 1447543 2171435 := bstep (se 1 (by rfl) ⟨1628576, by rfl⟩ : syracuseStep 2171435 = 3257153) B3257153
theorem B3260987 : Blo 1447543 3260987 := bstep (se 1 (by rfl) ⟨2445740, by rfl⟩ : syracuseStep 3260987 = 4891481) B4891481
theorem B2171465 : Blo 1447543 2171465 := bstep (se 2 (by rfl) ⟨814299, by rfl⟩ : syracuseStep 2171465 = 1628599) B1628599
theorem B3261113 : Blo 1447543 3261113 := bstep (se 2 (by rfl) ⟨1222917, by rfl⟩ : syracuseStep 3261113 = 2445835) B2445835
theorem B2171579 : Blo 1447543 2171579 := bstep (se 1 (by rfl) ⟨1628684, by rfl⟩ : syracuseStep 2171579 = 3257369) B3257369
theorem B23503553 : Blo 1447543 23503553 := bstep (se 2 (by rfl) ⟨8813832, by rfl⟩ : syracuseStep 23503553 = 17627665) B17627665
theorem B2171639 : Blo 1447543 2171639 := bstep (se 1 (by rfl) ⟨1628729, by rfl⟩ : syracuseStep 2171639 = 3257459) B3257459
theorem B1958647 : Blo 1447543 1958647 := bstep (se 1 (by rfl) ⟨1468985, by rfl⟩ : syracuseStep 1958647 = 2937971) B2937971
theorem B12550913 : Blo 1447543 12550913 := bstep (se 2 (by rfl) ⟨4706592, by rfl⟩ : syracuseStep 12550913 = 9413185) B9413185
theorem B2171663 : Blo 1447543 2171663 := bstep (se 1 (by rfl) ⟨1628747, by rfl⟩ : syracuseStep 2171663 = 3257495) B3257495
theorem B2171705 : Blo 1447543 2171705 := bstep (se 2 (by rfl) ⟨814389, by rfl⟩ : syracuseStep 2171705 = 1628779) B1628779
theorem B2171783 : Blo 1447543 2171783 := bstep (se 1 (by rfl) ⟨1628837, by rfl⟩ : syracuseStep 2171783 = 3257675) B3257675
theorem B5497753 : Blo 1447543 5497753 := bstep (se 2 (by rfl) ⟨2061657, by rfl⟩ : syracuseStep 5497753 = 4123315) B4123315
theorem B2171819 : Blo 1447543 2171819 := bstep (se 1 (by rfl) ⟨1628864, by rfl⟩ : syracuseStep 2171819 = 3257729) B3257729
theorem B2171849 : Blo 1447543 2171849 := bstep (se 2 (by rfl) ⟨814443, by rfl⟩ : syracuseStep 2171849 = 1628887) B1628887
theorem B3261455 : Blo 1447543 3261455 := bstep (se 1 (by rfl) ⟨2446091, by rfl⟩ : syracuseStep 3261455 = 4892183) B4892183
theorem B3261473 : Blo 1447543 3261473 := bstep (se 2 (by rfl) ⟨1223052, by rfl⟩ : syracuseStep 3261473 = 2446105) B2446105
theorem B2171963 : Blo 1447543 2171963 := bstep (se 1 (by rfl) ⟨1628972, by rfl⟩ : syracuseStep 2171963 = 3257945) B3257945
theorem B2172023 : Blo 1447543 2172023 := bstep (se 1 (by rfl) ⟨1629017, by rfl⟩ : syracuseStep 2172023 = 3258035) B3258035
theorem B2172047 : Blo 1447543 2172047 := bstep (se 1 (by rfl) ⟨1629035, by rfl⟩ : syracuseStep 2172047 = 3258071) B3258071
theorem B3482777 : Blo 1447543 3482777 := bstep (se 2 (by rfl) ⟨1306041, by rfl⟩ : syracuseStep 3482777 = 2612083) B2612083
theorem B2172089 : Blo 1447543 2172089 := bstep (se 2 (by rfl) ⟨814533, by rfl⟩ : syracuseStep 2172089 = 1629067) B1629067
theorem B5498057 : Blo 1447543 5498057 := bstep (se 2 (by rfl) ⟨2061771, by rfl⟩ : syracuseStep 5498057 = 4123543) B4123543
theorem B2172167 : Blo 1447543 2172167 := bstep (se 1 (by rfl) ⟨1629125, by rfl⟩ : syracuseStep 2172167 = 3258251) B3258251
theorem B3302689 : Blo 1447543 3302689 := bstep (se 2 (by rfl) ⟨1238508, by rfl⟩ : syracuseStep 3302689 = 2477017) B2477017
theorem B2172203 : Blo 1447543 2172203 := bstep (se 1 (by rfl) ⟨1629152, by rfl⟩ : syracuseStep 2172203 = 3258305) B3258305
theorem B2172233 : Blo 1447543 2172233 := bstep (se 2 (by rfl) ⟨814587, by rfl⟩ : syracuseStep 2172233 = 1629175) B1629175
theorem B2172347 : Blo 1447543 2172347 := bstep (se 1 (by rfl) ⟨1629260, by rfl⟩ : syracuseStep 2172347 = 3258521) B3258521
theorem B2172407 : Blo 1447543 2172407 := bstep (se 1 (by rfl) ⟨1629305, by rfl⟩ : syracuseStep 2172407 = 3258611) B3258611
theorem B1467919 : Blo 1447543 1467919 := bstep (se 1 (by rfl) ⟨1100939, by rfl⟩ : syracuseStep 1467919 = 2201879) B2201879
theorem B2172431 : Blo 1447543 2172431 := bstep (se 1 (by rfl) ⟨1629323, by rfl⟩ : syracuseStep 2172431 = 3258647) B3258647
theorem B2172473 : Blo 1447543 2172473 := bstep (se 2 (by rfl) ⟨814677, by rfl⟩ : syracuseStep 2172473 = 1629355) B1629355
theorem B2442811 : Blo 1447543 2442811 := bstep (se 1 (by rfl) ⟨1832108, by rfl⟩ : syracuseStep 2442811 = 3664217) B3664217
theorem B25445987 : Blo 1447543 25445987 := bstep (se 1 (by rfl) ⟨19084490, by rfl⟩ : syracuseStep 25445987 = 38168981) B38168981
theorem B9274999 : Blo 1447543 9274999 := bstep (se 1 (by rfl) ⟨6956249, by rfl⟩ : syracuseStep 9274999 = 13912499) B13912499
theorem B2172551 : Blo 1447543 2172551 := bstep (se 1 (by rfl) ⟨1629413, by rfl⟩ : syracuseStep 2172551 = 3258827) B3258827
theorem B3966617 : Blo 1447543 3966617 := bstep (se 2 (by rfl) ⟨1487481, by rfl⟩ : syracuseStep 3966617 = 2974963) B2974963
theorem B2172587 : Blo 1447543 2172587 := bstep (se 1 (by rfl) ⟨1629440, by rfl⟩ : syracuseStep 2172587 = 3258881) B3258881
theorem B2442953 : Blo 1447543 2442953 := bstep (se 2 (by rfl) ⟨916107, by rfl⟩ : syracuseStep 2442953 = 1832215) B1832215
theorem B2172617 : Blo 1447543 2172617 := bstep (se 2 (by rfl) ⟨814731, by rfl⟩ : syracuseStep 2172617 = 1629463) B1629463
theorem B7333577 : Blo 1447543 7333577 := bstep (se 2 (by rfl) ⟨2750091, by rfl⟩ : syracuseStep 7333577 = 5500183) B5500183
theorem B10438415 : Blo 1447543 10438415 := bstep (se 1 (by rfl) ⟨7828811, by rfl⟩ : syracuseStep 10438415 = 15657623) B15657623
theorem B4122427 : Blo 1447543 4122427 := bstep (se 1 (by rfl) ⟨3091820, by rfl⟩ : syracuseStep 4122427 = 6183641) B6183641
theorem B2172731 : Blo 1447543 2172731 := bstep (se 1 (by rfl) ⟨1629548, by rfl⟩ : syracuseStep 2172731 = 3259097) B3259097
theorem B133883765 : Blo 1447543 133883765 := bstep (se 5 (by rfl) ⟨6275801, by rfl⟩ : syracuseStep 133883765 = 12551603) B12551603
theorem B2172791 : Blo 1447543 2172791 := bstep (se 1 (by rfl) ⟨1629593, by rfl⟩ : syracuseStep 2172791 = 3259187) B3259187
theorem B6186887 : Blo 1447543 6186887 := bstep (se 1 (by rfl) ⟨4640165, by rfl⟩ : syracuseStep 6186887 = 9280331) B9280331
theorem B2172815 : Blo 1447543 2172815 := bstep (se 1 (by rfl) ⟨1629611, by rfl⟩ : syracuseStep 2172815 = 3259223) B3259223
theorem B4638617 : Blo 1447543 4638617 := bstep (se 2 (by rfl) ⟨1739481, by rfl⟩ : syracuseStep 4638617 = 3478963) B3478963
theorem B2172857 : Blo 1447543 2172857 := bstep (se 2 (by rfl) ⟨814821, by rfl⟩ : syracuseStep 2172857 = 1629643) B1629643
theorem B16508933 : Blo 1447543 16508933 := bstep (se 4 (by rfl) ⟨1547712, by rfl⟩ : syracuseStep 16508933 = 3095425) B3095425
theorem B2172935 : Blo 1447543 2172935 := bstep (se 1 (by rfl) ⟨1629701, by rfl⟩ : syracuseStep 2172935 = 3259403) B3259403
theorem B8251415 : Blo 1447543 8251415 := bstep (se 1 (by rfl) ⟨6188561, by rfl⟩ : syracuseStep 8251415 = 12377123) B12377123
theorem B2172971 : Blo 1447543 2172971 := bstep (se 1 (by rfl) ⟨1629728, by rfl⟩ : syracuseStep 2172971 = 3259457) B3259457
theorem B2173001 : Blo 1447543 2173001 := bstep (se 2 (by rfl) ⟨814875, by rfl⟩ : syracuseStep 2173001 = 1629751) B1629751
theorem B5498999 : Blo 1447543 5498999 := bstep (se 1 (by rfl) ⟨4124249, by rfl⟩ : syracuseStep 5498999 = 8248499) B8248499
theorem B12372101 : Blo 1447543 12372101 := bstep (se 4 (by rfl) ⟨1159884, by rfl⟩ : syracuseStep 12372101 = 2319769) B2319769
theorem B2173115 : Blo 1447543 2173115 := bstep (se 1 (by rfl) ⟨1629836, by rfl⟩ : syracuseStep 2173115 = 3259673) B3259673
theorem B2173175 : Blo 1447543 2173175 := bstep (se 1 (by rfl) ⟨1629881, by rfl⟩ : syracuseStep 2173175 = 3259763) B3259763
theorem B2173199 : Blo 1447543 2173199 := bstep (se 1 (by rfl) ⟨1629899, by rfl⟩ : syracuseStep 2173199 = 3259799) B3259799
theorem B2173241 : Blo 1447543 2173241 := bstep (se 2 (by rfl) ⟨814965, by rfl⟩ : syracuseStep 2173241 = 1629931) B1629931
theorem B3664187 : Blo 1447543 3664187 := bstep (se 1 (by rfl) ⟨2748140, by rfl⟩ : syracuseStep 3664187 = 5496281) B5496281
theorem B2443655 : Blo 1447543 2443655 := bstep (se 1 (by rfl) ⟨1832741, by rfl⟩ : syracuseStep 2443655 = 3665483) B3665483
theorem B2173319 : Blo 1447543 2173319 := bstep (se 1 (by rfl) ⟨1629989, by rfl⟩ : syracuseStep 2173319 = 3259979) B3259979
theorem B2173355 : Blo 1447543 2173355 := bstep (se 1 (by rfl) ⟨1630016, by rfl⟩ : syracuseStep 2173355 = 3260033) B3260033
theorem B2173385 : Blo 1447543 2173385 := bstep (se 2 (by rfl) ⟨815019, by rfl⟩ : syracuseStep 2173385 = 1630039) B1630039
theorem B6957521 : Blo 1447543 6957521 := bstep (se 2 (by rfl) ⟨2609070, by rfl⟩ : syracuseStep 6957521 = 5218141) B5218141
theorem B8251915 : Blo 1447543 8251915 := bstep (se 1 (by rfl) ⟨6188936, by rfl⟩ : syracuseStep 8251915 = 12377873) B12377873
theorem B3664399 : Blo 1447543 3664399 := bstep (se 1 (by rfl) ⟨2748299, by rfl⟩ : syracuseStep 3664399 = 5496599) B5496599
theorem B2173499 : Blo 1447543 2173499 := bstep (se 1 (by rfl) ⟨1630124, by rfl⟩ : syracuseStep 2173499 = 3260249) B3260249
theorem B2173559 : Blo 1447543 2173559 := bstep (se 1 (by rfl) ⟨1630169, by rfl⟩ : syracuseStep 2173559 = 3260339) B3260339
theorem B5294711 : Blo 1447543 5294711 := bstep (se 1 (by rfl) ⟨3971033, by rfl⟩ : syracuseStep 5294711 = 7942067) B7942067
theorem B2173583 : Blo 1447543 2173583 := bstep (se 1 (by rfl) ⟨1630187, by rfl⟩ : syracuseStep 2173583 = 3260375) B3260375
theorem B2173625 : Blo 1447543 2173625 := bstep (se 2 (by rfl) ⟨815109, by rfl⟩ : syracuseStep 2173625 = 1630219) B1630219
theorem B2173703 : Blo 1447543 2173703 := bstep (se 1 (by rfl) ⟨1630277, by rfl⟩ : syracuseStep 2173703 = 3260555) B3260555
theorem B3664673 : Blo 1447543 3664673 := bstep (se 2 (by rfl) ⟨1374252, by rfl⟩ : syracuseStep 3664673 = 2748505) B2748505
theorem B2173739 : Blo 1447543 2173739 := bstep (se 1 (by rfl) ⟨1630304, by rfl⟩ : syracuseStep 2173739 = 3260609) B3260609
theorem B2173769 : Blo 1447543 2173769 := bstep (se 2 (by rfl) ⟨815163, by rfl⟩ : syracuseStep 2173769 = 1630327) B1630327
theorem B12544883 : Blo 1447543 12544883 := bstep (se 1 (by rfl) ⟨9408662, by rfl⟩ : syracuseStep 12544883 = 18817325) B18817325
theorem B1739639 : Blo 1447543 1739639 := bstep (se 1 (by rfl) ⟨1304729, by rfl⟩ : syracuseStep 1739639 = 2609459) B2609459
theorem B2173883 : Blo 1447543 2173883 := bstep (se 1 (by rfl) ⟨1630412, by rfl⟩ : syracuseStep 2173883 = 3260825) B3260825
theorem B2173943 : Blo 1447543 2173943 := bstep (se 1 (by rfl) ⟨1630457, by rfl⟩ : syracuseStep 2173943 = 3260915) B3260915
theorem B2444303 : Blo 1447543 2444303 := bstep (se 1 (by rfl) ⟨1833227, by rfl⟩ : syracuseStep 2444303 = 3666455) B3666455
theorem B2173967 : Blo 1447543 2173967 := bstep (se 1 (by rfl) ⟨1630475, by rfl⟩ : syracuseStep 2173967 = 3260951) B3260951
theorem B2174009 : Blo 1447543 2174009 := bstep (se 2 (by rfl) ⟨815253, by rfl⟩ : syracuseStep 2174009 = 1630507) B1630507
theorem B3714107 : Blo 1447543 3714107 := bstep (se 1 (by rfl) ⟨2785580, by rfl⟩ : syracuseStep 3714107 = 5571161) B5571161
theorem B5499971 : Blo 1447543 5499971 := bstep (se 1 (by rfl) ⟨4124978, by rfl⟩ : syracuseStep 5499971 = 8249957) B8249957
theorem B2174087 : Blo 1447543 2174087 := bstep (se 1 (by rfl) ⟨1630565, by rfl⟩ : syracuseStep 2174087 = 3261131) B3261131
theorem B1739947 : Blo 1447543 1739947 := bstep (se 1 (by rfl) ⟨1304960, by rfl⟩ : syracuseStep 1739947 = 2609921) B2609921
theorem B2174123 : Blo 1447543 2174123 := bstep (se 1 (by rfl) ⟨1630592, by rfl⟩ : syracuseStep 2174123 = 3261185) B3261185
theorem B2174153 : Blo 1447543 2174153 := bstep (se 2 (by rfl) ⟨815307, by rfl⟩ : syracuseStep 2174153 = 1630615) B1630615
theorem B20360429 : Blo 1447543 20360429 := bstep (se 3 (by rfl) ⟨3817580, by rfl⟩ : syracuseStep 20360429 = 7635161) B7635161
theorem B2321723 : Blo 1447543 2321723 := bstep (se 1 (by rfl) ⟨1741292, by rfl⟩ : syracuseStep 2321723 = 3482585) B3482585
theorem B2174267 : Blo 1447543 2174267 := bstep (se 1 (by rfl) ⟨1630700, by rfl⟩ : syracuseStep 2174267 = 3261401) B3261401
theorem B5877107 : Blo 1447543 5877107 := bstep (se 1 (by rfl) ⟨4407830, by rfl⟩ : syracuseStep 5877107 = 8815661) B8815661
theorem B2682247 : Blo 1447543 2682247 := bstep (se 1 (by rfl) ⟨2011685, by rfl⟩ : syracuseStep 2682247 = 4023371) B4023371
theorem B8244625 : Blo 1447543 8244625 := bstep (se 2 (by rfl) ⟨3091734, by rfl⟩ : syracuseStep 8244625 = 6183469) B6183469
theorem B4886027 : Blo 1447543 4886027 := bstep (se 1 (by rfl) ⟨3664520, by rfl⟩ : syracuseStep 4886027 = 7329041) B7329041
theorem B11005469 : Blo 1447543 11005469 := bstep (se 3 (by rfl) ⟨2063525, by rfl⟩ : syracuseStep 11005469 = 4127051) B4127051
theorem B1740331 : Blo 1447543 1740331 := bstep (se 1 (by rfl) ⟨1305248, by rfl⟩ : syracuseStep 1740331 = 2610497) B2610497
theorem B2444843 : Blo 1447543 2444843 := bstep (se 1 (by rfl) ⟨1833632, by rfl⟩ : syracuseStep 2444843 = 3667265) B3667265
theorem B4886135 : Blo 1447543 4886135 := bstep (se 1 (by rfl) ⟨3664601, by rfl⟩ : syracuseStep 4886135 = 7329203) B7329203
theorem B6188663 : Blo 1447543 6188663 := bstep (se 1 (by rfl) ⟨4641497, by rfl⟩ : syracuseStep 6188663 = 9282995) B9282995
theorem B39628439 : Blo 1447543 39628439 := bstep (se 1 (by rfl) ⟨29721329, by rfl⟩ : syracuseStep 39628439 = 59442659) B59442659
theorem B412544663 : Blo 1447543 412544663 := bstep (se 1 (by rfl) ⟨309408497, by rfl⟩ : syracuseStep 412544663 = 618816995) B618816995
theorem B3665675 : Blo 1447543 3665675 := bstep (se 1 (by rfl) ⟨2749256, by rfl⟩ : syracuseStep 3665675 = 5498513) B5498513
theorem B2232079 : Blo 1447543 2232079 := bstep (se 1 (by rfl) ⟨1674059, by rfl⟩ : syracuseStep 2232079 = 3348119) B3348119
theorem B4640627 : Blo 1447543 4640627 := bstep (se 1 (by rfl) ⟨3480470, by rfl⟩ : syracuseStep 4640627 = 6960941) B6960941
theorem B2445241 : Blo 1447543 2445241 := bstep (se 2 (by rfl) ⟨916965, by rfl⟩ : syracuseStep 2445241 = 1833931) B1833931
theorem B6959171 : Blo 1447543 6959171 := bstep (se 1 (by rfl) ⟨5219378, by rfl⟩ : syracuseStep 6959171 = 10438757) B10438757
theorem B4124819 : Blo 1447543 4124819 := bstep (se 1 (by rfl) ⟨3093614, by rfl⟩ : syracuseStep 4124819 = 6187229) B6187229
theorem B4886729 : Blo 1447543 4886729 := bstep (se 2 (by rfl) ⟨1832523, by rfl⟩ : syracuseStep 4886729 = 3665047) B3665047
theorem B28233929 : Blo 1447543 28233929 := bstep (se 2 (by rfl) ⟨10587723, by rfl⟩ : syracuseStep 28233929 = 21175447) B21175447
theorem B4706695 : Blo 1447543 4706695 := bstep (se 1 (by rfl) ⟨3530021, by rfl⟩ : syracuseStep 4706695 = 7060043) B7060043
theorem B3666323 : Blo 1447543 3666323 := bstep (se 1 (by rfl) ⟨2749742, by rfl⟩ : syracuseStep 3666323 = 5499485) B5499485
theorem B8253899 : Blo 1447543 8253899 := bstep (se 1 (by rfl) ⟨6190424, by rfl⟩ : syracuseStep 8253899 = 12380849) B12380849
theorem B6189655 : Blo 1447543 6189655 := bstep (se 1 (by rfl) ⟨4642241, by rfl⟩ : syracuseStep 6189655 = 9284483) B9284483
theorem B2445943 : Blo 1447543 2445943 := bstep (se 1 (by rfl) ⟨1834457, by rfl⟩ : syracuseStep 2445943 = 3668915) B3668915
theorem B3666617 : Blo 1447543 3666617 := bstep (se 2 (by rfl) ⟨1374981, by rfl⟩ : syracuseStep 3666617 = 2749963) B2749963
theorem B5501641 : Blo 1447543 5501641 := bstep (se 2 (by rfl) ⟨2063115, by rfl⟩ : syracuseStep 5501641 = 4126231) B4126231
theorem B5288719 : Blo 1447543 5288719 := bstep (se 1 (by rfl) ⟨3966539, by rfl⟩ : syracuseStep 5288719 = 7933079) B7933079
theorem B3257207 : Blo 1447543 3257207 := bstep (se 1 (by rfl) ⟨2442905, by rfl⟩ : syracuseStep 3257207 = 4885811) B4885811
theorem B4887431 : Blo 1447543 4887431 := bstep (se 1 (by rfl) ⟨3665573, by rfl⟩ : syracuseStep 4887431 = 7331147) B7331147
theorem B4125593 : Blo 1447543 4125593 := bstep (se 2 (by rfl) ⟨1547097, by rfl⟩ : syracuseStep 4125593 = 3094195) B3094195
theorem B14873507 : Blo 1447543 14873507 := bstep (se 1 (by rfl) ⟨11155130, by rfl⟩ : syracuseStep 14873507 = 22310261) B22310261
theorem B3257387 : Blo 1447543 3257387 := bstep (se 1 (by rfl) ⟨2443040, by rfl⟩ : syracuseStep 3257387 = 4886081) B4886081
theorem B17855549 : Blo 1447543 17855549 := bstep (se 3 (by rfl) ⟨3347915, by rfl⟩ : syracuseStep 17855549 = 6695831) B6695831
theorem B3478663 : Blo 1447543 3478663 := bstep (se 1 (by rfl) ⟨2608997, by rfl⟩ : syracuseStep 3478663 = 5217995) B5217995
theorem B3716243 : Blo 1447543 3716243 := bstep (se 1 (by rfl) ⟨2787182, by rfl⟩ : syracuseStep 3716243 = 5574365) B5574365
theorem B4887809 : Blo 1447543 4887809 := bstep (se 2 (by rfl) ⟨1832928, by rfl⟩ : syracuseStep 4887809 = 3665857) B3665857
theorem B3478817 : Blo 1447543 3478817 := bstep (se 2 (by rfl) ⟨1304556, by rfl⟩ : syracuseStep 3478817 = 2609113) B2609113
theorem B33436961 : Blo 1447543 33436961 := bstep (se 2 (by rfl) ⟨12538860, by rfl⟩ : syracuseStep 33436961 = 25077721) B25077721
theorem B3667315 : Blo 1447543 3667315 := bstep (se 1 (by rfl) ⟨2750486, by rfl⟩ : syracuseStep 3667315 = 5500973) B5500973
theorem B1832311 : Blo 1447543 1832311 := bstep (se 1 (by rfl) ⟨1374233, by rfl⟩ : syracuseStep 1832311 = 2748467) B2748467
theorem B2061703 : Blo 1447543 2061703 := bstep (se 1 (by rfl) ⟨1546277, by rfl⟩ : syracuseStep 2061703 = 3092555) B3092555
theorem B3257747 : Blo 1447543 3257747 := bstep (se 1 (by rfl) ⟨2443310, by rfl⟩ : syracuseStep 3257747 = 4886621) B4886621
theorem B28227001 : Blo 1447543 28227001 := bstep (se 2 (by rfl) ⟨10585125, by rfl⟩ : syracuseStep 28227001 = 21170251) B21170251
theorem B3257801 : Blo 1447543 3257801 := bstep (se 2 (by rfl) ⟨1221675, by rfl⟩ : syracuseStep 3257801 = 2443351) B2443351
theorem B3667457 : Blo 1447543 3667457 := bstep (se 2 (by rfl) ⟨1375296, by rfl⟩ : syracuseStep 3667457 = 2750593) B2750593
theorem B1447559 : Blo 1447543 1447559 := bstep (se 1 (by rfl) ⟨1085669, by rfl⟩ : syracuseStep 1447559 = 2171339) B2171339
theorem B1447567 : Blo 1447543 1447567 := bstep (se 1 (by rfl) ⟨1085675, by rfl⟩ : syracuseStep 1447567 = 2171351) B2171351
theorem B1447611 : Blo 1447543 1447611 := bstep (se 1 (by rfl) ⟨1085708, by rfl⟩ : syracuseStep 1447611 = 2171417) B2171417
theorem B1832635 : Blo 1447543 1832635 := bstep (se 1 (by rfl) ⟨1374476, by rfl⟩ : syracuseStep 1832635 = 2748953) B2748953
theorem B8247041 : Blo 1447543 8247041 := bstep (se 2 (by rfl) ⟨3092640, by rfl⟩ : syracuseStep 8247041 = 6185281) B6185281
theorem B1447687 : Blo 1447543 1447687 := bstep (se 1 (by rfl) ⟨1085765, by rfl⟩ : syracuseStep 1447687 = 2171531) B2171531
theorem B1447695 : Blo 1447543 1447695 := bstep (se 1 (by rfl) ⟨1085771, by rfl⟩ : syracuseStep 1447695 = 2171543) B2171543
theorem B1447739 : Blo 1447543 1447739 := bstep (se 1 (by rfl) ⟨1085804, by rfl⟩ : syracuseStep 1447739 = 2171609) B2171609
theorem B2750267 : Blo 1447543 2750267 := bstep (se 1 (by rfl) ⟨2062700, by rfl⟩ : syracuseStep 2750267 = 4125401) B4125401
theorem B12719987 : Blo 1447543 12719987 := bstep (se 1 (by rfl) ⟨9539990, by rfl⟩ : syracuseStep 12719987 = 19079981) B19079981
theorem B2062199 : Blo 1447543 2062199 := bstep (se 1 (by rfl) ⟨1546649, by rfl⟩ : syracuseStep 2062199 = 3093299) B3093299
theorem B1447815 : Blo 1447543 1447815 := bstep (se 1 (by rfl) ⟨1085861, by rfl⟩ : syracuseStep 1447815 = 2171723) B2171723
theorem B1447823 : Blo 1447543 1447823 := bstep (se 1 (by rfl) ⟨1085867, by rfl⟩ : syracuseStep 1447823 = 2171735) B2171735
theorem B7329689 : Blo 1447543 7329689 := bstep (se 2 (by rfl) ⟨2748633, by rfl⟩ : syracuseStep 7329689 = 5497267) B5497267
theorem B1447867 : Blo 1447543 1447867 := bstep (se 1 (by rfl) ⟨1085900, by rfl⟩ : syracuseStep 1447867 = 2171801) B2171801
theorem B3667913 : Blo 1447543 3667913 := bstep (se 2 (by rfl) ⟨1375467, by rfl⟩ : syracuseStep 3667913 = 2750935) B2750935
theorem B8812547 : Blo 1447543 8812547 := bstep (se 1 (by rfl) ⟨6609410, by rfl⟩ : syracuseStep 8812547 = 13218821) B13218821
theorem B1447943 : Blo 1447543 1447943 := bstep (se 1 (by rfl) ⟨1085957, by rfl⟩ : syracuseStep 1447943 = 2171915) B2171915
theorem B1447951 : Blo 1447543 1447951 := bstep (se 1 (by rfl) ⟨1085963, by rfl⟩ : syracuseStep 1447951 = 2171927) B2171927
theorem B4888619 : Blo 1447543 4888619 := bstep (se 1 (by rfl) ⟨3666464, by rfl⟩ : syracuseStep 4888619 = 7332929) B7332929
theorem B3094571 : Blo 1447543 3094571 := bstep (se 1 (by rfl) ⟨2320928, by rfl⟩ : syracuseStep 3094571 = 4641857) B4641857
theorem B1447995 : Blo 1447543 1447995 := bstep (se 1 (by rfl) ⟨1085996, by rfl⟩ : syracuseStep 1447995 = 2171993) B2171993
theorem B1448071 : Blo 1447543 1448071 := bstep (se 1 (by rfl) ⟨1086053, by rfl⟩ : syracuseStep 1448071 = 2172107) B2172107
theorem B3258503 : Blo 1447543 3258503 := bstep (se 1 (by rfl) ⟨2443877, by rfl⟩ : syracuseStep 3258503 = 4887755) B4887755
theorem B1448079 : Blo 1447543 1448079 := bstep (se 1 (by rfl) ⟨1086059, by rfl⟩ : syracuseStep 1448079 = 2172119) B2172119
theorem B1833131 : Blo 1447543 1833131 := bstep (se 1 (by rfl) ⟨1374848, by rfl⟩ : syracuseStep 1833131 = 2749697) B2749697
theorem B1448123 : Blo 1447543 1448123 := bstep (se 1 (by rfl) ⟨1086092, by rfl⟩ : syracuseStep 1448123 = 2172185) B2172185
theorem B1448199 : Blo 1447543 1448199 := bstep (se 1 (by rfl) ⟨1086149, by rfl⟩ : syracuseStep 1448199 = 2172299) B2172299
theorem B1448207 : Blo 1447543 1448207 := bstep (se 1 (by rfl) ⟨1086155, by rfl⟩ : syracuseStep 1448207 = 2172311) B2172311
theorem B2750753 : Blo 1447543 2750753 := bstep (se 2 (by rfl) ⟨1031532, by rfl⟩ : syracuseStep 2750753 = 2063065) B2063065
theorem B3668267 : Blo 1447543 3668267 := bstep (se 1 (by rfl) ⟨2751200, by rfl⟩ : syracuseStep 3668267 = 5502401) B5502401
theorem B1448251 : Blo 1447543 1448251 := bstep (se 1 (by rfl) ⟨1086188, by rfl⟩ : syracuseStep 1448251 = 2172377) B2172377
theorem B3258683 : Blo 1447543 3258683 := bstep (se 1 (by rfl) ⟨2444012, by rfl⟩ : syracuseStep 3258683 = 4888025) B4888025
theorem B11000123 : Blo 1447543 11000123 := bstep (se 1 (by rfl) ⟨8250092, by rfl⟩ : syracuseStep 11000123 = 16500185) B16500185
theorem B1448327 : Blo 1447543 1448327 := bstep (se 1 (by rfl) ⟨1086245, by rfl⟩ : syracuseStep 1448327 = 2172491) B2172491
theorem B1448335 : Blo 1447543 1448335 := bstep (se 1 (by rfl) ⟨1086251, by rfl⟩ : syracuseStep 1448335 = 2172503) B2172503
theorem B6961555 : Blo 1447543 6961555 := bstep (se 1 (by rfl) ⟨5221166, by rfl⟩ : syracuseStep 6961555 = 10442333) B10442333
theorem B4954553 : Blo 1447543 4954553 := bstep (se 2 (by rfl) ⟨1857957, by rfl⟩ : syracuseStep 4954553 = 3715915) B3715915
theorem B3258809 : Blo 1447543 3258809 := bstep (se 2 (by rfl) ⟨1222053, by rfl⟩ : syracuseStep 3258809 = 2444107) B2444107
theorem B1448379 : Blo 1447543 1448379 := bstep (se 1 (by rfl) ⟨1086284, by rfl⟩ : syracuseStep 1448379 = 2172569) B2172569
theorem B1448455 : Blo 1447543 1448455 := bstep (se 1 (by rfl) ⟨1086341, by rfl⟩ : syracuseStep 1448455 = 2172683) B2172683
theorem B1448463 : Blo 1447543 1448463 := bstep (se 1 (by rfl) ⟨1086347, by rfl⟩ : syracuseStep 1448463 = 2172695) B2172695
theorem B7428631 : Blo 1447543 7428631 := bstep (se 1 (by rfl) ⟨5571473, by rfl⟩ : syracuseStep 7428631 = 11142947) B11142947
theorem B1448507 : Blo 1447543 1448507 := bstep (se 1 (by rfl) ⟨1086380, by rfl⟩ : syracuseStep 1448507 = 2172761) B2172761
theorem B1448583 : Blo 1447543 1448583 := bstep (se 1 (by rfl) ⟨1086437, by rfl⟩ : syracuseStep 1448583 = 2172875) B2172875
theorem B1833607 : Blo 1447543 1833607 := bstep (se 1 (by rfl) ⟨1375205, by rfl⟩ : syracuseStep 1833607 = 2750411) B2750411
theorem B1628815 : Blo 1447543 1628815 := bstep (se 1 (by rfl) ⟨1221611, by rfl⟩ : syracuseStep 1628815 = 2443223) B2443223
theorem B1448591 : Blo 1447543 1448591 := bstep (se 1 (by rfl) ⟨1086443, by rfl⟩ : syracuseStep 1448591 = 2172887) B2172887
theorem B1448635 : Blo 1447543 1448635 := bstep (se 1 (by rfl) ⟨1086476, by rfl⟩ : syracuseStep 1448635 = 2172953) B2172953
theorem B1448711 : Blo 1447543 1448711 := bstep (se 1 (by rfl) ⟨1086533, by rfl⟩ : syracuseStep 1448711 = 2173067) B2173067
theorem B3259151 : Blo 1447543 3259151 := bstep (se 1 (by rfl) ⟨2444363, by rfl⟩ : syracuseStep 3259151 = 4888727) B4888727
theorem B1448719 : Blo 1447543 1448719 := bstep (se 1 (by rfl) ⟨1086539, by rfl⟩ : syracuseStep 1448719 = 2173079) B2173079
theorem B3914525 : Blo 1447543 3914525 := bstep (se 3 (by rfl) ⟨733973, by rfl⟩ : syracuseStep 3914525 = 1467947) B1467947
theorem B3259169 : Blo 1447543 3259169 := bstep (se 2 (by rfl) ⟨1222188, by rfl⟩ : syracuseStep 3259169 = 2444377) B2444377
theorem B2063161 : Blo 1447543 2063161 := bstep (se 2 (by rfl) ⟨773685, by rfl⟩ : syracuseStep 2063161 = 1547371) B1547371
theorem B1448763 : Blo 1447543 1448763 := bstep (se 1 (by rfl) ⟨1086572, by rfl⟩ : syracuseStep 1448763 = 2173145) B2173145
theorem B1956727 : Blo 1447543 1956727 := bstep (se 1 (by rfl) ⟨1467545, by rfl⟩ : syracuseStep 1956727 = 2935091) B2935091
theorem B1448839 : Blo 1447543 1448839 := bstep (se 1 (by rfl) ⟨1086629, by rfl⟩ : syracuseStep 1448839 = 2173259) B2173259
theorem B1448847 : Blo 1447543 1448847 := bstep (se 1 (by rfl) ⟨1086635, by rfl⟩ : syracuseStep 1448847 = 2173271) B2173271
theorem B55663523 : Blo 1447543 55663523 := bstep (se 1 (by rfl) ⟨41747642, by rfl⟩ : syracuseStep 55663523 = 83495285) B83495285
theorem B2202553 : Blo 1447543 2202553 := bstep (se 2 (by rfl) ⟨825957, by rfl⟩ : syracuseStep 2202553 = 1651915) B1651915
theorem B1448891 : Blo 1447543 1448891 := bstep (se 1 (by rfl) ⟨1086668, by rfl⟩ : syracuseStep 1448891 = 2173337) B2173337
theorem B4127689 : Blo 1447543 4127689 := bstep (se 2 (by rfl) ⟨1547883, by rfl⟩ : syracuseStep 4127689 = 3095767) B3095767
theorem B1448967 : Blo 1447543 1448967 := bstep (se 1 (by rfl) ⟨1086725, by rfl⟩ : syracuseStep 1448967 = 2173451) B2173451
theorem B190528523 : Blo 1447543 190528523 := bstep (se 1 (by rfl) ⟨142896392, by rfl⟩ : syracuseStep 190528523 = 285792785) B285792785
theorem B1448975 : Blo 1447543 1448975 := bstep (se 1 (by rfl) ⟨1086731, by rfl⟩ : syracuseStep 1448975 = 2173463) B2173463
theorem B1449019 : Blo 1447543 1449019 := bstep (se 1 (by rfl) ⟨1086764, by rfl⟩ : syracuseStep 1449019 = 2173529) B2173529
theorem B3259511 : Blo 1447543 3259511 := bstep (se 1 (by rfl) ⟨2444633, by rfl⟩ : syracuseStep 3259511 = 4889267) B4889267
theorem B1834103 : Blo 1447543 1834103 := bstep (se 1 (by rfl) ⟨1375577, by rfl⟩ : syracuseStep 1834103 = 2751155) B2751155
theorem B1629319 : Blo 1447543 1629319 := bstep (se 1 (by rfl) ⟨1221989, by rfl⟩ : syracuseStep 1629319 = 2443979) B2443979
theorem B1449095 : Blo 1447543 1449095 := bstep (se 1 (by rfl) ⟨1086821, by rfl⟩ : syracuseStep 1449095 = 2173643) B2173643
theorem B1449103 : Blo 1447543 1449103 := bstep (se 1 (by rfl) ⟨1086827, by rfl⟩ : syracuseStep 1449103 = 2173655) B2173655
theorem B2063503 : Blo 1447543 2063503 := bstep (se 1 (by rfl) ⟨1547627, by rfl⟩ : syracuseStep 2063503 = 3095255) B3095255
theorem B1449147 : Blo 1447543 1449147 := bstep (se 1 (by rfl) ⟨1086860, by rfl⟩ : syracuseStep 1449147 = 2173721) B2173721
theorem B6610157 : Blo 1447543 6610157 := bstep (se 3 (by rfl) ⟨1239404, by rfl⟩ : syracuseStep 6610157 = 2478809) B2478809
theorem B1449223 : Blo 1447543 1449223 := bstep (se 1 (by rfl) ⟨1086917, by rfl⟩ : syracuseStep 1449223 = 2173835) B2173835
theorem B1449231 : Blo 1447543 1449231 := bstep (se 1 (by rfl) ⟨1086923, by rfl⟩ : syracuseStep 1449231 = 2173847) B2173847
theorem B1834255 : Blo 1447543 1834255 := bstep (se 1 (by rfl) ⟨1375691, by rfl⟩ : syracuseStep 1834255 = 2751383) B2751383
theorem B3259691 : Blo 1447543 3259691 := bstep (se 1 (by rfl) ⟨2444768, by rfl⟩ : syracuseStep 3259691 = 4889537) B4889537
theorem B1629499 : Blo 1447543 1629499 := bstep (se 1 (by rfl) ⟨1222124, by rfl⟩ : syracuseStep 1629499 = 2444249) B2444249
theorem B4889915 : Blo 1447543 4889915 := bstep (se 1 (by rfl) ⟨3667436, by rfl⟩ : syracuseStep 4889915 = 7334873) B7334873
theorem B1449275 : Blo 1447543 1449275 := bstep (se 1 (by rfl) ⟨1086956, by rfl⟩ : syracuseStep 1449275 = 2173913) B2173913
theorem B4406663 : Blo 1447543 4406663 := bstep (se 1 (by rfl) ⟨3304997, by rfl⟩ : syracuseStep 4406663 = 6609995) B6609995
theorem B1449351 : Blo 1447543 1449351 := bstep (se 1 (by rfl) ⟨1087013, by rfl⟩ : syracuseStep 1449351 = 2174027) B2174027
theorem B1449359 : Blo 1447543 1449359 := bstep (se 1 (by rfl) ⟨1087019, by rfl⟩ : syracuseStep 1449359 = 2174039) B2174039
theorem B1449403 : Blo 1447543 1449403 := bstep (se 1 (by rfl) ⟨1087052, by rfl⟩ : syracuseStep 1449403 = 2174105) B2174105
theorem B1834427 : Blo 1447543 1834427 := bstep (se 1 (by rfl) ⟨1375820, by rfl⟩ : syracuseStep 1834427 = 2751641) B2751641
theorem B1449479 : Blo 1447543 1449479 := bstep (se 1 (by rfl) ⟨1087109, by rfl⟩ : syracuseStep 1449479 = 2174219) B2174219
theorem B1449487 : Blo 1447543 1449487 := bstep (se 1 (by rfl) ⟨1087115, by rfl⟩ : syracuseStep 1449487 = 2174231) B2174231
theorem B1449531 : Blo 1447543 1449531 := bstep (se 1 (by rfl) ⟨1087148, by rfl⟩ : syracuseStep 1449531 = 2174297) B2174297
theorem B8805955 : Blo 1447543 8805955 := bstep (se 1 (by rfl) ⟨6604466, by rfl⟩ : syracuseStep 8805955 = 13208933) B13208933
theorem B41762405 : Blo 1447543 41762405 := bstep (se 4 (by rfl) ⟨3915225, by rfl⟩ : syracuseStep 41762405 = 7830451) B7830451
theorem B2350711 : Blo 1447543 2350711 := bstep (se 1 (by rfl) ⟨1763033, by rfl⟩ : syracuseStep 2350711 = 3526067) B3526067
theorem B3260051 : Blo 1447543 3260051 := bstep (se 1 (by rfl) ⟨2445038, by rfl⟩ : syracuseStep 3260051 = 4890077) B4890077
theorem B3260105 : Blo 1447543 3260105 := bstep (se 2 (by rfl) ⟨1222539, by rfl⟩ : syracuseStep 3260105 = 2445079) B2445079
theorem B2203337 : Blo 1447543 2203337 := bstep (se 2 (by rfl) ⟨826251, by rfl⟩ : syracuseStep 2203337 = 1652503) B1652503
theorem B11747045 : Blo 1447543 11747045 := bstep (se 4 (by rfl) ⟨1101285, by rfl⟩ : syracuseStep 11747045 = 2202571) B2202571
theorem B3481355 : Blo 1447543 3481355 := bstep (se 1 (by rfl) ⟨2611016, by rfl⟩ : syracuseStep 3481355 = 5222033) B5222033
theorem B1629967 : Blo 1447543 1629967 := bstep (se 1 (by rfl) ⟨1222475, by rfl⟩ : syracuseStep 1629967 = 2444951) B2444951
theorem B4890401 : Blo 1447543 4890401 := bstep (se 2 (by rfl) ⟨1833900, by rfl⟩ : syracuseStep 4890401 = 3667801) B3667801
theorem B8249273 : Blo 1447543 8249273 := bstep (se 2 (by rfl) ⟨3093477, by rfl⟩ : syracuseStep 8249273 = 6186955) B6186955
theorem B9904285 : Blo 1447543 9904285 := bstep (se 3 (by rfl) ⟨1857053, by rfl⟩ : syracuseStep 9904285 = 3714107) B3714107
theorem B9281765 : Blo 1447543 9281765 := bstep (se 4 (by rfl) ⟨870165, by rfl⟩ : syracuseStep 9281765 = 1740331) B1740331
theorem B3260663 : Blo 1447543 3260663 := bstep (se 1 (by rfl) ⟨2445497, by rfl⟩ : syracuseStep 3260663 = 4890995) B4890995
theorem B4890941 : Blo 1447543 4890941 := bstep (se 3 (by rfl) ⟨917051, by rfl⟩ : syracuseStep 4890941 = 1834103) B1834103
theorem B6275593 : Blo 1447543 6275593 := bstep (se 2 (by rfl) ⟨2353347, by rfl⟩ : syracuseStep 6275593 = 4706695) B4706695
theorem B9282073 : Blo 1447543 9282073 := bstep (se 2 (by rfl) ⟨3480777, by rfl⟩ : syracuseStep 9282073 = 6961555) B6961555
theorem B2171471 : Blo 1447543 2171471 := bstep (se 1 (by rfl) ⟨1628603, by rfl⟩ : syracuseStep 2171471 = 3257207) B3257207
theorem B11002553 : Blo 1447543 11002553 := bstep (se 2 (by rfl) ⟨4125957, by rfl⟩ : syracuseStep 11002553 = 8251915) B8251915
theorem B2171591 : Blo 1447543 2171591 := bstep (se 1 (by rfl) ⟨1628693, by rfl⟩ : syracuseStep 2171591 = 3257387) B3257387
theorem B9904841 : Blo 1447543 9904841 := bstep (se 2 (by rfl) ⟨3714315, by rfl⟩ : syracuseStep 9904841 = 7428631) B7428631
theorem B11903699 : Blo 1447543 11903699 := bstep (se 1 (by rfl) ⟨8927774, by rfl⟩ : syracuseStep 11903699 = 17855549) B17855549
theorem B3261257 : Blo 1447543 3261257 := bstep (se 2 (by rfl) ⟨1222971, by rfl⟩ : syracuseStep 3261257 = 2445943) B2445943
theorem B2171753 : Blo 1447543 2171753 := bstep (se 2 (by rfl) ⟨814407, by rfl⟩ : syracuseStep 2171753 = 1628815) B1628815
theorem B2319211 : Blo 1447543 2319211 := bstep (se 1 (by rfl) ⟨1739408, by rfl⟩ : syracuseStep 2319211 = 3478817) B3478817
theorem B22291307 : Blo 1447543 22291307 := bstep (se 1 (by rfl) ⟨16718480, by rfl⟩ : syracuseStep 22291307 = 33436961) B33436961
theorem B2171831 : Blo 1447543 2171831 := bstep (se 1 (by rfl) ⟨1628873, by rfl⟩ : syracuseStep 2171831 = 3257747) B3257747
theorem B2171867 : Blo 1447543 2171867 := bstep (se 1 (by rfl) ⟨1628900, by rfl⟩ : syracuseStep 2171867 = 3257801) B3257801
theorem B4891805 : Blo 1447543 4891805 := bstep (se 3 (by rfl) ⟨917213, by rfl⟩ : syracuseStep 4891805 = 1834427) B1834427
theorem B5498027 : Blo 1447543 5498027 := bstep (se 1 (by rfl) ⟨4123520, by rfl⟩ : syracuseStep 5498027 = 8247041) B8247041
theorem B8479991 : Blo 1447543 8479991 := bstep (se 1 (by rfl) ⟨6359993, by rfl⟩ : syracuseStep 8479991 = 12719987) B12719987
theorem B5875031 : Blo 1447543 5875031 := bstep (se 1 (by rfl) ⟨4406273, by rfl⟩ : syracuseStep 5875031 = 8812547) B8812547
theorem B11904421 : Blo 1447543 11904421 := bstep (se 4 (by rfl) ⟨1116039, by rfl⟩ : syracuseStep 11904421 = 2232079) B2232079
theorem B2172335 : Blo 1447543 2172335 := bstep (se 1 (by rfl) ⟨1629251, by rfl⟩ : syracuseStep 2172335 = 3258503) B3258503
theorem B4638217 : Blo 1447543 4638217 := bstep (se 2 (by rfl) ⟨1739331, by rfl⟩ : syracuseStep 4638217 = 3478663) B3478663
theorem B2172425 : Blo 1447543 2172425 := bstep (se 2 (by rfl) ⟨814659, by rfl⟩ : syracuseStep 2172425 = 1629319) B1629319
theorem B2442791 : Blo 1447543 2442791 := bstep (se 1 (by rfl) ⟨1832093, by rfl⟩ : syracuseStep 2442791 = 3664187) B3664187
theorem B2172455 : Blo 1447543 2172455 := bstep (se 1 (by rfl) ⟨1629341, by rfl⟩ : syracuseStep 2172455 = 3258683) B3258683
theorem B7333415 : Blo 1447543 7333415 := bstep (se 1 (by rfl) ⟨5500061, by rfl⟩ : syracuseStep 7333415 = 11000123) B11000123
theorem B2319929 : Blo 1447543 2319929 := bstep (se 2 (by rfl) ⟨869973, by rfl⟩ : syracuseStep 2319929 = 1739947) B1739947
theorem B3303035 : Blo 1447543 3303035 := bstep (se 1 (by rfl) ⟨2477276, by rfl⟩ : syracuseStep 3303035 = 4954553) B4954553
theorem B2172539 : Blo 1447543 2172539 := bstep (se 1 (by rfl) ⟨1629404, by rfl⟩ : syracuseStep 2172539 = 3258809) B3258809
theorem B11003525 : Blo 1447543 11003525 := bstep (se 4 (by rfl) ⟨1031580, by rfl⟩ : syracuseStep 11003525 = 2063161) B2063161
theorem B4638347 : Blo 1447543 4638347 := bstep (se 1 (by rfl) ⟨3478760, by rfl⟩ : syracuseStep 4638347 = 6957521) B6957521
theorem B2172665 : Blo 1447543 2172665 := bstep (se 2 (by rfl) ⟨814749, by rfl⟩ : syracuseStep 2172665 = 1629499) B1629499
theorem B2443081 : Blo 1447543 2443081 := bstep (se 2 (by rfl) ⟨916155, by rfl⟩ : syracuseStep 2443081 = 1832311) B1832311
theorem B2172767 : Blo 1447543 2172767 := bstep (se 1 (by rfl) ⟨1629575, by rfl⟩ : syracuseStep 2172767 = 3259151) B3259151
theorem B2443115 : Blo 1447543 2443115 := bstep (se 1 (by rfl) ⟨1832336, by rfl⟩ : syracuseStep 2443115 = 3664673) B3664673
theorem B2172779 : Blo 1447543 2172779 := bstep (se 1 (by rfl) ⟨1629584, by rfl⟩ : syracuseStep 2172779 = 3259169) B3259169
theorem B37636001 : Blo 1447543 37636001 := bstep (se 2 (by rfl) ⟨14113500, by rfl⟩ : syracuseStep 37636001 = 28227001) B28227001
theorem B127019015 : Blo 1447543 127019015 := bstep (se 1 (by rfl) ⟨95264261, by rfl⟩ : syracuseStep 127019015 = 190528523) B190528523
theorem B10995749 : Blo 1447543 10995749 := bstep (se 4 (by rfl) ⟨1030851, by rfl⟩ : syracuseStep 10995749 = 2061703) B2061703
theorem B10438733 : Blo 1447543 10438733 := bstep (se 3 (by rfl) ⟨1957262, by rfl⟩ : syracuseStep 10438733 = 3914525) B3914525
theorem B2173007 : Blo 1447543 2173007 := bstep (se 1 (by rfl) ⟨1629755, by rfl⟩ : syracuseStep 2173007 = 3259511) B3259511
theorem B11741273 : Blo 1447543 11741273 := bstep (se 2 (by rfl) ⟨4402977, by rfl⟩ : syracuseStep 11741273 = 8805955) B8805955
theorem B2173127 : Blo 1447543 2173127 := bstep (se 1 (by rfl) ⟨1629845, by rfl⟩ : syracuseStep 2173127 = 3259691) B3259691
theorem B3918071 : Blo 1447543 3918071 := bstep (se 1 (by rfl) ⟨2938553, by rfl⟩ : syracuseStep 3918071 = 5877107) B5877107
theorem B2443513 : Blo 1447543 2443513 := bstep (se 2 (by rfl) ⟨916317, by rfl⟩ : syracuseStep 2443513 = 1832635) B1832635
theorem B4639037 : Blo 1447543 4639037 := bstep (se 3 (by rfl) ⟨869819, by rfl⟩ : syracuseStep 4639037 = 1739639) B1739639
theorem B5499197 : Blo 1447543 5499197 := bstep (se 3 (by rfl) ⟨1031099, by rfl⟩ : syracuseStep 5499197 = 2062199) B2062199
theorem B2173289 : Blo 1447543 2173289 := bstep (se 2 (by rfl) ⟨814983, by rfl⟩ : syracuseStep 2173289 = 1629967) B1629967
theorem B2173367 : Blo 1447543 2173367 := bstep (se 1 (by rfl) ⟨1630025, by rfl⟩ : syracuseStep 2173367 = 3260051) B3260051
theorem B2173403 : Blo 1447543 2173403 := bstep (se 1 (by rfl) ⟨1630052, by rfl⟩ : syracuseStep 2173403 = 3260105) B3260105
theorem B1468891 : Blo 1447543 1468891 := bstep (se 1 (by rfl) ⟨1101668, by rfl⟩ : syracuseStep 1468891 = 2203337) B2203337
theorem B2443783 : Blo 1447543 2443783 := bstep (se 1 (by rfl) ⟨1832837, by rfl⟩ : syracuseStep 2443783 = 3665675) B3665675
theorem B2320903 : Blo 1447543 2320903 := bstep (se 1 (by rfl) ⟨1740677, by rfl⟩ : syracuseStep 2320903 = 3481355) B3481355
theorem B5499515 : Blo 1447543 5499515 := bstep (se 1 (by rfl) ⟨4124636, by rfl⟩ : syracuseStep 5499515 = 8249273) B8249273
theorem B4639447 : Blo 1447543 4639447 := bstep (se 1 (by rfl) ⟨3479585, by rfl⟩ : syracuseStep 4639447 = 6959171) B6959171
theorem B8252189 : Blo 1447543 8252189 := bstep (se 3 (by rfl) ⟨1547285, by rfl⟩ : syracuseStep 8252189 = 3094571) B3094571
theorem B4123487 : Blo 1447543 4123487 := bstep (se 1 (by rfl) ⟨3092615, by rfl⟩ : syracuseStep 4123487 = 6185231) B6185231
theorem B2173871 : Blo 1447543 2173871 := bstep (se 1 (by rfl) ⟨1630403, by rfl⟩ : syracuseStep 2173871 = 3260807) B3260807
theorem B2444215 : Blo 1447543 2444215 := bstep (se 1 (by rfl) ⟨1833161, by rfl⟩ : syracuseStep 2444215 = 3666323) B3666323
theorem B2173961 : Blo 1447543 2173961 := bstep (se 2 (by rfl) ⟨815235, by rfl⟩ : syracuseStep 2173961 = 1630471) B1630471
theorem B2173991 : Blo 1447543 2173991 := bstep (se 1 (by rfl) ⟨1630493, by rfl⟩ : syracuseStep 2173991 = 3260987) B3260987
theorem B2444411 : Blo 1447543 2444411 := bstep (se 1 (by rfl) ⟨1833308, by rfl⟩ : syracuseStep 2444411 = 3666617) B3666617
theorem B2174075 : Blo 1447543 2174075 := bstep (se 1 (by rfl) ⟨1630556, by rfl⟩ : syracuseStep 2174075 = 3261113) B3261113
theorem B8367275 : Blo 1447543 8367275 := bstep (se 1 (by rfl) ⟨6275456, by rfl⟩ : syracuseStep 8367275 = 12550913) B12550913
theorem B2174201 : Blo 1447543 2174201 := bstep (se 2 (by rfl) ⟨815325, by rfl⟩ : syracuseStep 2174201 = 1630651) B1630651
theorem B9915671 : Blo 1447543 9915671 := bstep (se 1 (by rfl) ⟨7436753, by rfl⟩ : syracuseStep 9915671 = 14873507) B14873507
theorem B12537125 : Blo 1447543 12537125 := bstep (se 4 (by rfl) ⟨1175355, by rfl⟩ : syracuseStep 12537125 = 2350711) B2350711
theorem B2174303 : Blo 1447543 2174303 := bstep (se 1 (by rfl) ⟨1630727, by rfl⟩ : syracuseStep 2174303 = 3261455) B3261455
theorem B4885865 : Blo 1447543 4885865 := bstep (se 2 (by rfl) ⟨1832199, by rfl⟩ : syracuseStep 4885865 = 3664399) B3664399
theorem B2174315 : Blo 1447543 2174315 := bstep (se 1 (by rfl) ⟨1630736, by rfl⟩ : syracuseStep 2174315 = 3261473) B3261473
theorem B2477495 : Blo 1447543 2477495 := bstep (se 1 (by rfl) ⟨1858121, by rfl⟩ : syracuseStep 2477495 = 3716243) B3716243
theorem B8252873 : Blo 1447543 8252873 := bstep (se 2 (by rfl) ⟨3094827, by rfl⟩ : syracuseStep 8252873 = 6189655) B6189655
theorem B3665371 : Blo 1447543 3665371 := bstep (se 1 (by rfl) ⟨2749028, by rfl⟩ : syracuseStep 3665371 = 5498057) B5498057
theorem B2444809 : Blo 1447543 2444809 := bstep (se 2 (by rfl) ⟨916803, by rfl⟩ : syracuseStep 2444809 = 1833607) B1833607
theorem B7335521 : Blo 1447543 7335521 := bstep (se 2 (by rfl) ⟨2750820, by rfl⟩ : syracuseStep 7335521 = 5501641) B5501641
theorem B2444971 : Blo 1447543 2444971 := bstep (se 1 (by rfl) ⟨1833728, by rfl⟩ : syracuseStep 2444971 = 3667457) B3667457
theorem B11751101 : Blo 1447543 11751101 := bstep (se 3 (by rfl) ⟨2203331, by rfl⟩ : syracuseStep 11751101 = 4406663) B4406663
theorem B6958943 : Blo 1447543 6958943 := bstep (se 1 (by rfl) ⟨5219207, by rfl⟩ : syracuseStep 6958943 = 10438415) B10438415
theorem B2936737 : Blo 1447543 2936737 := bstep (se 2 (by rfl) ⟨1101276, by rfl⟩ : syracuseStep 2936737 = 2202553) B2202553
theorem B89255843 : Blo 1447543 89255843 := bstep (se 1 (by rfl) ⟨66941882, by rfl⟩ : syracuseStep 89255843 = 133883765) B133883765
theorem B4124591 : Blo 1447543 4124591 := bstep (se 1 (by rfl) ⟨3093443, by rfl⟩ : syracuseStep 4124591 = 6186887) B6186887
theorem B4886459 : Blo 1447543 4886459 := bstep (se 1 (by rfl) ⟨3664844, by rfl⟩ : syracuseStep 4886459 = 7329689) B7329689
theorem B3092411 : Blo 1447543 3092411 := bstep (se 1 (by rfl) ⟨2319308, by rfl⟩ : syracuseStep 3092411 = 4638617) B4638617
theorem B2445275 : Blo 1447543 2445275 := bstep (se 1 (by rfl) ⟨1833956, by rfl⟩ : syracuseStep 2445275 = 3667913) B3667913
theorem B11005955 : Blo 1447543 11005955 := bstep (se 1 (by rfl) ⟨8254466, by rfl⟩ : syracuseStep 11005955 = 16508933) B16508933
theorem B5500943 : Blo 1447543 5500943 := bstep (se 1 (by rfl) ⟨4125707, by rfl⟩ : syracuseStep 5500943 = 8251415) B8251415
theorem B3665999 : Blo 1447543 3665999 := bstep (se 1 (by rfl) ⟨2749499, by rfl⟩ : syracuseStep 3665999 = 5498999) B5498999
theorem B2445511 : Blo 1447543 2445511 := bstep (se 1 (by rfl) ⟨1834133, by rfl⟩ : syracuseStep 2445511 = 3668267) B3668267
theorem B16503101 : Blo 1447543 16503101 := bstep (se 3 (by rfl) ⟨3094331, by rfl⟩ : syracuseStep 16503101 = 6188663) B6188663
theorem B2445673 : Blo 1447543 2445673 := bstep (se 2 (by rfl) ⟨917127, by rfl⟩ : syracuseStep 2445673 = 1834255) B1834255
theorem B4403585 : Blo 1447543 4403585 := bstep (se 2 (by rfl) ⟨1651344, by rfl⟩ : syracuseStep 4403585 = 3302689) B3302689
theorem B3576329 : Blo 1447543 3576329 := bstep (se 2 (by rfl) ⟨1341123, by rfl⟩ : syracuseStep 3576329 = 2682247) B2682247
theorem B3666647 : Blo 1447543 3666647 := bstep (se 1 (by rfl) ⟨2749985, by rfl⟩ : syracuseStep 3666647 = 5499971) B5499971
theorem B3257081 : Blo 1447543 3257081 := bstep (se 2 (by rfl) ⟨1221405, by rfl⟩ : syracuseStep 3257081 = 2442811) B2442811
theorem B12366665 : Blo 1447543 12366665 := bstep (se 2 (by rfl) ⟨4637499, by rfl⟩ : syracuseStep 12366665 = 9274999) B9274999
theorem B3257351 : Blo 1447543 3257351 := bstep (se 1 (by rfl) ⟨2443013, by rfl⟩ : syracuseStep 3257351 = 4886027) B4886027
theorem B7336979 : Blo 1447543 7336979 := bstep (se 1 (by rfl) ⟨5502734, by rfl⟩ : syracuseStep 7336979 = 11005469) B11005469
theorem B27841603 : Blo 1447543 27841603 := bstep (se 1 (by rfl) ⟨20881202, by rfl⟩ : syracuseStep 27841603 = 41762405) B41762405
theorem B3257423 : Blo 1447543 3257423 := bstep (se 1 (by rfl) ⟨2443067, by rfl⟩ : syracuseStep 3257423 = 4886135) B4886135
theorem B3093751 : Blo 1447543 3093751 := bstep (se 1 (by rfl) ⟨2320313, by rfl⟩ : syracuseStep 3093751 = 4640627) B4640627
theorem B2749879 : Blo 1447543 2749879 := bstep (se 1 (by rfl) ⟨2062409, by rfl⟩ : syracuseStep 2749879 = 4124819) B4124819
theorem B2938295 : Blo 1447543 2938295 := bstep (se 1 (by rfl) ⟨2203721, by rfl⟩ : syracuseStep 2938295 = 4407443) B4407443
theorem B3257819 : Blo 1447543 3257819 := bstep (se 1 (by rfl) ⟨2443364, by rfl⟩ : syracuseStep 3257819 = 4886729) B4886729
theorem B4642267 : Blo 1447543 4642267 := bstep (se 1 (by rfl) ⟨3481700, by rfl⟩ : syracuseStep 4642267 = 6963401) B6963401
theorem B18822619 : Blo 1447543 18822619 := bstep (se 1 (by rfl) ⟨14116964, by rfl⟩ : syracuseStep 18822619 = 28233929) B28233929
theorem B1447547 : Blo 1447543 1447547 := bstep (se 1 (by rfl) ⟨1085660, by rfl⟩ : syracuseStep 1447547 = 2171321) B2171321
theorem B4888187 : Blo 1447543 4888187 := bstep (se 1 (by rfl) ⟨3666140, by rfl⟩ : syracuseStep 4888187 = 7332281) B7332281
theorem B5502599 : Blo 1447543 5502599 := bstep (se 1 (by rfl) ⟨4126949, by rfl⟩ : syracuseStep 5502599 = 8253899) B8253899
theorem B1447599 : Blo 1447543 1447599 := bstep (se 1 (by rfl) ⟨1085699, by rfl⟩ : syracuseStep 1447599 = 2171399) B2171399
theorem B1447623 : Blo 1447543 1447623 := bstep (se 1 (by rfl) ⟨1085717, by rfl⟩ : syracuseStep 1447623 = 2171435) B2171435
theorem B1447643 : Blo 1447543 1447643 := bstep (se 1 (by rfl) ⟨1085732, by rfl⟩ : syracuseStep 1447643 = 2171465) B2171465
theorem B9287405 : Blo 1447543 9287405 := bstep (se 3 (by rfl) ⟨1741388, by rfl⟩ : syracuseStep 9287405 = 3482777) B3482777
theorem B4888349 : Blo 1447543 4888349 := bstep (se 3 (by rfl) ⟨916565, by rfl⟩ : syracuseStep 4888349 = 1833131) B1833131
theorem B1447719 : Blo 1447543 1447719 := bstep (se 1 (by rfl) ⟨1085789, by rfl⟩ : syracuseStep 1447719 = 2171579) B2171579
theorem B15669035 : Blo 1447543 15669035 := bstep (se 1 (by rfl) ⟨11751776, by rfl⟩ : syracuseStep 15669035 = 23503553) B23503553
theorem B1447759 : Blo 1447543 1447759 := bstep (se 1 (by rfl) ⟨1085819, by rfl⟩ : syracuseStep 1447759 = 2171639) B2171639
theorem B1447775 : Blo 1447543 1447775 := bstep (se 1 (by rfl) ⟨1085831, by rfl⟩ : syracuseStep 1447775 = 2171663) B2171663
theorem B1447803 : Blo 1447543 1447803 := bstep (se 1 (by rfl) ⟨1085852, by rfl⟩ : syracuseStep 1447803 = 2171705) B2171705
theorem B1447855 : Blo 1447543 1447855 := bstep (se 1 (by rfl) ⟨1085891, by rfl⟩ : syracuseStep 1447855 = 2171783) B2171783
theorem B3258287 : Blo 1447543 3258287 := bstep (se 1 (by rfl) ⟨2443715, by rfl⟩ : syracuseStep 3258287 = 4887431) B4887431
theorem B10442681 : Blo 1447543 10442681 := bstep (se 2 (by rfl) ⟨3916005, by rfl⟩ : syracuseStep 10442681 = 7832011) B7832011
theorem B1447879 : Blo 1447543 1447879 := bstep (se 1 (by rfl) ⟨1085909, by rfl⟩ : syracuseStep 1447879 = 2171819) B2171819
theorem B1447899 : Blo 1447543 1447899 := bstep (se 1 (by rfl) ⟨1085924, by rfl⟩ : syracuseStep 1447899 = 2171849) B2171849
theorem B1447975 : Blo 1447543 1447975 := bstep (se 1 (by rfl) ⟨1085981, by rfl⟩ : syracuseStep 1447975 = 2171963) B2171963
theorem B1448015 : Blo 1447543 1448015 := bstep (se 1 (by rfl) ⟨1086011, by rfl⟩ : syracuseStep 1448015 = 2172023) B2172023
theorem B1448031 : Blo 1447543 1448031 := bstep (se 1 (by rfl) ⟨1086023, by rfl⟩ : syracuseStep 1448031 = 2172047) B2172047
theorem B1448059 : Blo 1447543 1448059 := bstep (se 1 (by rfl) ⟨1086044, by rfl⟩ : syracuseStep 1448059 = 2172089) B2172089
theorem B6191261 : Blo 1447543 6191261 := bstep (se 3 (by rfl) ⟨1160861, by rfl⟩ : syracuseStep 6191261 = 2321723) B2321723
theorem B3258539 : Blo 1447543 3258539 := bstep (se 1 (by rfl) ⟨2443904, by rfl⟩ : syracuseStep 3258539 = 4887809) B4887809
theorem B1448111 : Blo 1447543 1448111 := bstep (se 1 (by rfl) ⟨1086083, by rfl⟩ : syracuseStep 1448111 = 2172167) B2172167
theorem B1448135 : Blo 1447543 1448135 := bstep (se 1 (by rfl) ⟨1086101, by rfl⟩ : syracuseStep 1448135 = 2172203) B2172203
theorem B1448155 : Blo 1447543 1448155 := bstep (se 1 (by rfl) ⟨1086116, by rfl⟩ : syracuseStep 1448155 = 2172233) B2172233
theorem B1448231 : Blo 1447543 1448231 := bstep (se 1 (by rfl) ⟨1086173, by rfl⟩ : syracuseStep 1448231 = 2172347) B2172347
theorem B2611529 : Blo 1447543 2611529 := bstep (se 2 (by rfl) ⟨979323, by rfl⟩ : syracuseStep 2611529 = 1958647) B1958647
theorem B1448271 : Blo 1447543 1448271 := bstep (se 1 (by rfl) ⟨1086203, by rfl⟩ : syracuseStep 1448271 = 2172407) B2172407
theorem B1448287 : Blo 1447543 1448287 := bstep (se 1 (by rfl) ⟨1086215, by rfl⟩ : syracuseStep 1448287 = 2172431) B2172431
theorem B7051625 : Blo 1447543 7051625 := bstep (se 2 (by rfl) ⟨2644359, by rfl⟩ : syracuseStep 7051625 = 5288719) B5288719
theorem B1448315 : Blo 1447543 1448315 := bstep (se 1 (by rfl) ⟨1086236, by rfl⟩ : syracuseStep 1448315 = 2172473) B2172473
theorem B16963991 : Blo 1447543 16963991 := bstep (se 1 (by rfl) ⟨12722993, by rfl⟩ : syracuseStep 16963991 = 25445987) B25445987
theorem B1448367 : Blo 1447543 1448367 := bstep (se 1 (by rfl) ⟨1086275, by rfl⟩ : syracuseStep 1448367 = 2172551) B2172551
theorem B2644411 : Blo 1447543 2644411 := bstep (se 1 (by rfl) ⟨1983308, by rfl⟩ : syracuseStep 2644411 = 3966617) B3966617
theorem B1448391 : Blo 1447543 1448391 := bstep (se 1 (by rfl) ⟨1086293, by rfl⟩ : syracuseStep 1448391 = 2172587) B2172587
theorem B1628635 : Blo 1447543 1628635 := bstep (se 1 (by rfl) ⟨1221476, by rfl⟩ : syracuseStep 1628635 = 2442953) B2442953
theorem B1448411 : Blo 1447543 1448411 := bstep (se 1 (by rfl) ⟨1086308, by rfl⟩ : syracuseStep 1448411 = 2172617) B2172617
theorem B4889051 : Blo 1447543 4889051 := bstep (se 1 (by rfl) ⟨3666788, by rfl⟩ : syracuseStep 4889051 = 7333577) B7333577
theorem B7330337 : Blo 1447543 7330337 := bstep (se 2 (by rfl) ⟨2748876, by rfl⟩ : syracuseStep 7330337 = 5497753) B5497753
theorem B1448487 : Blo 1447543 1448487 := bstep (se 1 (by rfl) ⟨1086365, by rfl⟩ : syracuseStep 1448487 = 2172731) B2172731
theorem B1833511 : Blo 1447543 1833511 := bstep (se 1 (by rfl) ⟨1375133, by rfl⟩ : syracuseStep 1833511 = 2750267) B2750267
theorem B1448527 : Blo 1447543 1448527 := bstep (se 1 (by rfl) ⟨1086395, by rfl⟩ : syracuseStep 1448527 = 2172791) B2172791
theorem B1448543 : Blo 1447543 1448543 := bstep (se 1 (by rfl) ⟨1086407, by rfl⟩ : syracuseStep 1448543 = 2172815) B2172815
theorem B5503585 : Blo 1447543 5503585 := bstep (se 2 (by rfl) ⟨2063844, by rfl⟩ : syracuseStep 5503585 = 4127689) B4127689
theorem B1448571 : Blo 1447543 1448571 := bstep (se 1 (by rfl) ⟨1086428, by rfl⟩ : syracuseStep 1448571 = 2172857) B2172857
theorem B1448623 : Blo 1447543 1448623 := bstep (se 1 (by rfl) ⟨1086467, by rfl⟩ : syracuseStep 1448623 = 2172935) B2172935
theorem B3259079 : Blo 1447543 3259079 := bstep (se 1 (by rfl) ⟨2444309, by rfl⟩ : syracuseStep 3259079 = 4888619) B4888619
theorem B1448647 : Blo 1447543 1448647 := bstep (se 1 (by rfl) ⟨1086485, by rfl⟩ : syracuseStep 1448647 = 2172971) B2172971
theorem B1448667 : Blo 1447543 1448667 := bstep (se 1 (by rfl) ⟨1086500, by rfl⟩ : syracuseStep 1448667 = 2173001) B2173001
theorem B8248067 : Blo 1447543 8248067 := bstep (se 1 (by rfl) ⟨6186050, by rfl⟩ : syracuseStep 8248067 = 12372101) B12372101
theorem B1448743 : Blo 1447543 1448743 := bstep (se 1 (by rfl) ⟨1086557, by rfl⟩ : syracuseStep 1448743 = 2173115) B2173115
theorem B1448783 : Blo 1447543 1448783 := bstep (se 1 (by rfl) ⟨1086587, by rfl⟩ : syracuseStep 1448783 = 2173175) B2173175
theorem B1448799 : Blo 1447543 1448799 := bstep (se 1 (by rfl) ⟨1086599, by rfl⟩ : syracuseStep 1448799 = 2173199) B2173199
theorem B2751337 : Blo 1447543 2751337 := bstep (se 2 (by rfl) ⟨1031751, by rfl⟩ : syracuseStep 2751337 = 2063503) B2063503
theorem B1833835 : Blo 1447543 1833835 := bstep (se 1 (by rfl) ⟨1375376, by rfl⟩ : syracuseStep 1833835 = 2750753) B2750753
theorem B1448827 : Blo 1447543 1448827 := bstep (se 1 (by rfl) ⟨1086620, by rfl⟩ : syracuseStep 1448827 = 2173241) B2173241
theorem B1629103 : Blo 1447543 1629103 := bstep (se 1 (by rfl) ⟨1221827, by rfl⟩ : syracuseStep 1629103 = 2443655) B2443655
theorem B1448879 : Blo 1447543 1448879 := bstep (se 1 (by rfl) ⟨1086659, by rfl⟩ : syracuseStep 1448879 = 2173319) B2173319
theorem B1448903 : Blo 1447543 1448903 := bstep (se 1 (by rfl) ⟨1086677, by rfl⟩ : syracuseStep 1448903 = 2173355) B2173355
theorem B1448923 : Blo 1447543 1448923 := bstep (se 1 (by rfl) ⟨1086692, by rfl⟩ : syracuseStep 1448923 = 2173385) B2173385
theorem B1448999 : Blo 1447543 1448999 := bstep (se 1 (by rfl) ⟨1086749, by rfl⟩ : syracuseStep 1448999 = 2173499) B2173499
theorem B1449039 : Blo 1447543 1449039 := bstep (se 1 (by rfl) ⟨1086779, by rfl⟩ : syracuseStep 1449039 = 2173559) B2173559
theorem B3529807 : Blo 1447543 3529807 := bstep (se 1 (by rfl) ⟨2647355, by rfl⟩ : syracuseStep 3529807 = 5294711) B5294711
theorem B1449055 : Blo 1447543 1449055 := bstep (se 1 (by rfl) ⟨1086791, by rfl⟩ : syracuseStep 1449055 = 2173583) B2173583
theorem B1449083 : Blo 1447543 1449083 := bstep (se 1 (by rfl) ⟨1086812, by rfl⟩ : syracuseStep 1449083 = 2173625) B2173625
theorem B4889753 : Blo 1447543 4889753 := bstep (se 2 (by rfl) ⟨1833657, by rfl⟩ : syracuseStep 4889753 = 3667315) B3667315
theorem B1449135 : Blo 1447543 1449135 := bstep (se 1 (by rfl) ⟨1086851, by rfl⟩ : syracuseStep 1449135 = 2173703) B2173703
theorem B10992833 : Blo 1447543 10992833 := bstep (se 2 (by rfl) ⟨4122312, by rfl⟩ : syracuseStep 10992833 = 8244625) B8244625
theorem B1449159 : Blo 1447543 1449159 := bstep (se 1 (by rfl) ⟨1086869, by rfl⟩ : syracuseStep 1449159 = 2173739) B2173739
theorem B1449179 : Blo 1447543 1449179 := bstep (se 1 (by rfl) ⟨1086884, by rfl⟩ : syracuseStep 1449179 = 2173769) B2173769
theorem B8363255 : Blo 1447543 8363255 := bstep (se 1 (by rfl) ⟨6272441, by rfl⟩ : syracuseStep 8363255 = 12544883) B12544883
theorem B37109015 : Blo 1447543 37109015 := bstep (se 1 (by rfl) ⟨27831761, by rfl⟩ : syracuseStep 37109015 = 55663523) B55663523
theorem B10435877 : Blo 1447543 10435877 := bstep (se 4 (by rfl) ⟨978363, by rfl⟩ : syracuseStep 10435877 = 1956727) B1956727
theorem B1449255 : Blo 1447543 1449255 := bstep (se 1 (by rfl) ⟨1086941, by rfl⟩ : syracuseStep 1449255 = 2173883) B2173883
theorem B1449295 : Blo 1447543 1449295 := bstep (se 1 (by rfl) ⟨1086971, by rfl⟩ : syracuseStep 1449295 = 2173943) B2173943
theorem B1629535 : Blo 1447543 1629535 := bstep (se 1 (by rfl) ⟨1222151, by rfl⟩ : syracuseStep 1629535 = 2444303) B2444303
theorem B1449311 : Blo 1447543 1449311 := bstep (se 1 (by rfl) ⟨1086983, by rfl⟩ : syracuseStep 1449311 = 2173967) B2173967
theorem B1957225 : Blo 1447543 1957225 := bstep (se 2 (by rfl) ⟨733959, by rfl⟩ : syracuseStep 1957225 = 1467919) B1467919
theorem B1449339 : Blo 1447543 1449339 := bstep (se 1 (by rfl) ⟨1087004, by rfl⟩ : syracuseStep 1449339 = 2174009) B2174009
theorem B1449391 : Blo 1447543 1449391 := bstep (se 1 (by rfl) ⟨1087043, by rfl⟩ : syracuseStep 1449391 = 2174087) B2174087
theorem B1449415 : Blo 1447543 1449415 := bstep (se 1 (by rfl) ⟨1087061, by rfl⟩ : syracuseStep 1449415 = 2174123) B2174123
theorem B1449435 : Blo 1447543 1449435 := bstep (se 1 (by rfl) ⟨1087076, by rfl⟩ : syracuseStep 1449435 = 2174153) B2174153
theorem B13573619 : Blo 1447543 13573619 := bstep (se 1 (by rfl) ⟨10180214, by rfl⟩ : syracuseStep 13573619 = 20360429) B20360429
theorem B4406771 : Blo 1447543 4406771 := bstep (se 1 (by rfl) ⟨3305078, by rfl⟩ : syracuseStep 4406771 = 6610157) B6610157
theorem B3259943 : Blo 1447543 3259943 := bstep (se 1 (by rfl) ⟨2444957, by rfl⟩ : syracuseStep 3259943 = 4889915) B4889915
theorem B1449511 : Blo 1447543 1449511 := bstep (se 1 (by rfl) ⟨1087133, by rfl⟩ : syracuseStep 1449511 = 2174267) B2174267
theorem B1629895 : Blo 1447543 1629895 := bstep (se 1 (by rfl) ⟨1222421, by rfl⟩ : syracuseStep 1629895 = 2444843) B2444843
theorem B11001581 : Blo 1447543 11001581 := bstep (se 3 (by rfl) ⟨2062796, by rfl⟩ : syracuseStep 11001581 = 4125593) B4125593
theorem B5496569 : Blo 1447543 5496569 := bstep (se 2 (by rfl) ⟨2061213, by rfl⟩ : syracuseStep 5496569 = 4122427) B4122427
theorem B26418959 : Blo 1447543 26418959 := bstep (se 1 (by rfl) ⟨19814219, by rfl⟩ : syracuseStep 26418959 = 39628439) B39628439
theorem B275029775 : Blo 1447543 275029775 := bstep (se 1 (by rfl) ⟨206272331, by rfl⟩ : syracuseStep 275029775 = 412544663) B412544663
theorem B7831363 : Blo 1447543 7831363 := bstep (se 1 (by rfl) ⟨5873522, by rfl⟩ : syracuseStep 7831363 = 11747045) B11747045
theorem B3260267 : Blo 1447543 3260267 := bstep (se 1 (by rfl) ⟨2445200, by rfl⟩ : syracuseStep 3260267 = 4890401) B4890401
theorem B3260321 : Blo 1447543 3260321 := bstep (se 2 (by rfl) ⟨1222620, by rfl⟩ : syracuseStep 3260321 = 2445241) B2445241
theorem B11002067 : Blo 1447543 11002067 := bstep (se 1 (by rfl) ⟨8251550, by rfl⟩ : syracuseStep 11002067 = 16503101) B16503101
theorem B3260627 : Blo 1447543 3260627 := bstep (se 1 (by rfl) ⟨2445470, by rfl⟩ : syracuseStep 3260627 = 4890941) B4890941
theorem B3260681 : Blo 1447543 3260681 := bstep (se 2 (by rfl) ⟨1222755, by rfl⟩ : syracuseStep 3260681 = 2445511) B2445511
theorem B2384219 : Blo 1447543 2384219 := bstep (se 1 (by rfl) ⟨1788164, by rfl⟩ : syracuseStep 2384219 = 3576329) B3576329
theorem B18825637 : Blo 1447543 18825637 := bstep (se 4 (by rfl) ⟨1764903, by rfl⟩ : syracuseStep 18825637 = 3529807) B3529807
theorem B6603227 : Blo 1447543 6603227 := bstep (se 1 (by rfl) ⟨4952420, by rfl⟩ : syracuseStep 6603227 = 9904841) B9904841
theorem B3260897 : Blo 1447543 3260897 := bstep (se 2 (by rfl) ⟨1222836, by rfl⟩ : syracuseStep 3260897 = 2445673) B2445673
theorem B2171387 : Blo 1447543 2171387 := bstep (se 1 (by rfl) ⟨1628540, by rfl⟩ : syracuseStep 2171387 = 3257081) B3257081
theorem B14860871 : Blo 1447543 14860871 := bstep (se 1 (by rfl) ⟨11145653, by rfl⟩ : syracuseStep 14860871 = 22291307) B22291307
theorem B2171513 : Blo 1447543 2171513 := bstep (se 2 (by rfl) ⟨814317, by rfl⟩ : syracuseStep 2171513 = 1628635) B1628635
theorem B2171567 : Blo 1447543 2171567 := bstep (se 1 (by rfl) ⟨1628675, by rfl⟩ : syracuseStep 2171567 = 3257351) B3257351
theorem B4891319 : Blo 1447543 4891319 := bstep (se 1 (by rfl) ⟨3668489, by rfl⟩ : syracuseStep 4891319 = 7336979) B7336979
theorem B2171615 : Blo 1447543 2171615 := bstep (se 1 (by rfl) ⟨1628711, by rfl⟩ : syracuseStep 2171615 = 3257423) B3257423
theorem B3261203 : Blo 1447543 3261203 := bstep (se 1 (by rfl) ⟨2445902, by rfl⟩ : syracuseStep 3261203 = 4891805) B4891805
theorem B52822853 : Blo 1447543 52822853 := bstep (se 4 (by rfl) ⟨4952142, by rfl⟩ : syracuseStep 52822853 = 9904285) B9904285
theorem B12370765 : Blo 1447543 12370765 := bstep (se 3 (by rfl) ⟨2319518, by rfl⟩ : syracuseStep 12370765 = 4639037) B4639037
theorem B5653327 : Blo 1447543 5653327 := bstep (se 1 (by rfl) ⟨4239995, by rfl⟩ : syracuseStep 5653327 = 8479991) B8479991
theorem B3916687 : Blo 1447543 3916687 := bstep (se 1 (by rfl) ⟨2937515, by rfl⟩ : syracuseStep 3916687 = 5875031) B5875031
theorem B2171879 : Blo 1447543 2171879 := bstep (se 1 (by rfl) ⟨1628909, by rfl⟩ : syracuseStep 2171879 = 3257819) B3257819
theorem B10446023 : Blo 1447543 10446023 := bstep (se 1 (by rfl) ⟨7834517, by rfl⟩ : syracuseStep 10446023 = 15669035) B15669035
theorem B2172137 : Blo 1447543 2172137 := bstep (se 2 (by rfl) ⟨814551, by rfl⟩ : syracuseStep 2172137 = 1629103) B1629103
theorem B2172191 : Blo 1447543 2172191 := bstep (se 1 (by rfl) ⟨1629143, by rfl⟩ : syracuseStep 2172191 = 3258287) B3258287
theorem B2172359 : Blo 1447543 2172359 := bstep (se 1 (by rfl) ⟨1629269, by rfl⟩ : syracuseStep 2172359 = 3258539) B3258539
theorem B2172713 : Blo 1447543 2172713 := bstep (se 2 (by rfl) ⟨814767, by rfl⟩ : syracuseStep 2172713 = 1629535) B1629535
theorem B2172719 : Blo 1447543 2172719 := bstep (se 1 (by rfl) ⟨1629539, by rfl⟩ : syracuseStep 2172719 = 3259079) B3259079
theorem B5498711 : Blo 1447543 5498711 := bstep (se 1 (by rfl) ⟨4124033, by rfl⟩ : syracuseStep 5498711 = 8248067) B8248067
theorem B8358083 : Blo 1447543 8358083 := bstep (se 1 (by rfl) ⟨6268562, by rfl⟩ : syracuseStep 8358083 = 12537125) B12537125
theorem B6957251 : Blo 1447543 6957251 := bstep (se 1 (by rfl) ⟨5217938, by rfl⟩ : syracuseStep 6957251 = 10435877) B10435877
theorem B2173193 : Blo 1447543 2173193 := bstep (se 2 (by rfl) ⟨814947, by rfl⟩ : syracuseStep 2173193 = 1629895) B1629895
theorem B2173295 : Blo 1447543 2173295 := bstep (se 1 (by rfl) ⟨1629971, by rfl⟩ : syracuseStep 2173295 = 3259943) B3259943
theorem B7834067 : Blo 1447543 7834067 := bstep (se 1 (by rfl) ⟨5875550, by rfl⟩ : syracuseStep 7834067 = 11751101) B11751101
theorem B7834085 : Blo 1447543 7834085 := bstep (se 4 (by rfl) ⟨734445, by rfl⟩ : syracuseStep 7834085 = 1468891) B1468891
theorem B7334387 : Blo 1447543 7334387 := bstep (se 1 (by rfl) ⟨5500790, by rfl⟩ : syracuseStep 7334387 = 11001581) B11001581
theorem B3664379 : Blo 1447543 3664379 := bstep (se 1 (by rfl) ⟨2748284, by rfl⟩ : syracuseStep 3664379 = 5496569) B5496569
theorem B4639295 : Blo 1447543 4639295 := bstep (se 1 (by rfl) ⟨3479471, by rfl⟩ : syracuseStep 4639295 = 6958943) B6958943
theorem B2173511 : Blo 1447543 2173511 := bstep (se 1 (by rfl) ⟨1630133, by rfl⟩ : syracuseStep 2173511 = 3260267) B3260267
theorem B2173547 : Blo 1447543 2173547 := bstep (se 1 (by rfl) ⟨1630160, by rfl⟩ : syracuseStep 2173547 = 3260321) B3260321
theorem B2443999 : Blo 1447543 2443999 := bstep (se 1 (by rfl) ⟨1832999, by rfl⟩ : syracuseStep 2443999 = 3665999) B3665999
theorem B6187843 : Blo 1447543 6187843 := bstep (se 1 (by rfl) ⟨4640882, by rfl⟩ : syracuseStep 6187843 = 9281765) B9281765
theorem B2173775 : Blo 1447543 2173775 := bstep (se 1 (by rfl) ⟨1630331, by rfl⟩ : syracuseStep 2173775 = 3260663) B3260663
theorem B7335035 : Blo 1447543 7335035 := bstep (se 1 (by rfl) ⟨5501276, by rfl⟩ : syracuseStep 7335035 = 11002553) B11002553
theorem B2444431 : Blo 1447543 2444431 := bstep (se 1 (by rfl) ⟨1833323, by rfl⟩ : syracuseStep 2444431 = 3666647) B3666647
theorem B8244443 : Blo 1447543 8244443 := bstep (se 1 (by rfl) ⟨6183332, by rfl⟩ : syracuseStep 8244443 = 12366665) B12366665
theorem B2174171 : Blo 1447543 2174171 := bstep (se 1 (by rfl) ⟨1630628, by rfl⟩ : syracuseStep 2174171 = 3261257) B3261257
theorem B3525881 : Blo 1447543 3525881 := bstep (se 2 (by rfl) ⟨1322205, by rfl⟩ : syracuseStep 3525881 = 2644411) B2644411
theorem B22302013 : Blo 1447543 22302013 := bstep (se 3 (by rfl) ⟨4181627, by rfl⟩ : syracuseStep 22302013 = 8363255) B8363255
theorem B10448189 : Blo 1447543 10448189 := bstep (se 3 (by rfl) ⟨1959035, by rfl⟩ : syracuseStep 10448189 = 3918071) B3918071
theorem B8367457 : Blo 1447543 8367457 := bstep (se 2 (by rfl) ⟨3137796, by rfl⟩ : syracuseStep 8367457 = 6275593) B6275593
theorem B2444681 : Blo 1447543 2444681 := bstep (se 2 (by rfl) ⟨916755, by rfl⟩ : syracuseStep 2444681 = 1833511) B1833511
theorem B3665351 : Blo 1447543 3665351 := bstep (se 1 (by rfl) ⟨2749013, by rfl⟩ : syracuseStep 3665351 = 5498027) B5498027
theorem B11742893 : Blo 1447543 11742893 := bstep (se 3 (by rfl) ⟨2201792, by rfl⟩ : syracuseStep 11742893 = 4403585) B4403585
theorem B7335683 : Blo 1447543 7335683 := bstep (se 1 (by rfl) ⟨5501762, by rfl⟩ : syracuseStep 7335683 = 11003525) B11003525
theorem B3092231 : Blo 1447543 3092231 := bstep (se 1 (by rfl) ⟨2319173, by rfl⟩ : syracuseStep 3092231 = 4638347) B4638347
theorem B24743717 : Blo 1447543 24743717 := bstep (se 4 (by rfl) ⟨2319723, by rfl⟩ : syracuseStep 24743717 = 4639447) B4639447
theorem B2445113 : Blo 1447543 2445113 := bstep (se 2 (by rfl) ⟨916917, by rfl⟩ : syracuseStep 2445113 = 1833835) B1833835
theorem B7835453 : Blo 1447543 7835453 := bstep (se 3 (by rfl) ⟨1469147, by rfl⟩ : syracuseStep 7835453 = 2938295) B2938295
theorem B11751389 : Blo 1447543 11751389 := bstep (se 3 (by rfl) ⟨2203385, by rfl⟩ : syracuseStep 11751389 = 4406771) B4406771
theorem B6959155 : Blo 1447543 6959155 := bstep (se 1 (by rfl) ⟨5219366, by rfl⟩ : syracuseStep 6959155 = 10438733) B10438733
theorem B7827515 : Blo 1447543 7827515 := bstep (se 1 (by rfl) ⟨5870636, by rfl⟩ : syracuseStep 7827515 = 11741273) B11741273
theorem B37122137 : Blo 1447543 37122137 := bstep (se 2 (by rfl) ⟨13920801, by rfl⟩ : syracuseStep 37122137 = 27841603) B27841603
theorem B3666131 : Blo 1447543 3666131 := bstep (se 1 (by rfl) ⟨2749598, by rfl⟩ : syracuseStep 3666131 = 5499197) B5499197
theorem B1741019 : Blo 1447543 1741019 := bstep (se 1 (by rfl) ⟨1305764, by rfl⟩ : syracuseStep 1741019 = 2611529) B2611529
theorem B11309327 : Blo 1447543 11309327 := bstep (se 1 (by rfl) ⟨8481995, by rfl⟩ : syracuseStep 11309327 = 16963991) B16963991
theorem B4125001 : Blo 1447543 4125001 := bstep (se 2 (by rfl) ⟨1546875, by rfl⟩ : syracuseStep 4125001 = 3093751) B3093751
theorem B4886891 : Blo 1447543 4886891 := bstep (se 1 (by rfl) ⟨3665168, by rfl⟩ : syracuseStep 4886891 = 7330337) B7330337
theorem B3666343 : Blo 1447543 3666343 := bstep (se 1 (by rfl) ⟨2749757, by rfl⟩ : syracuseStep 3666343 = 5499515) B5499515
theorem B2609633 : Blo 1447543 2609633 := bstep (se 2 (by rfl) ⟨978612, by rfl⟩ : syracuseStep 2609633 = 1957225) B1957225
theorem B5501459 : Blo 1447543 5501459 := bstep (se 1 (by rfl) ⟨4126094, by rfl⟩ : syracuseStep 5501459 = 8252189) B8252189
theorem B15872561 : Blo 1447543 15872561 := bstep (se 2 (by rfl) ⟨5952210, by rfl⟩ : syracuseStep 15872561 = 11904421) B11904421
theorem B2748991 : Blo 1447543 2748991 := bstep (se 1 (by rfl) ⟨2061743, by rfl⟩ : syracuseStep 2748991 = 4123487) B4123487
theorem B3666505 : Blo 1447543 3666505 := bstep (se 2 (by rfl) ⟨1374939, by rfl⟩ : syracuseStep 3666505 = 2749879) B2749879
theorem B4887161 : Blo 1447543 4887161 := bstep (se 2 (by rfl) ⟨1832685, by rfl⟩ : syracuseStep 4887161 = 3665371) B3665371
theorem B6189689 : Blo 1447543 6189689 := bstep (se 2 (by rfl) ⟨2321133, by rfl⟩ : syracuseStep 6189689 = 4642267) B4642267
theorem B25096825 : Blo 1447543 25096825 := bstep (se 2 (by rfl) ⟨9411309, by rfl⟩ : syracuseStep 25096825 = 18822619) B18822619
theorem B7328555 : Blo 1447543 7328555 := bstep (se 1 (by rfl) ⟨5496416, by rfl⟩ : syracuseStep 7328555 = 10992833) B10992833
theorem B3257243 : Blo 1447543 3257243 := bstep (se 1 (by rfl) ⟨2442932, by rfl⟩ : syracuseStep 3257243 = 4885865) B4885865
theorem B1651663 : Blo 1447543 1651663 := bstep (se 1 (by rfl) ⟨1238747, by rfl⟩ : syracuseStep 1651663 = 2477495) B2477495
theorem B5501915 : Blo 1447543 5501915 := bstep (se 1 (by rfl) ⟨4126436, by rfl⟩ : syracuseStep 5501915 = 8252873) B8252873
theorem B9049079 : Blo 1447543 9049079 := bstep (se 1 (by rfl) ⟨6786809, by rfl⟩ : syracuseStep 9049079 = 13573619) B13573619
theorem B10441817 : Blo 1447543 10441817 := bstep (se 2 (by rfl) ⟨3915681, by rfl⟩ : syracuseStep 10441817 = 7831363) B7831363
theorem B3257441 : Blo 1447543 3257441 := bstep (se 2 (by rfl) ⟨1221540, by rfl⟩ : syracuseStep 3257441 = 2443081) B2443081
theorem B59503895 : Blo 1447543 59503895 := bstep (se 1 (by rfl) ⟨44627921, by rfl⟩ : syracuseStep 59503895 = 89255843) B89255843
theorem B2749727 : Blo 1447543 2749727 := bstep (se 1 (by rfl) ⟨2062295, by rfl⟩ : syracuseStep 2749727 = 4124591) B4124591
theorem B3257639 : Blo 1447543 3257639 := bstep (se 1 (by rfl) ⟨2443229, by rfl⟩ : syracuseStep 3257639 = 4886459) B4886459
theorem B2061607 : Blo 1447543 2061607 := bstep (se 1 (by rfl) ⟨1546205, by rfl⟩ : syracuseStep 2061607 = 3092411) B3092411
theorem B7337303 : Blo 1447543 7337303 := bstep (se 1 (by rfl) ⟨5502977, by rfl⟩ : syracuseStep 7337303 = 11005955) B11005955
theorem B3667295 : Blo 1447543 3667295 := bstep (se 1 (by rfl) ⟨2750471, by rfl⟩ : syracuseStep 3667295 = 5500943) B5500943
theorem B3258017 : Blo 1447543 3258017 := bstep (se 2 (by rfl) ⟨1221756, by rfl⟩ : syracuseStep 3258017 = 2443513) B2443513
theorem B1447647 : Blo 1447543 1447647 := bstep (se 1 (by rfl) ⟨1085735, by rfl⟩ : syracuseStep 1447647 = 2171471) B2171471
theorem B1447727 : Blo 1447543 1447727 := bstep (se 1 (by rfl) ⟨1085795, by rfl⟩ : syracuseStep 1447727 = 2171591) B2171591
theorem B1447835 : Blo 1447543 1447835 := bstep (se 1 (by rfl) ⟨1085876, by rfl⟩ : syracuseStep 1447835 = 2171753) B2171753
theorem B1447887 : Blo 1447543 1447887 := bstep (se 1 (by rfl) ⟨1085915, by rfl⟩ : syracuseStep 1447887 = 2171831) B2171831
theorem B1447911 : Blo 1447543 1447911 := bstep (se 1 (by rfl) ⟨1085933, by rfl⟩ : syracuseStep 1447911 = 2171867) B2171867
theorem B3258377 : Blo 1447543 3258377 := bstep (se 2 (by rfl) ⟨1221891, by rfl⟩ : syracuseStep 3258377 = 2443783) B2443783
theorem B3094537 : Blo 1447543 3094537 := bstep (se 2 (by rfl) ⟨1160451, by rfl⟩ : syracuseStep 3094537 = 2320903) B2320903
theorem B12376097 : Blo 1447543 12376097 := bstep (se 2 (by rfl) ⟨4641036, by rfl⟩ : syracuseStep 12376097 = 9282073) B9282073
theorem B7338113 : Blo 1447543 7338113 := bstep (se 2 (by rfl) ⟨2751792, by rfl⟩ : syracuseStep 7338113 = 5503585) B5503585
theorem B1448223 : Blo 1447543 1448223 := bstep (se 1 (by rfl) ⟨1086167, by rfl⟩ : syracuseStep 1448223 = 2172335) B2172335
theorem B1448283 : Blo 1447543 1448283 := bstep (se 1 (by rfl) ⟨1086212, by rfl⟩ : syracuseStep 1448283 = 2172425) B2172425
theorem B1628527 : Blo 1447543 1628527 := bstep (se 1 (by rfl) ⟨1221395, by rfl⟩ : syracuseStep 1628527 = 2442791) B2442791
theorem B1448303 : Blo 1447543 1448303 := bstep (se 1 (by rfl) ⟨1086227, by rfl⟩ : syracuseStep 1448303 = 2172455) B2172455
theorem B4888943 : Blo 1447543 4888943 := bstep (se 1 (by rfl) ⟨3666707, by rfl⟩ : syracuseStep 4888943 = 7333415) B7333415
theorem B1546619 : Blo 1447543 1546619 := bstep (se 1 (by rfl) ⟨1159964, by rfl⟩ : syracuseStep 1546619 = 2319929) B2319929
theorem B2202023 : Blo 1447543 2202023 := bstep (se 1 (by rfl) ⟨1651517, by rfl⟩ : syracuseStep 2202023 = 3303035) B3303035
theorem B3258791 : Blo 1447543 3258791 := bstep (se 1 (by rfl) ⟨2444093, by rfl⟩ : syracuseStep 3258791 = 4888187) B4888187
theorem B1448359 : Blo 1447543 1448359 := bstep (se 1 (by rfl) ⟨1086269, by rfl⟩ : syracuseStep 1448359 = 2172539) B2172539
theorem B3668399 : Blo 1447543 3668399 := bstep (se 1 (by rfl) ⟨2751299, by rfl⟩ : syracuseStep 3668399 = 5502599) B5502599
theorem B3668449 : Blo 1447543 3668449 := bstep (se 2 (by rfl) ⟨1375668, by rfl⟩ : syracuseStep 3668449 = 2751337) B2751337
theorem B6191603 : Blo 1447543 6191603 := bstep (se 1 (by rfl) ⟨4643702, by rfl⟩ : syracuseStep 6191603 = 9287405) B9287405
theorem B1448443 : Blo 1447543 1448443 := bstep (se 1 (by rfl) ⟨1086332, by rfl⟩ : syracuseStep 1448443 = 2172665) B2172665
theorem B3258899 : Blo 1447543 3258899 := bstep (se 1 (by rfl) ⟨2444174, by rfl⟩ : syracuseStep 3258899 = 4888349) B4888349
theorem B1448511 : Blo 1447543 1448511 := bstep (se 1 (by rfl) ⟨1086383, by rfl⟩ : syracuseStep 1448511 = 2172767) B2172767
theorem B1628743 : Blo 1447543 1628743 := bstep (se 1 (by rfl) ⟨1221557, by rfl⟩ : syracuseStep 1628743 = 2443115) B2443115
theorem B1448519 : Blo 1447543 1448519 := bstep (se 1 (by rfl) ⟨1086389, by rfl⟩ : syracuseStep 1448519 = 2172779) B2172779
theorem B3258953 : Blo 1447543 3258953 := bstep (se 2 (by rfl) ⟨1222107, by rfl⟩ : syracuseStep 3258953 = 2444215) B2444215
theorem B25090667 : Blo 1447543 25090667 := bstep (se 1 (by rfl) ⟨18818000, by rfl⟩ : syracuseStep 25090667 = 37636001) B37636001
theorem B6961787 : Blo 1447543 6961787 := bstep (se 1 (by rfl) ⟨5221340, by rfl⟩ : syracuseStep 6961787 = 10442681) B10442681
theorem B84679343 : Blo 1447543 84679343 := bstep (se 1 (by rfl) ⟨63509507, by rfl⟩ : syracuseStep 84679343 = 127019015) B127019015
theorem B7330499 : Blo 1447543 7330499 := bstep (se 1 (by rfl) ⟨5497874, by rfl⟩ : syracuseStep 7330499 = 10995749) B10995749
theorem B1448671 : Blo 1447543 1448671 := bstep (se 1 (by rfl) ⟨1086503, by rfl⟩ : syracuseStep 1448671 = 2173007) B2173007
theorem B4127507 : Blo 1447543 4127507 := bstep (se 1 (by rfl) ⟨3095630, by rfl⟩ : syracuseStep 4127507 = 6191261) B6191261
theorem B1448751 : Blo 1447543 1448751 := bstep (se 1 (by rfl) ⟨1086563, by rfl⟩ : syracuseStep 1448751 = 2173127) B2173127
theorem B4701083 : Blo 1447543 4701083 := bstep (se 1 (by rfl) ⟨3525812, by rfl⟩ : syracuseStep 4701083 = 7051625) B7051625
theorem B1448859 : Blo 1447543 1448859 := bstep (se 1 (by rfl) ⟨1086644, by rfl⟩ : syracuseStep 1448859 = 2173289) B2173289
theorem B1448911 : Blo 1447543 1448911 := bstep (se 1 (by rfl) ⟨1086683, by rfl⟩ : syracuseStep 1448911 = 2173367) B2173367
theorem B3259367 : Blo 1447543 3259367 := bstep (se 1 (by rfl) ⟨2444525, by rfl⟩ : syracuseStep 3259367 = 4889051) B4889051
theorem B1448935 : Blo 1447543 1448935 := bstep (se 1 (by rfl) ⟨1086701, by rfl⟩ : syracuseStep 1448935 = 2173403) B2173403
theorem B31743197 : Blo 1447543 31743197 := bstep (se 3 (by rfl) ⟨5951849, by rfl⟩ : syracuseStep 31743197 = 11903699) B11903699
theorem B12369125 : Blo 1447543 12369125 := bstep (se 4 (by rfl) ⟨1159605, by rfl⟩ : syracuseStep 12369125 = 2319211) B2319211
theorem B1449247 : Blo 1447543 1449247 := bstep (se 1 (by rfl) ⟨1086935, by rfl⟩ : syracuseStep 1449247 = 2173871) B2173871
theorem B1449307 : Blo 1447543 1449307 := bstep (se 1 (by rfl) ⟨1086980, by rfl⟩ : syracuseStep 1449307 = 2173961) B2173961
theorem B6184289 : Blo 1447543 6184289 := bstep (se 2 (by rfl) ⟨2319108, by rfl⟩ : syracuseStep 6184289 = 4638217) B4638217
theorem B3259745 : Blo 1447543 3259745 := bstep (se 2 (by rfl) ⟨1222404, by rfl⟩ : syracuseStep 3259745 = 2444809) B2444809
theorem B1449327 : Blo 1447543 1449327 := bstep (se 1 (by rfl) ⟨1086995, by rfl⟩ : syracuseStep 1449327 = 2173991) B2173991
theorem B1629607 : Blo 1447543 1629607 := bstep (se 1 (by rfl) ⟨1222205, by rfl⟩ : syracuseStep 1629607 = 2444411) B2444411
theorem B1449383 : Blo 1447543 1449383 := bstep (se 1 (by rfl) ⟨1087037, by rfl⟩ : syracuseStep 1449383 = 2174075) B2174075
theorem B3259835 : Blo 1447543 3259835 := bstep (se 1 (by rfl) ⟨2444876, by rfl⟩ : syracuseStep 3259835 = 4889753) B4889753
theorem B5578183 : Blo 1447543 5578183 := bstep (se 1 (by rfl) ⟨4183637, by rfl⟩ : syracuseStep 5578183 = 8367275) B8367275
theorem B1449467 : Blo 1447543 1449467 := bstep (se 1 (by rfl) ⟨1087100, by rfl⟩ : syracuseStep 1449467 = 2174201) B2174201
theorem B24739343 : Blo 1447543 24739343 := bstep (se 1 (by rfl) ⟨18554507, by rfl⟩ : syracuseStep 24739343 = 37109015) B37109015
theorem B6610447 : Blo 1447543 6610447 := bstep (se 1 (by rfl) ⟨4957835, by rfl⟩ : syracuseStep 6610447 = 9915671) B9915671
theorem B3259961 : Blo 1447543 3259961 := bstep (se 2 (by rfl) ⟨1222485, by rfl⟩ : syracuseStep 3259961 = 2444971) B2444971
theorem B1449535 : Blo 1447543 1449535 := bstep (se 1 (by rfl) ⟨1087151, by rfl⟩ : syracuseStep 1449535 = 2174303) B2174303
theorem B1449543 : Blo 1447543 1449543 := bstep (se 1 (by rfl) ⟨1087157, by rfl⟩ : syracuseStep 1449543 = 2174315) B2174315
theorem B4890347 : Blo 1447543 4890347 := bstep (se 1 (by rfl) ⟨3667760, by rfl⟩ : syracuseStep 4890347 = 7335521) B7335521
theorem B17612639 : Blo 1447543 17612639 := bstep (se 1 (by rfl) ⟨13209479, by rfl⟩ : syracuseStep 17612639 = 26418959) B26418959
theorem B183353183 : Blo 1447543 183353183 := bstep (se 1 (by rfl) ⟨137514887, by rfl⟩ : syracuseStep 183353183 = 275029775) B275029775
theorem B3915649 : Blo 1447543 3915649 := bstep (se 2 (by rfl) ⟨1468368, by rfl⟩ : syracuseStep 3915649 = 2936737) B2936737
theorem B1630183 : Blo 1447543 1630183 := bstep (se 1 (by rfl) ⟨1222637, by rfl⟩ : syracuseStep 1630183 = 2445275) B2445275
theorem B5218343 : Blo 1447543 5218343 := bstep (se 1 (by rfl) ⟨3913757, by rfl⟩ : syracuseStep 5218343 = 7827515) B7827515
theorem B24748091 : Blo 1447543 24748091 := bstep (se 1 (by rfl) ⟨18561068, by rfl⟩ : syracuseStep 24748091 = 37122137) B37122137
theorem B3260879 : Blo 1447543 3260879 := bstep (se 1 (by rfl) ⟨2445659, by rfl⟩ : syracuseStep 3260879 = 4891319) B4891319
theorem B2171369 : Blo 1447543 2171369 := bstep (se 2 (by rfl) ⟨814263, by rfl⟩ : syracuseStep 2171369 = 1628527) B1628527
theorem B25100849 : Blo 1447543 25100849 := bstep (se 2 (by rfl) ⟨9412818, by rfl⟩ : syracuseStep 25100849 = 18825637) B18825637
theorem B2171495 : Blo 1447543 2171495 := bstep (se 1 (by rfl) ⟨1628621, by rfl⟩ : syracuseStep 2171495 = 3257243) B3257243
theorem B4891265 : Blo 1447543 4891265 := bstep (se 2 (by rfl) ⟨1834224, by rfl⟩ : syracuseStep 4891265 = 3668449) B3668449
theorem B2171627 : Blo 1447543 2171627 := bstep (se 1 (by rfl) ⟨1628720, by rfl⟩ : syracuseStep 2171627 = 3257441) B3257441
theorem B7332605 : Blo 1447543 7332605 := bstep (se 3 (by rfl) ⟨1374863, by rfl⟩ : syracuseStep 7332605 = 2749727) B2749727
theorem B2171657 : Blo 1447543 2171657 := bstep (se 2 (by rfl) ⟨814371, by rfl⟩ : syracuseStep 2171657 = 1628743) B1628743
theorem B2171759 : Blo 1447543 2171759 := bstep (se 1 (by rfl) ⟨1628819, by rfl⟩ : syracuseStep 2171759 = 3257639) B3257639
theorem B4891535 : Blo 1447543 4891535 := bstep (se 1 (by rfl) ⟨3668651, by rfl⟩ : syracuseStep 4891535 = 7337303) B7337303
theorem B6357917 : Blo 1447543 6357917 := bstep (se 3 (by rfl) ⟨1192109, by rfl⟩ : syracuseStep 6357917 = 2384219) B2384219
theorem B16491437 : Blo 1447543 16491437 := bstep (se 3 (by rfl) ⟨3092144, by rfl⟩ : syracuseStep 16491437 = 6184289) B6184289
theorem B8250457 : Blo 1447543 8250457 := bstep (se 2 (by rfl) ⟨3093921, by rfl⟩ : syracuseStep 8250457 = 6187843) B6187843
theorem B7537769 : Blo 1447543 7537769 := bstep (se 2 (by rfl) ⟨2826663, by rfl⟩ : syracuseStep 7537769 = 5653327) B5653327
theorem B2172011 : Blo 1447543 2172011 := bstep (se 1 (by rfl) ⟨1629008, by rfl⟩ : syracuseStep 2172011 = 3258017) B3258017
theorem B2172251 : Blo 1447543 2172251 := bstep (se 1 (by rfl) ⟨1629188, by rfl⟩ : syracuseStep 2172251 = 3258377) B3258377
theorem B8250731 : Blo 1447543 8250731 := bstep (se 1 (by rfl) ⟨6188048, by rfl⟩ : syracuseStep 8250731 = 12376097) B12376097
theorem B4892075 : Blo 1447543 4892075 := bstep (se 1 (by rfl) ⟨3669056, by rfl⟩ : syracuseStep 4892075 = 7338113) B7338113
theorem B5572055 : Blo 1447543 5572055 := bstep (se 1 (by rfl) ⟨4179041, by rfl⟩ : syracuseStep 5572055 = 8358083) B8358083
theorem B4638167 : Blo 1447543 4638167 := bstep (se 1 (by rfl) ⟨3478625, by rfl⟩ : syracuseStep 4638167 = 6957251) B6957251
theorem B2172527 : Blo 1447543 2172527 := bstep (se 1 (by rfl) ⟨1629395, by rfl⟩ : syracuseStep 2172527 = 3258791) B3258791
theorem B2442919 : Blo 1447543 2442919 := bstep (se 1 (by rfl) ⟨1832189, by rfl⟩ : syracuseStep 2442919 = 3664379) B3664379
theorem B2172599 : Blo 1447543 2172599 := bstep (se 1 (by rfl) ⟨1629449, by rfl⟩ : syracuseStep 2172599 = 3258899) B3258899
theorem B2172635 : Blo 1447543 2172635 := bstep (se 1 (by rfl) ⟨1629476, by rfl⟩ : syracuseStep 2172635 = 3258953) B3258953
theorem B56452895 : Blo 1447543 56452895 := bstep (se 1 (by rfl) ⟨42339671, by rfl⟩ : syracuseStep 56452895 = 84679343) B84679343
theorem B2172809 : Blo 1447543 2172809 := bstep (se 2 (by rfl) ⟨814803, by rfl⟩ : syracuseStep 2172809 = 1629607) B1629607
theorem B2172911 : Blo 1447543 2172911 := bstep (se 1 (by rfl) ⟨1629683, by rfl⟩ : syracuseStep 2172911 = 3259367) B3259367
theorem B21162131 : Blo 1447543 21162131 := bstep (se 1 (by rfl) ⟨15871598, by rfl⟩ : syracuseStep 21162131 = 31743197) B31743197
theorem B6965459 : Blo 1447543 6965459 := bstep (se 1 (by rfl) ⟨5224094, by rfl⟩ : syracuseStep 6965459 = 10448189) B10448189
theorem B2173163 : Blo 1447543 2173163 := bstep (se 1 (by rfl) ⟨1629872, by rfl⟩ : syracuseStep 2173163 = 3259745) B3259745
theorem B2173223 : Blo 1447543 2173223 := bstep (se 1 (by rfl) ⟨1629917, by rfl⟩ : syracuseStep 2173223 = 3259835) B3259835
theorem B2443567 : Blo 1447543 2443567 := bstep (se 1 (by rfl) ⟨1832675, by rfl⟩ : syracuseStep 2443567 = 3665351) B3665351
theorem B16492895 : Blo 1447543 16492895 := bstep (se 1 (by rfl) ⟨12369671, by rfl⟩ : syracuseStep 16492895 = 24739343) B24739343
theorem B2173307 : Blo 1447543 2173307 := bstep (se 1 (by rfl) ⟨1629980, by rfl⟩ : syracuseStep 2173307 = 3259961) B3259961
theorem B12536221 : Blo 1447543 12536221 := bstep (se 3 (by rfl) ⟨2350541, by rfl⟩ : syracuseStep 12536221 = 4701083) B4701083
theorem B8808869 : Blo 1447543 8808869 := bstep (se 4 (by rfl) ⟨825831, by rfl⟩ : syracuseStep 8808869 = 1651663) B1651663
theorem B5220865 : Blo 1447543 5220865 := bstep (se 2 (by rfl) ⟨1957824, by rfl⟩ : syracuseStep 5220865 = 3915649) B3915649
theorem B11741759 : Blo 1447543 11741759 := bstep (se 1 (by rfl) ⟨8806319, by rfl⟩ : syracuseStep 11741759 = 17612639) B17612639
theorem B122235455 : Blo 1447543 122235455 := bstep (se 1 (by rfl) ⟨91676591, by rfl⟩ : syracuseStep 122235455 = 183353183) B183353183
theorem B2173577 : Blo 1447543 2173577 := bstep (se 2 (by rfl) ⟨815091, by rfl⟩ : syracuseStep 2173577 = 1630183) B1630183
theorem B7834259 : Blo 1447543 7834259 := bstep (se 1 (by rfl) ⟨5875694, by rfl⟩ : syracuseStep 7834259 = 11751389) B11751389
theorem B2444087 : Blo 1447543 2444087 := bstep (se 1 (by rfl) ⟨1833065, by rfl⟩ : syracuseStep 2444087 = 3666131) B3666131
theorem B7334711 : Blo 1447543 7334711 := bstep (se 1 (by rfl) ⟨5501033, by rfl⟩ : syracuseStep 7334711 = 11002067) B11002067
theorem B2173751 : Blo 1447543 2173751 := bstep (se 1 (by rfl) ⟨1630313, by rfl⟩ : syracuseStep 2173751 = 3260627) B3260627
theorem B2173787 : Blo 1447543 2173787 := bstep (se 1 (by rfl) ⟨1630340, by rfl⟩ : syracuseStep 2173787 = 3260681) B3260681
theorem B7539551 : Blo 1447543 7539551 := bstep (se 1 (by rfl) ⟨5654663, by rfl⟩ : syracuseStep 7539551 = 11309327) B11309327
theorem B4402151 : Blo 1447543 4402151 := bstep (se 1 (by rfl) ⟨3301613, by rfl⟩ : syracuseStep 4402151 = 6603227) B6603227
theorem B1739755 : Blo 1447543 1739755 := bstep (se 1 (by rfl) ⟨1304816, by rfl⟩ : syracuseStep 1739755 = 2609633) B2609633
theorem B2173931 : Blo 1447543 2173931 := bstep (se 1 (by rfl) ⟨1630448, by rfl⟩ : syracuseStep 2173931 = 3260897) B3260897
theorem B9907247 : Blo 1447543 9907247 := bstep (se 1 (by rfl) ⟨7430435, by rfl⟩ : syracuseStep 9907247 = 14860871) B14860871
theorem B5500001 : Blo 1447543 5500001 := bstep (se 2 (by rfl) ⟨2062500, by rfl⟩ : syracuseStep 5500001 = 4125001) B4125001
theorem B2174135 : Blo 1447543 2174135 := bstep (se 1 (by rfl) ⟨1630601, by rfl⟩ : syracuseStep 2174135 = 3261203) B3261203
theorem B27856061 : Blo 1447543 27856061 := bstep (se 3 (by rfl) ⟨5223011, by rfl⟩ : syracuseStep 27856061 = 10446023) B10446023
theorem B4885703 : Blo 1447543 4885703 := bstep (se 1 (by rfl) ⟨3664277, by rfl⟩ : syracuseStep 4885703 = 7328555) B7328555
theorem B6032719 : Blo 1447543 6032719 := bstep (se 1 (by rfl) ⟨4524539, by rfl⟩ : syracuseStep 6032719 = 9049079) B9049079
theorem B3665321 : Blo 1447543 3665321 := bstep (se 2 (by rfl) ⟨1374495, by rfl⟩ : syracuseStep 3665321 = 2748991) B2748991
theorem B39669263 : Blo 1447543 39669263 := bstep (se 1 (by rfl) ⟨29751947, by rfl⟩ : syracuseStep 39669263 = 59503895) B59503895
theorem B2444863 : Blo 1447543 2444863 := bstep (se 1 (by rfl) ⟨1833647, by rfl⟩ : syracuseStep 2444863 = 3667295) B3667295
theorem B16494353 : Blo 1447543 16494353 := bstep (se 2 (by rfl) ⟨6185382, by rfl⟩ : syracuseStep 16494353 = 12370765) B12370765
theorem B5222249 : Blo 1447543 5222249 := bstep (se 2 (by rfl) ⟨1958343, by rfl⟩ : syracuseStep 5222249 = 3916687) B3916687
theorem B3665807 : Blo 1447543 3665807 := bstep (se 1 (by rfl) ⟨2749355, by rfl⟩ : syracuseStep 3665807 = 5498711) B5498711
theorem B2445599 : Blo 1447543 2445599 := bstep (se 1 (by rfl) ⟨1834199, by rfl⟩ : syracuseStep 2445599 = 3668399) B3668399
theorem B5222711 : Blo 1447543 5222711 := bstep (se 1 (by rfl) ⟨3917033, by rfl⟩ : syracuseStep 5222711 = 7834067) B7834067
theorem B5222723 : Blo 1447543 5222723 := bstep (se 1 (by rfl) ⟨3917042, by rfl⟩ : syracuseStep 5222723 = 7834085) B7834085
theorem B3092863 : Blo 1447543 3092863 := bstep (se 1 (by rfl) ⟨2319647, by rfl⟩ : syracuseStep 3092863 = 4639295) B4639295
theorem B2748809 : Blo 1447543 2748809 := bstep (se 2 (by rfl) ⟨1030803, by rfl⟩ : syracuseStep 2748809 = 2061607) B2061607
theorem B4641191 : Blo 1447543 4641191 := bstep (se 1 (by rfl) ⟨3480893, by rfl⟩ : syracuseStep 4641191 = 6961787) B6961787
theorem B4886999 : Blo 1447543 4886999 := bstep (se 1 (by rfl) ⟨3665249, by rfl⟩ : syracuseStep 4886999 = 7330499) B7330499
theorem B8246083 : Blo 1447543 8246083 := bstep (se 1 (by rfl) ⟨6184562, by rfl⟩ : syracuseStep 8246083 = 12369125) B12369125
theorem B7828595 : Blo 1447543 7828595 := bstep (se 1 (by rfl) ⟨5871446, by rfl⟩ : syracuseStep 7828595 = 11742893) B11742893
theorem B2061487 : Blo 1447543 2061487 := bstep (se 1 (by rfl) ⟨1546115, by rfl⟩ : syracuseStep 2061487 = 3092231) B3092231
theorem B16495811 : Blo 1447543 16495811 := bstep (se 1 (by rfl) ⟨12371858, by rfl⟩ : syracuseStep 16495811 = 24743717) B24743717
theorem B5223635 : Blo 1447543 5223635 := bstep (se 1 (by rfl) ⟨3917726, by rfl⟩ : syracuseStep 5223635 = 7835453) B7835453
theorem B4126049 : Blo 1447543 4126049 := bstep (se 2 (by rfl) ⟨1547268, by rfl⟩ : syracuseStep 4126049 = 3094537) B3094537
theorem B9278873 : Blo 1447543 9278873 := bstep (se 2 (by rfl) ⟨3479577, by rfl⟩ : syracuseStep 9278873 = 6959155) B6959155
theorem B3257927 : Blo 1447543 3257927 := bstep (se 1 (by rfl) ⟨2443445, by rfl⟩ : syracuseStep 3257927 = 4886891) B4886891
theorem B1447591 : Blo 1447543 1447591 := bstep (se 1 (by rfl) ⟨1085693, by rfl⟩ : syracuseStep 1447591 = 2171387) B2171387
theorem B3667639 : Blo 1447543 3667639 := bstep (se 1 (by rfl) ⟨2750729, by rfl⟩ : syracuseStep 3667639 = 5501459) B5501459
theorem B10581707 : Blo 1447543 10581707 := bstep (se 1 (by rfl) ⟨7936280, by rfl⟩ : syracuseStep 10581707 = 15872561) B15872561
theorem B1447675 : Blo 1447543 1447675 := bstep (se 1 (by rfl) ⟨1085756, by rfl⟩ : syracuseStep 1447675 = 2171513) B2171513
theorem B3258107 : Blo 1447543 3258107 := bstep (se 1 (by rfl) ⟨2443580, by rfl⟩ : syracuseStep 3258107 = 4887161) B4887161
theorem B4126459 : Blo 1447543 4126459 := bstep (se 1 (by rfl) ⟨3094844, by rfl⟩ : syracuseStep 4126459 = 6189689) B6189689
theorem B1447711 : Blo 1447543 1447711 := bstep (se 1 (by rfl) ⟨1085783, by rfl⟩ : syracuseStep 1447711 = 2171567) B2171567
theorem B1447743 : Blo 1447543 1447743 := bstep (se 1 (by rfl) ⟨1085807, by rfl⟩ : syracuseStep 1447743 = 2171615) B2171615
theorem B35215235 : Blo 1447543 35215235 := bstep (se 1 (by rfl) ⟨26411426, by rfl⟩ : syracuseStep 35215235 = 52822853) B52822853
theorem B4888457 : Blo 1447543 4888457 := bstep (se 2 (by rfl) ⟨1833171, by rfl⟩ : syracuseStep 4888457 = 3666343) B3666343
theorem B4642717 : Blo 1447543 4642717 := bstep (se 3 (by rfl) ⟨870509, by rfl⟩ : syracuseStep 4642717 = 1741019) B1741019
theorem B3667943 : Blo 1447543 3667943 := bstep (se 1 (by rfl) ⟨2750957, by rfl⟩ : syracuseStep 3667943 = 5501915) B5501915
theorem B9402349 : Blo 1447543 9402349 := bstep (se 3 (by rfl) ⟨1762940, by rfl⟩ : syracuseStep 9402349 = 3525881) B3525881
theorem B1447919 : Blo 1447543 1447919 := bstep (se 1 (by rfl) ⟨1085939, by rfl⟩ : syracuseStep 1447919 = 2171879) B2171879
theorem B6961211 : Blo 1447543 6961211 := bstep (se 1 (by rfl) ⟨5220908, by rfl⟩ : syracuseStep 6961211 = 10441817) B10441817
theorem B4888673 : Blo 1447543 4888673 := bstep (se 2 (by rfl) ⟨1833252, by rfl⟩ : syracuseStep 4888673 = 3666505) B3666505
theorem B1448091 : Blo 1447543 1448091 := bstep (se 1 (by rfl) ⟨1086068, by rfl⟩ : syracuseStep 1448091 = 2172137) B2172137
theorem B33462433 : Blo 1447543 33462433 := bstep (se 2 (by rfl) ⟨12548412, by rfl⟩ : syracuseStep 33462433 = 25096825) B25096825
theorem B1448127 : Blo 1447543 1448127 := bstep (se 1 (by rfl) ⟨1086095, by rfl⟩ : syracuseStep 1448127 = 2172191) B2172191
theorem B3258665 : Blo 1447543 3258665 := bstep (se 2 (by rfl) ⟨1221999, by rfl⟩ : syracuseStep 3258665 = 2443999) B2443999
theorem B1448239 : Blo 1447543 1448239 := bstep (se 1 (by rfl) ⟨1086179, by rfl⟩ : syracuseStep 1448239 = 2172359) B2172359
theorem B5872061 : Blo 1447543 5872061 := bstep (se 3 (by rfl) ⟨1101011, by rfl⟩ : syracuseStep 5872061 = 2202023) B2202023
theorem B1448475 : Blo 1447543 1448475 := bstep (se 1 (by rfl) ⟨1086356, by rfl⟩ : syracuseStep 1448475 = 2172713) B2172713
theorem B1448479 : Blo 1447543 1448479 := bstep (se 1 (by rfl) ⟨1086359, by rfl⟩ : syracuseStep 1448479 = 2172719) B2172719
theorem B16497269 : Blo 1447543 16497269 := bstep (se 5 (by rfl) ⟨773309, by rfl⟩ : syracuseStep 16497269 = 1546619) B1546619
theorem B1448795 : Blo 1447543 1448795 := bstep (se 1 (by rfl) ⟨1086596, by rfl⟩ : syracuseStep 1448795 = 2173193) B2173193
theorem B3259241 : Blo 1447543 3259241 := bstep (se 2 (by rfl) ⟨1222215, by rfl⟩ : syracuseStep 3259241 = 2444431) B2444431
theorem B3259295 : Blo 1447543 3259295 := bstep (se 1 (by rfl) ⟨2444471, by rfl⟩ : syracuseStep 3259295 = 4888943) B4888943
theorem B1448863 : Blo 1447543 1448863 := bstep (se 1 (by rfl) ⟨1086647, by rfl⟩ : syracuseStep 1448863 = 2173295) B2173295
theorem B4889591 : Blo 1447543 4889591 := bstep (se 1 (by rfl) ⟨3667193, by rfl⟩ : syracuseStep 4889591 = 7334387) B7334387
theorem B4127735 : Blo 1447543 4127735 := bstep (se 1 (by rfl) ⟨3095801, by rfl⟩ : syracuseStep 4127735 = 6191603) B6191603
theorem B1449007 : Blo 1447543 1449007 := bstep (se 1 (by rfl) ⟨1086755, by rfl⟩ : syracuseStep 1449007 = 2173511) B2173511
theorem B16727111 : Blo 1447543 16727111 := bstep (se 1 (by rfl) ⟨12545333, by rfl⟩ : syracuseStep 16727111 = 25090667) B25090667
theorem B1449031 : Blo 1447543 1449031 := bstep (se 1 (by rfl) ⟨1086773, by rfl⟩ : syracuseStep 1449031 = 2173547) B2173547
theorem B29736017 : Blo 1447543 29736017 := bstep (se 2 (by rfl) ⟨11151006, by rfl⟩ : syracuseStep 29736017 = 22302013) B22302013
theorem B11156609 : Blo 1447543 11156609 := bstep (se 2 (by rfl) ⟨4183728, by rfl⟩ : syracuseStep 11156609 = 8367457) B8367457
theorem B2751671 : Blo 1447543 2751671 := bstep (se 1 (by rfl) ⟨2063753, by rfl⟩ : syracuseStep 2751671 = 4127507) B4127507
theorem B1449183 : Blo 1447543 1449183 := bstep (se 1 (by rfl) ⟨1086887, by rfl⟩ : syracuseStep 1449183 = 2173775) B2173775
theorem B7437577 : Blo 1447543 7437577 := bstep (se 2 (by rfl) ⟨2789091, by rfl⟩ : syracuseStep 7437577 = 5578183) B5578183
theorem B8813929 : Blo 1447543 8813929 := bstep (se 2 (by rfl) ⟨3305223, by rfl⟩ : syracuseStep 8813929 = 6610447) B6610447
theorem B4890023 : Blo 1447543 4890023 := bstep (se 1 (by rfl) ⟨3667517, by rfl⟩ : syracuseStep 4890023 = 7335035) B7335035
theorem B5496295 : Blo 1447543 5496295 := bstep (se 1 (by rfl) ⟨4122221, by rfl⟩ : syracuseStep 5496295 = 8244443) B8244443
theorem B1449447 : Blo 1447543 1449447 := bstep (se 1 (by rfl) ⟨1087085, by rfl⟩ : syracuseStep 1449447 = 2174171) B2174171
theorem B1629787 : Blo 1447543 1629787 := bstep (se 1 (by rfl) ⟨1222340, by rfl⟩ : syracuseStep 1629787 = 2444681) B2444681
theorem B3260231 : Blo 1447543 3260231 := bstep (se 1 (by rfl) ⟨2445173, by rfl⟩ : syracuseStep 3260231 = 4890347) B4890347
theorem B4890455 : Blo 1447543 4890455 := bstep (se 1 (by rfl) ⟨3667841, by rfl⟩ : syracuseStep 4890455 = 7335683) B7335683
theorem B1630075 : Blo 1447543 1630075 := bstep (se 1 (by rfl) ⟨1222556, by rfl⟩ : syracuseStep 1630075 = 2445113) B2445113
theorem B16498727 : Blo 1447543 16498727 := bstep (se 1 (by rfl) ⟨12374045, by rfl⟩ : syracuseStep 16498727 = 24748091) B24748091
theorem B1630399 : Blo 1447543 1630399 := bstep (se 1 (by rfl) ⟨1222799, by rfl⟩ : syracuseStep 1630399 = 2445599) B2445599
theorem B3481807 : Blo 1447543 3481807 := bstep (se 1 (by rfl) ⟨2611355, by rfl⟩ : syracuseStep 3481807 = 5222711) B5222711
theorem B3260843 : Blo 1447543 3260843 := bstep (se 1 (by rfl) ⟨2445632, by rfl⟩ : syracuseStep 3260843 = 4891265) B4891265
theorem B3261023 : Blo 1447543 3261023 := bstep (se 1 (by rfl) ⟨2445767, by rfl⟩ : syracuseStep 3261023 = 4891535) B4891535
theorem B10994291 : Blo 1447543 10994291 := bstep (se 1 (by rfl) ⟨8245718, by rfl⟩ : syracuseStep 10994291 = 16491437) B16491437
theorem B5219063 : Blo 1447543 5219063 := bstep (se 1 (by rfl) ⟨3914297, by rfl⟩ : syracuseStep 5219063 = 7828595) B7828595
theorem B3482423 : Blo 1447543 3482423 := bstep (se 1 (by rfl) ⟨2611817, by rfl⟩ : syracuseStep 3482423 = 5223635) B5223635
theorem B13927261 : Blo 1447543 13927261 := bstep (se 3 (by rfl) ⟨2611361, by rfl⟩ : syracuseStep 13927261 = 5222723) B5222723
theorem B6185915 : Blo 1447543 6185915 := bstep (se 1 (by rfl) ⟨4639436, by rfl⟩ : syracuseStep 6185915 = 9278873) B9278873
theorem B3261383 : Blo 1447543 3261383 := bstep (se 1 (by rfl) ⟨2446037, by rfl⟩ : syracuseStep 3261383 = 4892075) B4892075
theorem B2171951 : Blo 1447543 2171951 := bstep (se 1 (by rfl) ⟨1628963, by rfl⟩ : syracuseStep 2171951 = 3257927) B3257927
theorem B10994777 : Blo 1447543 10994777 := bstep (se 2 (by rfl) ⟨4123041, by rfl⟩ : syracuseStep 10994777 = 8246083) B8246083
theorem B7054471 : Blo 1447543 7054471 := bstep (se 1 (by rfl) ⟨5290853, by rfl⟩ : syracuseStep 7054471 = 10581707) B10581707
theorem B2172071 : Blo 1447543 2172071 := bstep (se 1 (by rfl) ⟨1629053, by rfl⟩ : syracuseStep 2172071 = 3258107) B3258107
theorem B37635263 : Blo 1447543 37635263 := bstep (se 1 (by rfl) ⟨28226447, by rfl⟩ : syracuseStep 37635263 = 56452895) B56452895
theorem B2319673 : Blo 1447543 2319673 := bstep (se 2 (by rfl) ⟨869877, by rfl⟩ : syracuseStep 2319673 = 1739755) B1739755
theorem B14108087 : Blo 1447543 14108087 := bstep (se 1 (by rfl) ⟨10581065, by rfl⟩ : syracuseStep 14108087 = 21162131) B21162131
theorem B2172443 : Blo 1447543 2172443 := bstep (se 1 (by rfl) ⟨1629332, by rfl⟩ : syracuseStep 2172443 = 3258665) B3258665
theorem B10995263 : Blo 1447543 10995263 := bstep (se 1 (by rfl) ⟨8246447, by rfl⟩ : syracuseStep 10995263 = 16492895) B16492895
theorem B2172827 : Blo 1447543 2172827 := bstep (se 1 (by rfl) ⟨1629620, by rfl⟩ : syracuseStep 2172827 = 3259241) B3259241
theorem B2172863 : Blo 1447543 2172863 := bstep (se 1 (by rfl) ⟨1629647, by rfl⟩ : syracuseStep 2172863 = 3259295) B3259295
theorem B2934767 : Blo 1447543 2934767 := bstep (se 1 (by rfl) ⟨2201075, by rfl⟩ : syracuseStep 2934767 = 4402151) B4402151
theorem B6604831 : Blo 1447543 6604831 := bstep (se 1 (by rfl) ⟨4953623, by rfl⟩ : syracuseStep 6604831 = 9907247) B9907247
theorem B11151407 : Blo 1447543 11151407 := bstep (se 1 (by rfl) ⟨8363555, by rfl⟩ : syracuseStep 11151407 = 16727111) B16727111
theorem B2173049 : Blo 1447543 2173049 := bstep (se 2 (by rfl) ⟨814893, by rfl⟩ : syracuseStep 2173049 = 1629787) B1629787
theorem B2443547 : Blo 1447543 2443547 := bstep (se 1 (by rfl) ⟨1832660, by rfl⟩ : syracuseStep 2443547 = 3665321) B3665321
theorem B26446175 : Blo 1447543 26446175 := bstep (se 1 (by rfl) ⟨19834631, by rfl⟩ : syracuseStep 26446175 = 39669263) B39669263
theorem B2173433 : Blo 1447543 2173433 := bstep (se 2 (by rfl) ⟨815037, by rfl⟩ : syracuseStep 2173433 = 1630075) B1630075
theorem B10996235 : Blo 1447543 10996235 := bstep (se 1 (by rfl) ⟨8247176, by rfl⟩ : syracuseStep 10996235 = 16494353) B16494353
theorem B2173487 : Blo 1447543 2173487 := bstep (se 1 (by rfl) ⟨1630115, by rfl⟩ : syracuseStep 2173487 = 3260231) B3260231
theorem B2443871 : Blo 1447543 2443871 := bstep (se 1 (by rfl) ⟨1832903, by rfl⟩ : syracuseStep 2443871 = 3665807) B3665807
theorem B12536465 : Blo 1447543 12536465 := bstep (se 2 (by rfl) ⟨4701174, by rfl⟩ : syracuseStep 12536465 = 9402349) B9402349
theorem B44616577 : Blo 1447543 44616577 := bstep (se 2 (by rfl) ⟨16731216, by rfl⟩ : syracuseStep 44616577 = 33462433) B33462433
theorem B2173919 : Blo 1447543 2173919 := bstep (se 1 (by rfl) ⟨1630439, by rfl⟩ : syracuseStep 2173919 = 3260879) B3260879
theorem B4123817 : Blo 1447543 4123817 := bstep (se 2 (by rfl) ⟨1546431, by rfl⟩ : syracuseStep 4123817 = 3092863) B3092863
theorem B16714961 : Blo 1447543 16714961 := bstep (se 2 (by rfl) ⟨6268110, by rfl⟩ : syracuseStep 16714961 = 12536221) B12536221
theorem B4238611 : Blo 1447543 4238611 := bstep (se 1 (by rfl) ⟨3178958, by rfl⟩ : syracuseStep 4238611 = 6357917) B6357917
theorem B5025179 : Blo 1447543 5025179 := bstep (se 1 (by rfl) ⟨3768884, by rfl⟩ : syracuseStep 5025179 = 7537769) B7537769
theorem B10997207 : Blo 1447543 10997207 := bstep (se 1 (by rfl) ⟨8247905, by rfl⟩ : syracuseStep 10997207 = 16495811) B16495811
theorem B5500487 : Blo 1447543 5500487 := bstep (se 1 (by rfl) ⟨4125365, by rfl⟩ : syracuseStep 5500487 = 8250731) B8250731
theorem B3714703 : Blo 1447543 3714703 := bstep (se 1 (by rfl) ⟨2786027, by rfl⟩ : syracuseStep 3714703 = 5572055) B5572055
theorem B3092111 : Blo 1447543 3092111 := bstep (se 1 (by rfl) ⟨2319083, by rfl⟩ : syracuseStep 3092111 = 4638167) B4638167
theorem B23490317 : Blo 1447543 23490317 := bstep (se 3 (by rfl) ⟨4404434, by rfl⟩ : syracuseStep 23490317 = 8808869) B8808869
theorem B15658829 : Blo 1447543 15658829 := bstep (se 3 (by rfl) ⟨2936030, by rfl⟩ : syracuseStep 15658829 = 5872061) B5872061
theorem B2445295 : Blo 1447543 2445295 := bstep (se 1 (by rfl) ⟨1833971, by rfl⟩ : syracuseStep 2445295 = 3667943) B3667943
theorem B4640807 : Blo 1447543 4640807 := bstep (se 1 (by rfl) ⟨3480605, by rfl⟩ : syracuseStep 4640807 = 6961211) B6961211
theorem B2748649 : Blo 1447543 2748649 := bstep (se 2 (by rfl) ⟨1030743, by rfl⟩ : syracuseStep 2748649 = 2061487) B2061487
theorem B9916769 : Blo 1447543 9916769 := bstep (se 2 (by rfl) ⟨3718788, by rfl⟩ : syracuseStep 9916769 = 7437577) B7437577
theorem B7827839 : Blo 1447543 7827839 := bstep (se 1 (by rfl) ⟨5870879, by rfl⟩ : syracuseStep 7827839 = 11741759) B11741759
theorem B81490303 : Blo 1447543 81490303 := bstep (se 1 (by rfl) ⟨61117727, by rfl⟩ : syracuseStep 81490303 = 122235455) B122235455
theorem B10998179 : Blo 1447543 10998179 := bstep (se 1 (by rfl) ⟨8248634, by rfl⟩ : syracuseStep 10998179 = 16497269) B16497269
theorem B5222839 : Blo 1447543 5222839 := bstep (se 1 (by rfl) ⟨3917129, by rfl⟩ : syracuseStep 5222839 = 7834259) B7834259
theorem B11751905 : Blo 1447543 11751905 := bstep (se 2 (by rfl) ⟨4406964, by rfl⟩ : syracuseStep 11751905 = 8813929) B8813929
theorem B5026367 : Blo 1447543 5026367 := bstep (se 1 (by rfl) ⟨3769775, by rfl⟩ : syracuseStep 5026367 = 7539551) B7539551
theorem B7328393 : Blo 1447543 7328393 := bstep (se 2 (by rfl) ⟨2748147, by rfl⟩ : syracuseStep 7328393 = 5496295) B5496295
theorem B3666667 : Blo 1447543 3666667 := bstep (se 1 (by rfl) ⟨2750000, by rfl⟩ : syracuseStep 3666667 = 5500001) B5500001
theorem B3257135 : Blo 1447543 3257135 := bstep (se 1 (by rfl) ⟨2442851, by rfl⟩ : syracuseStep 3257135 = 4885703) B4885703
theorem B3257225 : Blo 1447543 3257225 := bstep (se 2 (by rfl) ⟨1221459, by rfl⟩ : syracuseStep 3257225 = 2442919) B2442919
theorem B5501945 : Blo 1447543 5501945 := bstep (se 2 (by rfl) ⟨2063229, by rfl⟩ : syracuseStep 5501945 = 4126459) B4126459
theorem B6190289 : Blo 1447543 6190289 := bstep (se 2 (by rfl) ⟨2321358, by rfl⟩ : syracuseStep 6190289 = 4642717) B4642717
theorem B3478895 : Blo 1447543 3478895 := bstep (se 1 (by rfl) ⟨2609171, by rfl⟩ : syracuseStep 3478895 = 5218343) B5218343
theorem B1832539 : Blo 1447543 1832539 := bstep (se 1 (by rfl) ⟨1374404, by rfl⟩ : syracuseStep 1832539 = 2748809) B2748809
theorem B3094127 : Blo 1447543 3094127 := bstep (se 1 (by rfl) ⟨2320595, by rfl⟩ : syracuseStep 3094127 = 4641191) B4641191
theorem B3257999 : Blo 1447543 3257999 := bstep (se 1 (by rfl) ⟨2443499, by rfl⟩ : syracuseStep 3257999 = 4886999) B4886999
theorem B1447579 : Blo 1447543 1447579 := bstep (se 1 (by rfl) ⟨1085684, by rfl⟩ : syracuseStep 1447579 = 2171369) B2171369
theorem B16733899 : Blo 1447543 16733899 := bstep (se 1 (by rfl) ⟨12550424, by rfl⟩ : syracuseStep 16733899 = 25100849) B25100849
theorem B3258089 : Blo 1447543 3258089 := bstep (se 2 (by rfl) ⟨1221783, by rfl⟩ : syracuseStep 3258089 = 2443567) B2443567
theorem B1447663 : Blo 1447543 1447663 := bstep (se 1 (by rfl) ⟨1085747, by rfl⟩ : syracuseStep 1447663 = 2171495) B2171495
theorem B7337789 : Blo 1447543 7337789 := bstep (se 3 (by rfl) ⟨1375835, by rfl⟩ : syracuseStep 7337789 = 2751671) B2751671
theorem B1447751 : Blo 1447543 1447751 := bstep (se 1 (by rfl) ⟨1085813, by rfl⟩ : syracuseStep 1447751 = 2171627) B2171627
theorem B4888403 : Blo 1447543 4888403 := bstep (se 1 (by rfl) ⟨3666302, by rfl⟩ : syracuseStep 4888403 = 7332605) B7332605
theorem B1447771 : Blo 1447543 1447771 := bstep (se 1 (by rfl) ⟨1085828, by rfl⟩ : syracuseStep 1447771 = 2171657) B2171657
theorem B1447839 : Blo 1447543 1447839 := bstep (se 1 (by rfl) ⟨1085879, by rfl⟩ : syracuseStep 1447839 = 2171759) B2171759
theorem B6961153 : Blo 1447543 6961153 := bstep (se 2 (by rfl) ⟨2610432, by rfl⟩ : syracuseStep 6961153 = 5220865) B5220865
theorem B1448007 : Blo 1447543 1448007 := bstep (se 1 (by rfl) ⟨1086005, by rfl⟩ : syracuseStep 1448007 = 2172011) B2172011
theorem B1448167 : Blo 1447543 1448167 := bstep (se 1 (by rfl) ⟨1086125, by rfl⟩ : syracuseStep 1448167 = 2172251) B2172251
theorem B2750699 : Blo 1447543 2750699 := bstep (se 1 (by rfl) ⟨2063024, by rfl⟩ : syracuseStep 2750699 = 4126049) B4126049
theorem B1448351 : Blo 1447543 1448351 := bstep (se 1 (by rfl) ⟨1086263, by rfl⟩ : syracuseStep 1448351 = 2172527) B2172527
theorem B1448399 : Blo 1447543 1448399 := bstep (se 1 (by rfl) ⟨1086299, by rfl⟩ : syracuseStep 1448399 = 2172599) B2172599
theorem B1448423 : Blo 1447543 1448423 := bstep (se 1 (by rfl) ⟨1086317, by rfl⟩ : syracuseStep 1448423 = 2172635) B2172635
theorem B23476823 : Blo 1447543 23476823 := bstep (se 1 (by rfl) ⟨17607617, by rfl⟩ : syracuseStep 23476823 = 35215235) B35215235
theorem B3258971 : Blo 1447543 3258971 := bstep (se 1 (by rfl) ⟨2444228, by rfl⟩ : syracuseStep 3258971 = 4888457) B4888457
theorem B1448539 : Blo 1447543 1448539 := bstep (se 1 (by rfl) ⟨1086404, by rfl⟩ : syracuseStep 1448539 = 2172809) B2172809
theorem B1448607 : Blo 1447543 1448607 := bstep (se 1 (by rfl) ⟨1086455, by rfl⟩ : syracuseStep 1448607 = 2172911) B2172911
theorem B3259115 : Blo 1447543 3259115 := bstep (se 1 (by rfl) ⟨2444336, by rfl⟩ : syracuseStep 3259115 = 4888673) B4888673
theorem B11000609 : Blo 1447543 11000609 := bstep (se 2 (by rfl) ⟨4125228, by rfl⟩ : syracuseStep 11000609 = 8250457) B8250457
theorem B4643639 : Blo 1447543 4643639 := bstep (se 1 (by rfl) ⟨3482729, by rfl⟩ : syracuseStep 4643639 = 6965459) B6965459
theorem B1448775 : Blo 1447543 1448775 := bstep (se 1 (by rfl) ⟨1086581, by rfl⟩ : syracuseStep 1448775 = 2173163) B2173163
theorem B1448815 : Blo 1447543 1448815 := bstep (se 1 (by rfl) ⟨1086611, by rfl⟩ : syracuseStep 1448815 = 2173223) B2173223
theorem B1448871 : Blo 1447543 1448871 := bstep (se 1 (by rfl) ⟨1086653, by rfl⟩ : syracuseStep 1448871 = 2173307) B2173307
theorem B1449051 : Blo 1447543 1449051 := bstep (se 1 (by rfl) ⟨1086788, by rfl⟩ : syracuseStep 1449051 = 2173577) B2173577
theorem B8043625 : Blo 1447543 8043625 := bstep (se 2 (by rfl) ⟨3016359, by rfl⟩ : syracuseStep 8043625 = 6032719) B6032719
theorem B1629391 : Blo 1447543 1629391 := bstep (se 1 (by rfl) ⟨1222043, by rfl⟩ : syracuseStep 1629391 = 2444087) B2444087
theorem B4889807 : Blo 1447543 4889807 := bstep (se 1 (by rfl) ⟨3667355, by rfl⟩ : syracuseStep 4889807 = 7334711) B7334711
theorem B1449167 : Blo 1447543 1449167 := bstep (se 1 (by rfl) ⟨1086875, by rfl⟩ : syracuseStep 1449167 = 2173751) B2173751
theorem B1449191 : Blo 1447543 1449191 := bstep (se 1 (by rfl) ⟨1086893, by rfl⟩ : syracuseStep 1449191 = 2173787) B2173787
theorem B1449287 : Blo 1447543 1449287 := bstep (se 1 (by rfl) ⟨1086965, by rfl⟩ : syracuseStep 1449287 = 2173931) B2173931
theorem B3259727 : Blo 1447543 3259727 := bstep (se 1 (by rfl) ⟨2444795, by rfl⟩ : syracuseStep 3259727 = 4889591) B4889591
theorem B2751823 : Blo 1447543 2751823 := bstep (se 1 (by rfl) ⟨2063867, by rfl⟩ : syracuseStep 2751823 = 4127735) B4127735
theorem B19824011 : Blo 1447543 19824011 := bstep (se 1 (by rfl) ⟨14868008, by rfl⟩ : syracuseStep 19824011 = 29736017) B29736017
theorem B3259817 : Blo 1447543 3259817 := bstep (se 2 (by rfl) ⟨1222431, by rfl⟩ : syracuseStep 3259817 = 2444863) B2444863
theorem B7437739 : Blo 1447543 7437739 := bstep (se 1 (by rfl) ⟨5578304, by rfl⟩ : syracuseStep 7437739 = 11156609) B11156609
theorem B1449423 : Blo 1447543 1449423 := bstep (se 1 (by rfl) ⟨1087067, by rfl⟩ : syracuseStep 1449423 = 2174135) B2174135
theorem B18570707 : Blo 1447543 18570707 := bstep (se 1 (by rfl) ⟨13928030, by rfl⟩ : syracuseStep 18570707 = 27856061) B27856061
theorem B4890185 : Blo 1447543 4890185 := bstep (se 2 (by rfl) ⟨1833819, by rfl⟩ : syracuseStep 4890185 = 3667639) B3667639
theorem B3260015 : Blo 1447543 3260015 := bstep (se 1 (by rfl) ⟨2445011, by rfl⟩ : syracuseStep 3260015 = 4890023) B4890023
theorem B3260303 : Blo 1447543 3260303 := bstep (se 1 (by rfl) ⟨2445227, by rfl⟩ : syracuseStep 3260303 = 4890455) B4890455
theorem B3481499 : Blo 1447543 3481499 := bstep (se 1 (by rfl) ⟨2611124, by rfl⟩ : syracuseStep 3481499 = 5222249) B5222249
theorem B9281537 : Blo 1447543 9281537 := bstep (se 2 (by rfl) ⟨3480576, by rfl⟩ : syracuseStep 9281537 = 6961153) B6961153
theorem B8806441 : Blo 1447543 8806441 := bstep (se 2 (by rfl) ⟨3302415, by rfl⟩ : syracuseStep 8806441 = 6604831) B6604831
theorem B6611179 : Blo 1447543 6611179 := bstep (se 1 (by rfl) ⟨4958384, by rfl⟩ : syracuseStep 6611179 = 9916769) B9916769
theorem B5218559 : Blo 1447543 5218559 := bstep (se 1 (by rfl) ⟨3913919, by rfl⟩ : syracuseStep 5218559 = 7827839) B7827839
theorem B7332119 : Blo 1447543 7332119 := bstep (se 1 (by rfl) ⟨5499089, by rfl⟩ : syracuseStep 7332119 = 10998179) B10998179
theorem B3350911 : Blo 1447543 3350911 := bstep (se 1 (by rfl) ⟨2513183, by rfl⟩ : syracuseStep 3350911 = 5026367) B5026367
theorem B2171423 : Blo 1447543 2171423 := bstep (se 1 (by rfl) ⟨1628567, by rfl⟩ : syracuseStep 2171423 = 3257135) B3257135
theorem B6963785 : Blo 1447543 6963785 := bstep (se 2 (by rfl) ⟨2611419, by rfl⟩ : syracuseStep 6963785 = 5222839) B5222839
theorem B2171483 : Blo 1447543 2171483 := bstep (se 1 (by rfl) ⟨1628612, by rfl⟩ : syracuseStep 2171483 = 3257225) B3257225
theorem B2319263 : Blo 1447543 2319263 := bstep (se 1 (by rfl) ⟨1739447, by rfl⟩ : syracuseStep 2319263 = 3478895) B3478895
theorem B9405391 : Blo 1447543 9405391 := bstep (se 1 (by rfl) ⟨7054043, by rfl⟩ : syracuseStep 9405391 = 14108087) B14108087
theorem B2171999 : Blo 1447543 2171999 := bstep (se 1 (by rfl) ⟨1628999, by rfl⟩ : syracuseStep 2171999 = 3257999) B3257999
theorem B2172059 : Blo 1447543 2172059 := bstep (se 1 (by rfl) ⟨1629044, by rfl⟩ : syracuseStep 2172059 = 3258089) B3258089
theorem B4891859 : Blo 1447543 4891859 := bstep (se 1 (by rfl) ⟨3668894, by rfl⟩ : syracuseStep 4891859 = 7337789) B7337789
theorem B10724833 : Blo 1447543 10724833 := bstep (se 2 (by rfl) ⟨4021812, by rfl⟩ : syracuseStep 10724833 = 8043625) B8043625
theorem B17630783 : Blo 1447543 17630783 := bstep (se 1 (by rfl) ⟨13223087, by rfl⟩ : syracuseStep 17630783 = 26446175) B26446175
theorem B2172521 : Blo 1447543 2172521 := bstep (se 2 (by rfl) ⟨814695, by rfl⟩ : syracuseStep 2172521 = 1629391) B1629391
theorem B2172647 : Blo 1447543 2172647 := bstep (se 1 (by rfl) ⟨1629485, by rfl⟩ : syracuseStep 2172647 = 3258971) B3258971
theorem B2172743 : Blo 1447543 2172743 := bstep (se 1 (by rfl) ⟨1629557, by rfl⟩ : syracuseStep 2172743 = 3259115) B3259115
theorem B7333739 : Blo 1447543 7333739 := bstep (se 1 (by rfl) ⟨5500304, by rfl⟩ : syracuseStep 7333739 = 11000609) B11000609
theorem B2443385 : Blo 1447543 2443385 := bstep (se 2 (by rfl) ⟨916269, by rfl⟩ : syracuseStep 2443385 = 1832539) B1832539
theorem B11143307 : Blo 1447543 11143307 := bstep (se 1 (by rfl) ⟨8357480, by rfl⟩ : syracuseStep 11143307 = 16714961) B16714961
theorem B2173151 : Blo 1447543 2173151 := bstep (se 1 (by rfl) ⟨1629863, by rfl⟩ : syracuseStep 2173151 = 3259727) B3259727
theorem B13216007 : Blo 1447543 13216007 := bstep (se 1 (by rfl) ⟨9912005, by rfl⟩ : syracuseStep 13216007 = 19824011) B19824011
theorem B2173211 : Blo 1447543 2173211 := bstep (se 1 (by rfl) ⟨1629908, by rfl⟩ : syracuseStep 2173211 = 3259817) B3259817
theorem B12380471 : Blo 1447543 12380471 := bstep (se 1 (by rfl) ⟨9285353, by rfl⟩ : syracuseStep 12380471 = 18570707) B18570707
theorem B9283997 : Blo 1447543 9283997 := bstep (se 3 (by rfl) ⟨1740749, by rfl⟩ : syracuseStep 9283997 = 3481499) B3481499
theorem B2173343 : Blo 1447543 2173343 := bstep (se 1 (by rfl) ⟨1630007, by rfl⟩ : syracuseStep 2173343 = 3260015) B3260015
theorem B10439219 : Blo 1447543 10439219 := bstep (se 1 (by rfl) ⟨7829414, by rfl⟩ : syracuseStep 10439219 = 15658829) B15658829
theorem B2173535 : Blo 1447543 2173535 := bstep (se 1 (by rfl) ⟨1630151, by rfl⟩ : syracuseStep 2173535 = 3260303) B3260303
theorem B2173865 : Blo 1447543 2173865 := bstep (se 2 (by rfl) ⟨815199, by rfl⟩ : syracuseStep 2173865 = 1630399) B1630399
theorem B2173895 : Blo 1447543 2173895 := bstep (se 1 (by rfl) ⟨1630421, by rfl⟩ : syracuseStep 2173895 = 3260843) B3260843
theorem B3664865 : Blo 1447543 3664865 := bstep (se 2 (by rfl) ⟨1374324, by rfl⟩ : syracuseStep 3664865 = 2748649) B2748649
theorem B2174015 : Blo 1447543 2174015 := bstep (se 1 (by rfl) ⟨1630511, by rfl⟩ : syracuseStep 2174015 = 3261023) B3261023
theorem B4885595 : Blo 1447543 4885595 := bstep (se 1 (by rfl) ⟨3664196, by rfl⟩ : syracuseStep 4885595 = 7328393) B7328393
theorem B108653737 : Blo 1447543 108653737 := bstep (se 2 (by rfl) ⟨40745151, by rfl⟩ : syracuseStep 108653737 = 81490303) B81490303
theorem B2321615 : Blo 1447543 2321615 := bstep (se 1 (by rfl) ⟨1741211, by rfl⟩ : syracuseStep 2321615 = 3482423) B3482423
theorem B7335197 : Blo 1447543 7335197 := bstep (se 3 (by rfl) ⟨1375349, by rfl⟩ : syracuseStep 7335197 = 2750699) B2750699
theorem B4123943 : Blo 1447543 4123943 := bstep (se 1 (by rfl) ⟨3092957, by rfl⟩ : syracuseStep 4123943 = 6185915) B6185915
theorem B2174255 : Blo 1447543 2174255 := bstep (se 1 (by rfl) ⟨1630691, by rfl⟩ : syracuseStep 2174255 = 3261383) B3261383
theorem B19811749 : Blo 1447543 19811749 := bstep (se 4 (by rfl) ⟨1857351, by rfl⟩ : syracuseStep 19811749 = 3714703) B3714703
theorem B31338413 : Blo 1447543 31338413 := bstep (se 3 (by rfl) ⟨5875952, by rfl⟩ : syracuseStep 31338413 = 11751905) B11751905
theorem B7434271 : Blo 1447543 7434271 := bstep (se 1 (by rfl) ⟨5575703, by rfl⟩ : syracuseStep 7434271 = 11151407) B11151407
theorem B22605925 : Blo 1447543 22605925 := bstep (se 4 (by rfl) ⟨2119305, by rfl⟩ : syracuseStep 22605925 = 4238611) B4238611
theorem B15651215 : Blo 1447543 15651215 := bstep (se 1 (by rfl) ⟨11738411, by rfl⟩ : syracuseStep 15651215 = 23476823) B23476823
theorem B3092897 : Blo 1447543 3092897 := bstep (se 2 (by rfl) ⟨1159836, by rfl⟩ : syracuseStep 3092897 = 2319673) B2319673
theorem B9916985 : Blo 1447543 9916985 := bstep (se 2 (by rfl) ⟨3718869, by rfl⟩ : syracuseStep 9916985 = 7437739) B7437739
theorem B2749211 : Blo 1447543 2749211 := bstep (se 1 (by rfl) ⟨2061908, by rfl⟩ : syracuseStep 2749211 = 4123817) B4123817
theorem B22311865 : Blo 1447543 22311865 := bstep (se 2 (by rfl) ⟨8366949, by rfl⟩ : syracuseStep 22311865 = 16733899) B16733899
theorem B3666991 : Blo 1447543 3666991 := bstep (se 1 (by rfl) ⟨2750243, by rfl⟩ : syracuseStep 3666991 = 5500487) B5500487
theorem B2061407 : Blo 1447543 2061407 := bstep (se 1 (by rfl) ⟨1546055, by rfl⟩ : syracuseStep 2061407 = 3092111) B3092111
theorem B15660211 : Blo 1447543 15660211 := bstep (se 1 (by rfl) ⟨11745158, by rfl⟩ : syracuseStep 15660211 = 23490317) B23490317
theorem B10999151 : Blo 1447543 10999151 := bstep (se 1 (by rfl) ⟨8249363, by rfl⟩ : syracuseStep 10999151 = 16498727) B16498727
theorem B3093871 : Blo 1447543 3093871 := bstep (se 1 (by rfl) ⟨2320403, by rfl⟩ : syracuseStep 3093871 = 4640807) B4640807
theorem B4642409 : Blo 1447543 4642409 := bstep (se 2 (by rfl) ⟨1740903, by rfl⟩ : syracuseStep 4642409 = 3481807) B3481807
theorem B7329527 : Blo 1447543 7329527 := bstep (se 1 (by rfl) ⟨5497145, by rfl⟩ : syracuseStep 7329527 = 10994291) B10994291
theorem B3479375 : Blo 1447543 3479375 := bstep (se 1 (by rfl) ⟨2609531, by rfl⟩ : syracuseStep 3479375 = 5219063) B5219063
theorem B3667963 : Blo 1447543 3667963 := bstep (se 1 (by rfl) ⟨2750972, by rfl⟩ : syracuseStep 3667963 = 5501945) B5501945
theorem B1447967 : Blo 1447543 1447967 := bstep (se 1 (by rfl) ⟨1085975, by rfl⟩ : syracuseStep 1447967 = 2171951) B2171951
theorem B37623845 : Blo 1447543 37623845 := bstep (se 4 (by rfl) ⟨3527235, by rfl⟩ : syracuseStep 37623845 = 7054471) B7054471
theorem B7329851 : Blo 1447543 7329851 := bstep (se 1 (by rfl) ⟨5497388, by rfl⟩ : syracuseStep 7329851 = 10994777) B10994777
theorem B1448047 : Blo 1447543 1448047 := bstep (se 1 (by rfl) ⟨1086035, by rfl⟩ : syracuseStep 1448047 = 2172071) B2172071
theorem B25090175 : Blo 1447543 25090175 := bstep (se 1 (by rfl) ⟨18817631, by rfl⟩ : syracuseStep 25090175 = 37635263) B37635263
theorem B4126859 : Blo 1447543 4126859 := bstep (se 1 (by rfl) ⟨3095144, by rfl⟩ : syracuseStep 4126859 = 6190289) B6190289
theorem B4888889 : Blo 1447543 4888889 := bstep (se 2 (by rfl) ⟨1833333, by rfl⟩ : syracuseStep 4888889 = 3666667) B3666667
theorem B1448295 : Blo 1447543 1448295 := bstep (se 1 (by rfl) ⟨1086221, by rfl⟩ : syracuseStep 1448295 = 2172443) B2172443
theorem B7330175 : Blo 1447543 7330175 := bstep (se 1 (by rfl) ⟨5497631, by rfl⟩ : syracuseStep 7330175 = 10995263) B10995263
theorem B13400477 : Blo 1447543 13400477 := bstep (se 3 (by rfl) ⟨2512589, by rfl⟩ : syracuseStep 13400477 = 5025179) B5025179
theorem B2062751 : Blo 1447543 2062751 := bstep (se 1 (by rfl) ⟨1547063, by rfl⟩ : syracuseStep 2062751 = 3094127) B3094127
theorem B18569681 : Blo 1447543 18569681 := bstep (se 2 (by rfl) ⟨6963630, by rfl⟩ : syracuseStep 18569681 = 13927261) B13927261
theorem B59488769 : Blo 1447543 59488769 := bstep (se 2 (by rfl) ⟨22308288, by rfl⟩ : syracuseStep 59488769 = 44616577) B44616577
theorem B3258935 : Blo 1447543 3258935 := bstep (se 1 (by rfl) ⟨2444201, by rfl⟩ : syracuseStep 3258935 = 4888403) B4888403
theorem B1448551 : Blo 1447543 1448551 := bstep (se 1 (by rfl) ⟨1086413, by rfl⟩ : syracuseStep 1448551 = 2172827) B2172827
theorem B1448575 : Blo 1447543 1448575 := bstep (se 1 (by rfl) ⟨1086431, by rfl⟩ : syracuseStep 1448575 = 2172863) B2172863
theorem B1956511 : Blo 1447543 1956511 := bstep (se 1 (by rfl) ⟨1467383, by rfl⟩ : syracuseStep 1956511 = 2934767) B2934767
theorem B1448699 : Blo 1447543 1448699 := bstep (se 1 (by rfl) ⟨1086524, by rfl⟩ : syracuseStep 1448699 = 2173049) B2173049
theorem B1629031 : Blo 1447543 1629031 := bstep (se 1 (by rfl) ⟨1221773, by rfl⟩ : syracuseStep 1629031 = 2443547) B2443547
theorem B1448955 : Blo 1447543 1448955 := bstep (se 1 (by rfl) ⟨1086716, by rfl⟩ : syracuseStep 1448955 = 2173433) B2173433
theorem B7330823 : Blo 1447543 7330823 := bstep (se 1 (by rfl) ⟨5498117, by rfl⟩ : syracuseStep 7330823 = 10996235) B10996235
theorem B1448991 : Blo 1447543 1448991 := bstep (se 1 (by rfl) ⟨1086743, by rfl⟩ : syracuseStep 1448991 = 2173487) B2173487
theorem B33430573 : Blo 1447543 33430573 := bstep (se 3 (by rfl) ⟨6268232, by rfl⟩ : syracuseStep 33430573 = 12536465) B12536465
theorem B1629247 : Blo 1447543 1629247 := bstep (se 1 (by rfl) ⟨1221935, by rfl⟩ : syracuseStep 1629247 = 2443871) B2443871
theorem B3669097 : Blo 1447543 3669097 := bstep (se 2 (by rfl) ⟨1375911, by rfl⟩ : syracuseStep 3669097 = 2751823) B2751823
theorem B3095759 : Blo 1447543 3095759 := bstep (se 1 (by rfl) ⟨2321819, by rfl⟩ : syracuseStep 3095759 = 4643639) B4643639
theorem B1449279 : Blo 1447543 1449279 := bstep (se 1 (by rfl) ⟨1086959, by rfl⟩ : syracuseStep 1449279 = 2173919) B2173919
theorem B3259871 : Blo 1447543 3259871 := bstep (se 1 (by rfl) ⟨2444903, by rfl⟩ : syracuseStep 3259871 = 4889807) B4889807
theorem B7331471 : Blo 1447543 7331471 := bstep (se 1 (by rfl) ⟨5498603, by rfl⟩ : syracuseStep 7331471 = 10997207) B10997207
theorem B3260123 : Blo 1447543 3260123 := bstep (se 1 (by rfl) ⟨2445092, by rfl⟩ : syracuseStep 3260123 = 4890185) B4890185
theorem B3260393 : Blo 1447543 3260393 := bstep (se 2 (by rfl) ⟨1222647, by rfl⟩ : syracuseStep 3260393 = 2445295) B2445295
theorem B39649445 : Blo 1447543 39649445 := bstep (se 4 (by rfl) ⟨3717135, by rfl⟩ : syracuseStep 39649445 = 7434271) B7434271
theorem B5497085 : Blo 1447543 5497085 := bstep (se 3 (by rfl) ⟨1030703, by rfl⟩ : syracuseStep 5497085 = 2061407) B2061407
theorem B8814905 : Blo 1447543 8814905 := bstep (se 2 (by rfl) ⟨3305589, by rfl⟩ : syracuseStep 8814905 = 6611179) B6611179
theorem B6611323 : Blo 1447543 6611323 := bstep (se 1 (by rfl) ⟨4958492, by rfl⟩ : syracuseStep 6611323 = 9916985) B9916985
theorem B35242685 : Blo 1447543 35242685 := bstep (se 3 (by rfl) ⟨6608003, by rfl⟩ : syracuseStep 35242685 = 13216007) B13216007
theorem B3261239 : Blo 1447543 3261239 := bstep (se 1 (by rfl) ⟨2445929, by rfl⟩ : syracuseStep 3261239 = 4891859) B4891859
theorem B7332767 : Blo 1447543 7332767 := bstep (se 1 (by rfl) ⟨5499575, by rfl⟩ : syracuseStep 7332767 = 10999151) B10999151
theorem B2172041 : Blo 1447543 2172041 := bstep (se 2 (by rfl) ⟨814515, by rfl⟩ : syracuseStep 2172041 = 1629031) B1629031
theorem B44574097 : Blo 1447543 44574097 := bstep (se 2 (by rfl) ⟨16715286, by rfl⟩ : syracuseStep 44574097 = 33430573) B33430573
theorem B2172329 : Blo 1447543 2172329 := bstep (se 2 (by rfl) ⟨814623, by rfl⟩ : syracuseStep 2172329 = 1629247) B1629247
theorem B4892129 : Blo 1447543 4892129 := bstep (se 2 (by rfl) ⟨1834548, by rfl⟩ : syracuseStep 4892129 = 3669097) B3669097
theorem B12379787 : Blo 1447543 12379787 := bstep (se 1 (by rfl) ⟨9284840, by rfl⟩ : syracuseStep 12379787 = 18569681) B18569681
theorem B39659179 : Blo 1447543 39659179 := bstep (se 1 (by rfl) ⟨29744384, by rfl⟩ : syracuseStep 39659179 = 59488769) B59488769
theorem B2172623 : Blo 1447543 2172623 := bstep (se 1 (by rfl) ⟨1629467, by rfl⟩ : syracuseStep 2172623 = 3258935) B3258935
theorem B2443243 : Blo 1447543 2443243 := bstep (se 1 (by rfl) ⟨1832432, by rfl⟩ : syracuseStep 2443243 = 3664865) B3664865
theorem B2173247 : Blo 1447543 2173247 := bstep (se 1 (by rfl) ⟨1629935, by rfl⟩ : syracuseStep 2173247 = 3259871) B3259871
theorem B2173415 : Blo 1447543 2173415 := bstep (se 1 (by rfl) ⟨1630061, by rfl⟩ : syracuseStep 2173415 = 3260123) B3260123
theorem B20892275 : Blo 1447543 20892275 := bstep (se 1 (by rfl) ⟨15669206, by rfl⟩ : syracuseStep 20892275 = 31338413) B31338413
theorem B2173595 : Blo 1447543 2173595 := bstep (se 1 (by rfl) ⟨1630196, by rfl⟩ : syracuseStep 2173595 = 3260393) B3260393
theorem B6187691 : Blo 1447543 6187691 := bstep (se 1 (by rfl) ⟨4640768, by rfl⟩ : syracuseStep 6187691 = 9281537) B9281537
theorem B11741921 : Blo 1447543 11741921 := bstep (se 2 (by rfl) ⟨4403220, by rfl⟩ : syracuseStep 11741921 = 8806441) B8806441
theorem B30141233 : Blo 1447543 30141233 := bstep (se 2 (by rfl) ⟨11302962, by rfl⟩ : syracuseStep 30141233 = 22605925) B22605925
theorem B66907133 : Blo 1447543 66907133 := bstep (se 3 (by rfl) ⟨12545087, by rfl⟩ : syracuseStep 66907133 = 25090175) B25090175
theorem B4467881 : Blo 1447543 4467881 := bstep (se 2 (by rfl) ⟨1675455, by rfl⟩ : syracuseStep 4467881 = 3350911) B3350911
theorem B2608681 : Blo 1447543 2608681 := bstep (se 2 (by rfl) ⟨978255, by rfl⟩ : syracuseStep 2608681 = 1956511) B1956511
theorem B5500669 : Blo 1447543 5500669 := bstep (se 3 (by rfl) ⟨1031375, by rfl⟩ : syracuseStep 5500669 = 2062751) B2062751
theorem B4886351 : Blo 1447543 4886351 := bstep (se 1 (by rfl) ⟨3664763, by rfl⟩ : syracuseStep 4886351 = 7329527) B7329527
theorem B29749153 : Blo 1447543 29749153 := bstep (se 2 (by rfl) ⟨11155932, by rfl⟩ : syracuseStep 29749153 = 22311865) B22311865
theorem B4886567 : Blo 1447543 4886567 := bstep (se 1 (by rfl) ⟨3664925, by rfl⟩ : syracuseStep 4886567 = 7329851) B7329851
theorem B8253647 : Blo 1447543 8253647 := bstep (se 1 (by rfl) ⟨6190235, by rfl⟩ : syracuseStep 8253647 = 12380471) B12380471
theorem B144871649 : Blo 1447543 144871649 := bstep (se 2 (by rfl) ⟨54326868, by rfl⟩ : syracuseStep 144871649 = 108653737) B108653737
theorem B4886783 : Blo 1447543 4886783 := bstep (se 1 (by rfl) ⟨3665087, by rfl⟩ : syracuseStep 4886783 = 7330175) B7330175
theorem B6189331 : Blo 1447543 6189331 := bstep (se 1 (by rfl) ⟨4641998, by rfl⟩ : syracuseStep 6189331 = 9283997) B9283997
theorem B8933651 : Blo 1447543 8933651 := bstep (se 1 (by rfl) ⟨6700238, by rfl⟩ : syracuseStep 8933651 = 13400477) B13400477
theorem B6959479 : Blo 1447543 6959479 := bstep (se 1 (by rfl) ⟨5219609, by rfl⟩ : syracuseStep 6959479 = 10439219) B10439219
theorem B4125161 : Blo 1447543 4125161 := bstep (se 2 (by rfl) ⟨1546935, by rfl⟩ : syracuseStep 4125161 = 3093871) B3093871
theorem B26415665 : Blo 1447543 26415665 := bstep (se 2 (by rfl) ⟨9905874, by rfl⟩ : syracuseStep 26415665 = 19811749) B19811749
theorem B14299777 : Blo 1447543 14299777 := bstep (se 2 (by rfl) ⟨5362416, by rfl⟩ : syracuseStep 14299777 = 10724833) B10724833
theorem B4887215 : Blo 1447543 4887215 := bstep (se 1 (by rfl) ⟨3665411, by rfl⟩ : syracuseStep 4887215 = 7330823) B7330823
theorem B3257063 : Blo 1447543 3257063 := bstep (se 1 (by rfl) ⟨2442797, by rfl⟩ : syracuseStep 3257063 = 4885595) B4885595
theorem B2749295 : Blo 1447543 2749295 := bstep (se 1 (by rfl) ⟨2061971, by rfl⟩ : syracuseStep 2749295 = 4123943) B4123943
theorem B9278333 : Blo 1447543 9278333 := bstep (se 3 (by rfl) ⟨1739687, by rfl⟩ : syracuseStep 9278333 = 3479375) B3479375
theorem B4887647 : Blo 1447543 4887647 := bstep (se 1 (by rfl) ⟨3665735, by rfl⟩ : syracuseStep 4887647 = 7331471) B7331471
theorem B4890617 : Blo 1447543 4890617 := bstep (se 2 (by rfl) ⟨1833981, by rfl⟩ : syracuseStep 4890617 = 3667963) B3667963
theorem B3479039 : Blo 1447543 3479039 := bstep (se 1 (by rfl) ⟨2609279, by rfl⟩ : syracuseStep 3479039 = 5218559) B5218559
theorem B4888079 : Blo 1447543 4888079 := bstep (se 1 (by rfl) ⟨3666059, by rfl⟩ : syracuseStep 4888079 = 7332119) B7332119
theorem B10434143 : Blo 1447543 10434143 := bstep (se 1 (by rfl) ⟨7825607, by rfl⟩ : syracuseStep 10434143 = 15651215) B15651215
theorem B2061931 : Blo 1447543 2061931 := bstep (se 1 (by rfl) ⟨1546448, by rfl⟩ : syracuseStep 2061931 = 3092897) B3092897
theorem B1447615 : Blo 1447543 1447615 := bstep (se 1 (by rfl) ⟨1085711, by rfl⟩ : syracuseStep 1447615 = 2171423) B2171423
theorem B4642523 : Blo 1447543 4642523 := bstep (se 1 (by rfl) ⟨3481892, by rfl⟩ : syracuseStep 4642523 = 6963785) B6963785
theorem B1447655 : Blo 1447543 1447655 := bstep (se 1 (by rfl) ⟨1085741, by rfl⟩ : syracuseStep 1447655 = 2171483) B2171483
theorem B1832807 : Blo 1447543 1832807 := bstep (se 1 (by rfl) ⟨1374605, by rfl⟩ : syracuseStep 1832807 = 2749211) B2749211
theorem B8255357 : Blo 1447543 8255357 := bstep (se 3 (by rfl) ⟨1547879, by rfl⟩ : syracuseStep 8255357 = 3095759) B3095759
theorem B1546175 : Blo 1447543 1546175 := bstep (se 1 (by rfl) ⟨1159631, by rfl⟩ : syracuseStep 1546175 = 2319263) B2319263
theorem B1447999 : Blo 1447543 1447999 := bstep (se 1 (by rfl) ⟨1085999, by rfl⟩ : syracuseStep 1447999 = 2171999) B2171999
theorem B1448039 : Blo 1447543 1448039 := bstep (se 1 (by rfl) ⟨1086029, by rfl⟩ : syracuseStep 1448039 = 2172059) B2172059
theorem B11753855 : Blo 1447543 11753855 := bstep (se 1 (by rfl) ⟨8815391, by rfl⟩ : syracuseStep 11753855 = 17630783) B17630783
theorem B1448347 : Blo 1447543 1448347 := bstep (se 1 (by rfl) ⟨1086260, by rfl⟩ : syracuseStep 1448347 = 2172521) B2172521
theorem B3094939 : Blo 1447543 3094939 := bstep (se 1 (by rfl) ⟨2321204, by rfl⟩ : syracuseStep 3094939 = 4642409) B4642409
theorem B1448431 : Blo 1447543 1448431 := bstep (se 1 (by rfl) ⟨1086323, by rfl⟩ : syracuseStep 1448431 = 2172647) B2172647
theorem B1448495 : Blo 1447543 1448495 := bstep (se 1 (by rfl) ⟨1086371, by rfl⟩ : syracuseStep 1448495 = 2172743) B2172743
theorem B4889159 : Blo 1447543 4889159 := bstep (se 1 (by rfl) ⟨3666869, by rfl⟩ : syracuseStep 4889159 = 7333739) B7333739
theorem B12540521 : Blo 1447543 12540521 := bstep (se 2 (by rfl) ⟨4702695, by rfl⟩ : syracuseStep 12540521 = 9405391) B9405391
theorem B25082563 : Blo 1447543 25082563 := bstep (se 1 (by rfl) ⟨18811922, by rfl⟩ : syracuseStep 25082563 = 37623845) B37623845
theorem B4889321 : Blo 1447543 4889321 := bstep (se 2 (by rfl) ⟨1833495, by rfl⟩ : syracuseStep 4889321 = 3666991) B3666991
theorem B1628923 : Blo 1447543 1628923 := bstep (se 1 (by rfl) ⟨1221692, by rfl⟩ : syracuseStep 1628923 = 2443385) B2443385
theorem B7428871 : Blo 1447543 7428871 := bstep (se 1 (by rfl) ⟨5571653, by rfl⟩ : syracuseStep 7428871 = 11143307) B11143307
theorem B2751239 : Blo 1447543 2751239 := bstep (se 1 (by rfl) ⟨2063429, by rfl⟩ : syracuseStep 2751239 = 4126859) B4126859
theorem B1448767 : Blo 1447543 1448767 := bstep (se 1 (by rfl) ⟨1086575, by rfl⟩ : syracuseStep 1448767 = 2173151) B2173151
theorem B1448807 : Blo 1447543 1448807 := bstep (se 1 (by rfl) ⟨1086605, by rfl⟩ : syracuseStep 1448807 = 2173211) B2173211
theorem B3259259 : Blo 1447543 3259259 := bstep (se 1 (by rfl) ⟨2444444, by rfl⟩ : syracuseStep 3259259 = 4888889) B4888889
theorem B20880281 : Blo 1447543 20880281 := bstep (se 2 (by rfl) ⟨7830105, by rfl⟩ : syracuseStep 20880281 = 15660211) B15660211
theorem B1448895 : Blo 1447543 1448895 := bstep (se 1 (by rfl) ⟨1086671, by rfl⟩ : syracuseStep 1448895 = 2173343) B2173343
theorem B1449023 : Blo 1447543 1449023 := bstep (se 1 (by rfl) ⟨1086767, by rfl⟩ : syracuseStep 1449023 = 2173535) B2173535
theorem B1449243 : Blo 1447543 1449243 := bstep (se 1 (by rfl) ⟨1086932, by rfl⟩ : syracuseStep 1449243 = 2173865) B2173865
theorem B1449263 : Blo 1447543 1449263 := bstep (se 1 (by rfl) ⟨1086947, by rfl⟩ : syracuseStep 1449263 = 2173895) B2173895
theorem B1449343 : Blo 1447543 1449343 := bstep (se 1 (by rfl) ⟨1087007, by rfl⟩ : syracuseStep 1449343 = 2174015) B2174015
theorem B1547743 : Blo 1447543 1547743 := bstep (se 1 (by rfl) ⟨1160807, by rfl⟩ : syracuseStep 1547743 = 2321615) B2321615
theorem B4890131 : Blo 1447543 4890131 := bstep (se 1 (by rfl) ⟨3667598, by rfl⟩ : syracuseStep 4890131 = 7335197) B7335197
theorem B1449503 : Blo 1447543 1449503 := bstep (se 1 (by rfl) ⟨1087127, by rfl⟩ : syracuseStep 1449503 = 2174255) B2174255
theorem B5955767 : Blo 1447543 5955767 := bstep (se 1 (by rfl) ⟨4466825, by rfl⟩ : syracuseStep 5955767 = 8933651) B8933651
theorem B23495123 : Blo 1447543 23495123 := bstep (se 1 (by rfl) ⟨17621342, by rfl⟩ : syracuseStep 23495123 = 35242685) B35242685
theorem B2171375 : Blo 1447543 2171375 := bstep (se 1 (by rfl) ⟨1628531, by rfl⟩ : syracuseStep 2171375 = 3257063) B3257063
theorem B8815097 : Blo 1447543 8815097 := bstep (se 2 (by rfl) ⟨3305661, by rfl⟩ : syracuseStep 8815097 = 6611323) B6611323
theorem B6185555 : Blo 1447543 6185555 := bstep (se 1 (by rfl) ⟨4639166, by rfl⟩ : syracuseStep 6185555 = 9278333) B9278333
theorem B3261419 : Blo 1447543 3261419 := bstep (se 1 (by rfl) ⟨2446064, by rfl⟩ : syracuseStep 3261419 = 4892129) B4892129
theorem B2171897 : Blo 1447543 2171897 := bstep (se 2 (by rfl) ⟨814461, by rfl⟩ : syracuseStep 2171897 = 1628923) B1628923
theorem B2319359 : Blo 1447543 2319359 := bstep (se 1 (by rfl) ⟨1739519, by rfl⟩ : syracuseStep 2319359 = 3479039) B3479039
theorem B9905161 : Blo 1447543 9905161 := bstep (se 2 (by rfl) ⟨3714435, by rfl⟩ : syracuseStep 9905161 = 7428871) B7428871
theorem B13928183 : Blo 1447543 13928183 := bstep (se 1 (by rfl) ⟨10446137, by rfl⟩ : syracuseStep 13928183 = 20892275) B20892275
theorem B2172839 : Blo 1447543 2172839 := bstep (se 1 (by rfl) ⟨1629629, by rfl⟩ : syracuseStep 2172839 = 3259259) B3259259
theorem B13920187 : Blo 1447543 13920187 := bstep (se 1 (by rfl) ⟨10440140, by rfl⟩ : syracuseStep 13920187 = 20880281) B20880281
theorem B7334225 : Blo 1447543 7334225 := bstep (se 2 (by rfl) ⟨2750334, by rfl⟩ : syracuseStep 7334225 = 5500669) B5500669
theorem B4123133 : Blo 1447543 4123133 := bstep (se 3 (by rfl) ⟨773087, by rfl⟩ : syracuseStep 4123133 = 1546175) B1546175
theorem B3664723 : Blo 1447543 3664723 := bstep (se 1 (by rfl) ⟨2748542, by rfl⟩ : syracuseStep 3664723 = 5497085) B5497085
theorem B5876603 : Blo 1447543 5876603 := bstep (se 1 (by rfl) ⟨4407452, by rfl⟩ : syracuseStep 5876603 = 8814905) B8814905
theorem B8252441 : Blo 1447543 8252441 := bstep (se 2 (by rfl) ⟨3094665, by rfl⟩ : syracuseStep 8252441 = 6189331) B6189331
theorem B2174159 : Blo 1447543 2174159 := bstep (se 1 (by rfl) ⟨1630619, by rfl⟩ : syracuseStep 2174159 = 3261239) B3261239
theorem B19066369 : Blo 1447543 19066369 := bstep (se 2 (by rfl) ⟨7149888, by rfl⟩ : syracuseStep 19066369 = 14299777) B14299777
theorem B33443417 : Blo 1447543 33443417 := bstep (se 2 (by rfl) ⟨12541281, by rfl⟩ : syracuseStep 33443417 = 25082563) B25082563
theorem B8253191 : Blo 1447543 8253191 := bstep (se 1 (by rfl) ⟨6189893, by rfl⟩ : syracuseStep 8253191 = 12379787) B12379787
theorem B27824381 : Blo 1447543 27824381 := bstep (se 3 (by rfl) ⟨5217071, by rfl⟩ : syracuseStep 27824381 = 10434143) B10434143
theorem B7835903 : Blo 1447543 7835903 := bstep (se 1 (by rfl) ⟨5876927, by rfl⟩ : syracuseStep 7835903 = 11753855) B11753855
theorem B8360347 : Blo 1447543 8360347 := bstep (se 1 (by rfl) ⟨6270260, by rfl⟩ : syracuseStep 8360347 = 12540521) B12540521
theorem B4125127 : Blo 1447543 4125127 := bstep (se 1 (by rfl) ⟨3093845, by rfl⟩ : syracuseStep 4125127 = 6187691) B6187691
theorem B7827947 : Blo 1447543 7827947 := bstep (se 1 (by rfl) ⟨5870960, by rfl⟩ : syracuseStep 7827947 = 11741921) B11741921
theorem B3478241 : Blo 1447543 3478241 := bstep (se 2 (by rfl) ⟨1304340, by rfl⟩ : syracuseStep 3478241 = 2608681) B2608681
theorem B2978587 : Blo 1447543 2978587 := bstep (se 1 (by rfl) ⟨2233940, by rfl⟩ : syracuseStep 2978587 = 4467881) B4467881
theorem B2749241 : Blo 1447543 2749241 := bstep (se 2 (by rfl) ⟨1030965, by rfl⟩ : syracuseStep 2749241 = 2061931) B2061931
theorem B4887485 : Blo 1447543 4887485 := bstep (se 3 (by rfl) ⟨916403, by rfl⟩ : syracuseStep 4887485 = 1832807) B1832807
theorem B3257567 : Blo 1447543 3257567 := bstep (se 1 (by rfl) ⟨2443175, by rfl⟩ : syracuseStep 3257567 = 4886351) B4886351
theorem B3257657 : Blo 1447543 3257657 := bstep (se 2 (by rfl) ⟨1221621, by rfl⟩ : syracuseStep 3257657 = 2443243) B2443243
theorem B3257711 : Blo 1447543 3257711 := bstep (se 1 (by rfl) ⟨2443283, by rfl⟩ : syracuseStep 3257711 = 4886567) B4886567
theorem B26432963 : Blo 1447543 26432963 := bstep (se 1 (by rfl) ⟨19824722, by rfl⟩ : syracuseStep 26432963 = 39649445) B39649445
theorem B5502431 : Blo 1447543 5502431 := bstep (se 1 (by rfl) ⟨4126823, by rfl⟩ : syracuseStep 5502431 = 8253647) B8253647
theorem B96581099 : Blo 1447543 96581099 := bstep (se 1 (by rfl) ⟨72435824, by rfl⟩ : syracuseStep 96581099 = 144871649) B144871649
theorem B3257855 : Blo 1447543 3257855 := bstep (se 1 (by rfl) ⟨2443391, by rfl⟩ : syracuseStep 3257855 = 4886783) B4886783
theorem B2750107 : Blo 1447543 2750107 := bstep (se 1 (by rfl) ⟨2062580, by rfl⟩ : syracuseStep 2750107 = 4125161) B4125161
theorem B17610443 : Blo 1447543 17610443 := bstep (se 1 (by rfl) ⟨13207832, by rfl⟩ : syracuseStep 17610443 = 26415665) B26415665
theorem B3258143 : Blo 1447543 3258143 := bstep (se 1 (by rfl) ⟨2443607, by rfl⟩ : syracuseStep 3258143 = 4887215) B4887215
theorem B9279305 : Blo 1447543 9279305 := bstep (se 2 (by rfl) ⟨3479739, by rfl⟩ : syracuseStep 9279305 = 6959479) B6959479
theorem B4126585 : Blo 1447543 4126585 := bstep (se 2 (by rfl) ⟨1547469, by rfl⟩ : syracuseStep 4126585 = 3094939) B3094939
theorem B1832863 : Blo 1447543 1832863 := bstep (se 1 (by rfl) ⟨1374647, by rfl⟩ : syracuseStep 1832863 = 2749295) B2749295
theorem B4888511 : Blo 1447543 4888511 := bstep (se 1 (by rfl) ⟨3666383, by rfl⟩ : syracuseStep 4888511 = 7332767) B7332767
theorem B3258431 : Blo 1447543 3258431 := bstep (se 1 (by rfl) ⟨2443823, by rfl⟩ : syracuseStep 3258431 = 4887647) B4887647
theorem B1448027 : Blo 1447543 1448027 := bstep (se 1 (by rfl) ⟨1086020, by rfl⟩ : syracuseStep 1448027 = 2172041) B2172041
theorem B1448219 : Blo 1447543 1448219 := bstep (se 1 (by rfl) ⟨1086164, by rfl⟩ : syracuseStep 1448219 = 2172329) B2172329
theorem B3258719 : Blo 1447543 3258719 := bstep (se 1 (by rfl) ⟨2444039, by rfl⟩ : syracuseStep 3258719 = 4888079) B4888079
theorem B1448415 : Blo 1447543 1448415 := bstep (se 1 (by rfl) ⟨1086311, by rfl⟩ : syracuseStep 1448415 = 2172623) B2172623
theorem B3095015 : Blo 1447543 3095015 := bstep (se 1 (by rfl) ⟨2321261, by rfl⟩ : syracuseStep 3095015 = 4642523) B4642523
theorem B5503571 : Blo 1447543 5503571 := bstep (se 1 (by rfl) ⟨4127678, by rfl⟩ : syracuseStep 5503571 = 8255357) B8255357
theorem B1448831 : Blo 1447543 1448831 := bstep (se 1 (by rfl) ⟨1086623, by rfl⟩ : syracuseStep 1448831 = 2173247) B2173247
theorem B1448943 : Blo 1447543 1448943 := bstep (se 1 (by rfl) ⟨1086707, by rfl⟩ : syracuseStep 1448943 = 2173415) B2173415
theorem B3259439 : Blo 1447543 3259439 := bstep (se 1 (by rfl) ⟨2444579, by rfl⟩ : syracuseStep 3259439 = 4889159) B4889159
theorem B1449063 : Blo 1447543 1449063 := bstep (se 1 (by rfl) ⟨1086797, by rfl⟩ : syracuseStep 1449063 = 2173595) B2173595
theorem B3259547 : Blo 1447543 3259547 := bstep (se 1 (by rfl) ⟨2444660, by rfl⟩ : syracuseStep 3259547 = 4889321) B4889321
theorem B1834159 : Blo 1447543 1834159 := bstep (se 1 (by rfl) ⟨1375619, by rfl⟩ : syracuseStep 1834159 = 2751239) B2751239
theorem B59432129 : Blo 1447543 59432129 := bstep (se 2 (by rfl) ⟨22287048, by rfl⟩ : syracuseStep 59432129 = 44574097) B44574097
theorem B20094155 : Blo 1447543 20094155 := bstep (se 1 (by rfl) ⟨15070616, by rfl⟩ : syracuseStep 20094155 = 30141233) B30141233
theorem B2063657 : Blo 1447543 2063657 := bstep (se 2 (by rfl) ⟨773871, by rfl⟩ : syracuseStep 2063657 = 1547743) B1547743
theorem B44604755 : Blo 1447543 44604755 := bstep (se 1 (by rfl) ⟨33453566, by rfl⟩ : syracuseStep 44604755 = 66907133) B66907133
theorem B52878905 : Blo 1447543 52878905 := bstep (se 2 (by rfl) ⟨19829589, by rfl⟩ : syracuseStep 52878905 = 39659179) B39659179
theorem B3260087 : Blo 1447543 3260087 := bstep (se 1 (by rfl) ⟨2445065, by rfl⟩ : syracuseStep 3260087 = 4890131) B4890131
theorem B39665537 : Blo 1447543 39665537 := bstep (se 2 (by rfl) ⟨14874576, by rfl⟩ : syracuseStep 39665537 = 29749153) B29749153
theorem B3260411 : Blo 1447543 3260411 := bstep (se 1 (by rfl) ⟨2445308, by rfl⟩ : syracuseStep 3260411 = 4890617) B4890617
theorem B15663415 : Blo 1447543 15663415 := bstep (se 1 (by rfl) ⟨11747561, by rfl⟩ : syracuseStep 15663415 = 23495123) B23495123
theorem B5218631 : Blo 1447543 5218631 := bstep (se 1 (by rfl) ⟨3913973, by rfl⟩ : syracuseStep 5218631 = 7827947) B7827947
theorem B2171711 : Blo 1447543 2171711 := bstep (se 1 (by rfl) ⟨1628783, by rfl⟩ : syracuseStep 2171711 = 3257567) B3257567
theorem B2171771 : Blo 1447543 2171771 := bstep (se 1 (by rfl) ⟨1628828, by rfl⟩ : syracuseStep 2171771 = 3257657) B3257657
theorem B2171807 : Blo 1447543 2171807 := bstep (se 1 (by rfl) ⟨1628855, by rfl⟩ : syracuseStep 2171807 = 3257711) B3257711
theorem B17621975 : Blo 1447543 17621975 := bstep (se 1 (by rfl) ⟨13216481, by rfl⟩ : syracuseStep 17621975 = 26432963) B26432963
theorem B2171903 : Blo 1447543 2171903 := bstep (se 1 (by rfl) ⟨1628927, by rfl⟩ : syracuseStep 2171903 = 3257855) B3257855
theorem B11740295 : Blo 1447543 11740295 := bstep (se 1 (by rfl) ⟨8805221, by rfl⟩ : syracuseStep 11740295 = 17610443) B17610443
theorem B2172095 : Blo 1447543 2172095 := bstep (se 1 (by rfl) ⟨1629071, by rfl⟩ : syracuseStep 2172095 = 3258143) B3258143
theorem B6186203 : Blo 1447543 6186203 := bstep (se 1 (by rfl) ⟨4639652, by rfl⟩ : syracuseStep 6186203 = 9279305) B9279305
theorem B13206881 : Blo 1447543 13206881 := bstep (se 2 (by rfl) ⟨4952580, by rfl⟩ : syracuseStep 13206881 = 9905161) B9905161
theorem B2172287 : Blo 1447543 2172287 := bstep (se 1 (by rfl) ⟨1629215, by rfl⟩ : syracuseStep 2172287 = 3258431) B3258431
theorem B2172479 : Blo 1447543 2172479 := bstep (se 1 (by rfl) ⟨1629359, by rfl⟩ : syracuseStep 2172479 = 3258719) B3258719
theorem B3917735 : Blo 1447543 3917735 := bstep (se 1 (by rfl) ⟨2938301, by rfl⟩ : syracuseStep 3917735 = 5876603) B5876603
theorem B9275309 : Blo 1447543 9275309 := bstep (se 3 (by rfl) ⟨1739120, by rfl⟩ : syracuseStep 9275309 = 3478241) B3478241
theorem B25421825 : Blo 1447543 25421825 := bstep (se 2 (by rfl) ⟨9533184, by rfl⟩ : syracuseStep 25421825 = 19066369) B19066369
theorem B2172959 : Blo 1447543 2172959 := bstep (se 1 (by rfl) ⟨1629719, by rfl⟩ : syracuseStep 2172959 = 3259439) B3259439
theorem B2173031 : Blo 1447543 2173031 := bstep (se 1 (by rfl) ⟨1629773, by rfl⟩ : syracuseStep 2173031 = 3259547) B3259547
theorem B13396103 : Blo 1447543 13396103 := bstep (se 1 (by rfl) ⟨10047077, by rfl⟩ : syracuseStep 13396103 = 20094155) B20094155
theorem B35252603 : Blo 1447543 35252603 := bstep (se 1 (by rfl) ⟨26439452, by rfl⟩ : syracuseStep 35252603 = 52878905) B52878905
theorem B2173391 : Blo 1447543 2173391 := bstep (se 1 (by rfl) ⟨1630043, by rfl⟩ : syracuseStep 2173391 = 3260087) B3260087
theorem B2443817 : Blo 1447543 2443817 := bstep (se 2 (by rfl) ⟨916431, by rfl⟩ : syracuseStep 2443817 = 1832863) B1832863
theorem B2173607 : Blo 1447543 2173607 := bstep (se 1 (by rfl) ⟨1630205, by rfl⟩ : syracuseStep 2173607 = 3260411) B3260411
theorem B18549587 : Blo 1447543 18549587 := bstep (se 1 (by rfl) ⟨13912190, by rfl⟩ : syracuseStep 18549587 = 27824381) B27824381
theorem B5876731 : Blo 1447543 5876731 := bstep (se 1 (by rfl) ⟨4407548, by rfl⟩ : syracuseStep 5876731 = 8815097) B8815097
theorem B4123703 : Blo 1447543 4123703 := bstep (se 1 (by rfl) ⟨3092777, by rfl⟩ : syracuseStep 4123703 = 6185555) B6185555
theorem B5500169 : Blo 1447543 5500169 := bstep (se 2 (by rfl) ⟨2062563, by rfl⟩ : syracuseStep 5500169 = 4125127) B4125127
theorem B2174279 : Blo 1447543 2174279 := bstep (se 1 (by rfl) ⟨1630709, by rfl⟩ : syracuseStep 2174279 = 3261419) B3261419
theorem B4886297 : Blo 1447543 4886297 := bstep (se 2 (by rfl) ⟨1832361, by rfl⟩ : syracuseStep 4886297 = 3664723) B3664723
theorem B9285455 : Blo 1447543 9285455 := bstep (se 1 (by rfl) ⟨6964091, by rfl⟩ : syracuseStep 9285455 = 13928183) B13928183
theorem B8253373 : Blo 1447543 8253373 := bstep (se 3 (by rfl) ⟨1547507, by rfl⟩ : syracuseStep 8253373 = 3095015) B3095015
theorem B2445545 : Blo 1447543 2445545 := bstep (se 2 (by rfl) ⟨917079, by rfl⟩ : syracuseStep 2445545 = 1834159) B1834159
theorem B2748755 : Blo 1447543 2748755 := bstep (se 1 (by rfl) ⟨2061566, by rfl⟩ : syracuseStep 2748755 = 4123133) B4123133
theorem B5501627 : Blo 1447543 5501627 := bstep (se 1 (by rfl) ⟨4126220, by rfl⟩ : syracuseStep 5501627 = 8252441) B8252441
theorem B39621419 : Blo 1447543 39621419 := bstep (se 1 (by rfl) ⟨29716064, by rfl⟩ : syracuseStep 39621419 = 59432129) B59432129
theorem B3666809 : Blo 1447543 3666809 := bstep (se 2 (by rfl) ⟨1375053, by rfl⟩ : syracuseStep 3666809 = 2750107) B2750107
theorem B22295611 : Blo 1447543 22295611 := bstep (se 1 (by rfl) ⟨16721708, by rfl⟩ : syracuseStep 22295611 = 33443417) B33443417
theorem B5502113 : Blo 1447543 5502113 := bstep (se 2 (by rfl) ⟨2063292, by rfl⟩ : syracuseStep 5502113 = 4126585) B4126585
theorem B5502127 : Blo 1447543 5502127 := bstep (se 1 (by rfl) ⟨4126595, by rfl⟩ : syracuseStep 5502127 = 8253191) B8253191
theorem B18560249 : Blo 1447543 18560249 := bstep (se 2 (by rfl) ⟨6960093, by rfl⟩ : syracuseStep 18560249 = 13920187) B13920187
theorem B3970511 : Blo 1447543 3970511 := bstep (se 1 (by rfl) ⟨2977883, by rfl⟩ : syracuseStep 3970511 = 5955767) B5955767
theorem B5223935 : Blo 1447543 5223935 := bstep (se 1 (by rfl) ⟨3917951, by rfl⟩ : syracuseStep 5223935 = 7835903) B7835903
theorem B1447583 : Blo 1447543 1447583 := bstep (se 1 (by rfl) ⟨1085687, by rfl⟩ : syracuseStep 1447583 = 2171375) B2171375
theorem B11147129 : Blo 1447543 11147129 := bstep (se 2 (by rfl) ⟨4180173, by rfl⟩ : syracuseStep 11147129 = 8360347) B8360347
theorem B3258323 : Blo 1447543 3258323 := bstep (se 1 (by rfl) ⟨2443742, by rfl⟩ : syracuseStep 3258323 = 4887485) B4887485
theorem B1447931 : Blo 1447543 1447931 := bstep (se 1 (by rfl) ⟨1085948, by rfl⟩ : syracuseStep 1447931 = 2171897) B2171897
theorem B5503085 : Blo 1447543 5503085 := bstep (se 3 (by rfl) ⟨1031828, by rfl⟩ : syracuseStep 5503085 = 2063657) B2063657
theorem B3668287 : Blo 1447543 3668287 := bstep (se 1 (by rfl) ⟨2751215, by rfl⟩ : syracuseStep 3668287 = 5502431) B5502431
theorem B64387399 : Blo 1447543 64387399 := bstep (se 1 (by rfl) ⟨48290549, by rfl⟩ : syracuseStep 64387399 = 96581099) B96581099
theorem B3971449 : Blo 1447543 3971449 := bstep (se 2 (by rfl) ⟨1489293, by rfl⟩ : syracuseStep 3971449 = 2978587) B2978587
theorem B1448559 : Blo 1447543 1448559 := bstep (se 1 (by rfl) ⟨1086419, by rfl⟩ : syracuseStep 1448559 = 2172839) B2172839
theorem B3259007 : Blo 1447543 3259007 := bstep (se 1 (by rfl) ⟨2444255, by rfl⟩ : syracuseStep 3259007 = 4888511) B4888511
theorem B4889483 : Blo 1447543 4889483 := bstep (se 1 (by rfl) ⟨3667112, by rfl⟩ : syracuseStep 4889483 = 7334225) B7334225
theorem B3669047 : Blo 1447543 3669047 := bstep (se 1 (by rfl) ⟨2751785, by rfl⟩ : syracuseStep 3669047 = 5503571) B5503571
theorem B1449439 : Blo 1447543 1449439 := bstep (se 1 (by rfl) ⟨1087079, by rfl⟩ : syracuseStep 1449439 = 2174159) B2174159
theorem B7331309 : Blo 1447543 7331309 := bstep (se 3 (by rfl) ⟨1374620, by rfl⟩ : syracuseStep 7331309 = 2749241) B2749241
theorem B29736503 : Blo 1447543 29736503 := bstep (se 1 (by rfl) ⟨22302377, by rfl⟩ : syracuseStep 29736503 = 44604755) B44604755
theorem B26443691 : Blo 1447543 26443691 := bstep (se 1 (by rfl) ⟨19832768, by rfl⟩ : syracuseStep 26443691 = 39665537) B39665537
theorem B6184957 : Blo 1447543 6184957 := bstep (se 3 (by rfl) ⟨1159679, by rfl⟩ : syracuseStep 6184957 = 2319359) B2319359
theorem B1630363 : Blo 1447543 1630363 := bstep (se 1 (by rfl) ⟨1222772, by rfl⟩ : syracuseStep 1630363 = 2445545) B2445545
theorem B4891049 : Blo 1447543 4891049 := bstep (se 2 (by rfl) ⟨1834143, by rfl⟩ : syracuseStep 4891049 = 3668287) B3668287
theorem B2647007 : Blo 1447543 2647007 := bstep (se 1 (by rfl) ⟨1985255, by rfl⟩ : syracuseStep 2647007 = 3970511) B3970511
theorem B3482623 : Blo 1447543 3482623 := bstep (se 1 (by rfl) ⟨2611967, by rfl⟩ : syracuseStep 3482623 = 5223935) B5223935
theorem B7431419 : Blo 1447543 7431419 := bstep (se 1 (by rfl) ⟨5573564, by rfl⟩ : syracuseStep 7431419 = 11147129) B11147129
theorem B2172215 : Blo 1447543 2172215 := bstep (se 1 (by rfl) ⟨1629161, by rfl⟩ : syracuseStep 2172215 = 3258323) B3258323
theorem B8930735 : Blo 1447543 8930735 := bstep (se 1 (by rfl) ⟨6698051, by rfl⟩ : syracuseStep 8930735 = 13396103) B13396103
theorem B2172671 : Blo 1447543 2172671 := bstep (se 1 (by rfl) ⟨1629503, by rfl⟩ : syracuseStep 2172671 = 3259007) B3259007
theorem B46991933 : Blo 1447543 46991933 := bstep (se 3 (by rfl) ⟨8810987, by rfl⟩ : syracuseStep 46991933 = 17621975) B17621975
theorem B11004497 : Blo 1447543 11004497 := bstep (se 2 (by rfl) ⟨4126686, by rfl⟩ : syracuseStep 11004497 = 8253373) B8253373
theorem B20884553 : Blo 1447543 20884553 := bstep (se 2 (by rfl) ⟨7831707, by rfl⟩ : syracuseStep 20884553 = 15663415) B15663415
theorem B26414279 : Blo 1447543 26414279 := bstep (se 1 (by rfl) ⟨19810709, by rfl⟩ : syracuseStep 26414279 = 39621419) B39621419
theorem B2444539 : Blo 1447543 2444539 := bstep (se 1 (by rfl) ⟨1833404, by rfl⟩ : syracuseStep 2444539 = 3666809) B3666809
theorem B7826863 : Blo 1447543 7826863 := bstep (se 1 (by rfl) ⟨5870147, by rfl⟩ : syracuseStep 7826863 = 11740295) B11740295
theorem B4124135 : Blo 1447543 4124135 := bstep (se 1 (by rfl) ⟨3093101, by rfl⟩ : syracuseStep 4124135 = 6186203) B6186203
theorem B12373499 : Blo 1447543 12373499 := bstep (se 1 (by rfl) ⟨9280124, by rfl⟩ : syracuseStep 12373499 = 18560249) B18560249
theorem B7336169 : Blo 1447543 7336169 := bstep (se 2 (by rfl) ⟨2751063, by rfl⟩ : syracuseStep 7336169 = 5502127) B5502127
theorem B12366391 : Blo 1447543 12366391 := bstep (se 1 (by rfl) ⟨9274793, by rfl⟩ : syracuseStep 12366391 = 18549587) B18549587
theorem B21181061 : Blo 1447543 21181061 := bstep (se 4 (by rfl) ⟨1985724, by rfl⟩ : syracuseStep 21181061 = 3971449) B3971449
theorem B2749135 : Blo 1447543 2749135 := bstep (se 1 (by rfl) ⟨2061851, by rfl⟩ : syracuseStep 2749135 = 4123703) B4123703
theorem B2446031 : Blo 1447543 2446031 := bstep (se 1 (by rfl) ⟨1834523, by rfl⟩ : syracuseStep 2446031 = 3669047) B3669047
theorem B3666779 : Blo 1447543 3666779 := bstep (se 1 (by rfl) ⟨2750084, by rfl⟩ : syracuseStep 3666779 = 5500169) B5500169
theorem B24761213 : Blo 1447543 24761213 := bstep (se 3 (by rfl) ⟨4642727, by rfl⟩ : syracuseStep 24761213 = 9285455) B9285455
theorem B4887539 : Blo 1447543 4887539 := bstep (se 1 (by rfl) ⟨3665654, by rfl⟩ : syracuseStep 4887539 = 7331309) B7331309
theorem B3257531 : Blo 1447543 3257531 := bstep (se 1 (by rfl) ⟨2443148, by rfl⟩ : syracuseStep 3257531 = 4886297) B4886297
theorem B8246609 : Blo 1447543 8246609 := bstep (se 2 (by rfl) ⟨3092478, by rfl⟩ : syracuseStep 8246609 = 6184957) B6184957
theorem B3479087 : Blo 1447543 3479087 := bstep (se 1 (by rfl) ⟨2609315, by rfl⟩ : syracuseStep 3479087 = 5218631) B5218631
theorem B85849865 : Blo 1447543 85849865 := bstep (se 2 (by rfl) ⟨32193699, by rfl⟩ : syracuseStep 85849865 = 64387399) B64387399
theorem B3667751 : Blo 1447543 3667751 := bstep (se 1 (by rfl) ⟨2750813, by rfl⟩ : syracuseStep 3667751 = 5501627) B5501627
theorem B1447807 : Blo 1447543 1447807 := bstep (se 1 (by rfl) ⟨1085855, by rfl⟩ : syracuseStep 1447807 = 2171711) B2171711
theorem B1447847 : Blo 1447543 1447847 := bstep (se 1 (by rfl) ⟨1085885, by rfl⟩ : syracuseStep 1447847 = 2171771) B2171771
theorem B1447871 : Blo 1447543 1447871 := bstep (se 1 (by rfl) ⟨1085903, by rfl⟩ : syracuseStep 1447871 = 2171807) B2171807
theorem B1447935 : Blo 1447543 1447935 := bstep (se 1 (by rfl) ⟨1085951, by rfl⟩ : syracuseStep 1447935 = 2171903) B2171903
theorem B3668075 : Blo 1447543 3668075 := bstep (se 1 (by rfl) ⟨2751056, by rfl⟩ : syracuseStep 3668075 = 5502113) B5502113
theorem B1448063 : Blo 1447543 1448063 := bstep (se 1 (by rfl) ⟨1086047, by rfl⟩ : syracuseStep 1448063 = 2172095) B2172095
theorem B7330013 : Blo 1447543 7330013 := bstep (se 3 (by rfl) ⟨1374377, by rfl⟩ : syracuseStep 7330013 = 2748755) B2748755
theorem B8804587 : Blo 1447543 8804587 := bstep (se 1 (by rfl) ⟨6603440, by rfl⟩ : syracuseStep 8804587 = 13206881) B13206881
theorem B1448191 : Blo 1447543 1448191 := bstep (se 1 (by rfl) ⟨1086143, by rfl⟩ : syracuseStep 1448191 = 2172287) B2172287
theorem B1448319 : Blo 1447543 1448319 := bstep (se 1 (by rfl) ⟨1086239, by rfl⟩ : syracuseStep 1448319 = 2172479) B2172479
theorem B2611823 : Blo 1447543 2611823 := bstep (se 1 (by rfl) ⟨1958867, by rfl⟩ : syracuseStep 2611823 = 3917735) B3917735
theorem B6183539 : Blo 1447543 6183539 := bstep (se 1 (by rfl) ⟨4637654, by rfl⟩ : syracuseStep 6183539 = 9275309) B9275309
theorem B16947883 : Blo 1447543 16947883 := bstep (se 1 (by rfl) ⟨12710912, by rfl⟩ : syracuseStep 16947883 = 25421825) B25421825
theorem B1448639 : Blo 1447543 1448639 := bstep (se 1 (by rfl) ⟨1086479, by rfl⟩ : syracuseStep 1448639 = 2172959) B2172959
theorem B1448687 : Blo 1447543 1448687 := bstep (se 1 (by rfl) ⟨1086515, by rfl⟩ : syracuseStep 1448687 = 2173031) B2173031
theorem B3668723 : Blo 1447543 3668723 := bstep (se 1 (by rfl) ⟨2751542, by rfl⟩ : syracuseStep 3668723 = 5503085) B5503085
theorem B29727481 : Blo 1447543 29727481 := bstep (se 2 (by rfl) ⟨11147805, by rfl⟩ : syracuseStep 29727481 = 22295611) B22295611
theorem B23501735 : Blo 1447543 23501735 := bstep (se 1 (by rfl) ⟨17626301, by rfl⟩ : syracuseStep 23501735 = 35252603) B35252603
theorem B1448927 : Blo 1447543 1448927 := bstep (se 1 (by rfl) ⟨1086695, by rfl⟩ : syracuseStep 1448927 = 2173391) B2173391
theorem B1629211 : Blo 1447543 1629211 := bstep (se 1 (by rfl) ⟨1221908, by rfl⟩ : syracuseStep 1629211 = 2443817) B2443817
theorem B1449071 : Blo 1447543 1449071 := bstep (se 1 (by rfl) ⟨1086803, by rfl⟩ : syracuseStep 1449071 = 2173607) B2173607
theorem B3259655 : Blo 1447543 3259655 := bstep (se 1 (by rfl) ⟨2444741, by rfl⟩ : syracuseStep 3259655 = 4889483) B4889483
theorem B1449519 : Blo 1447543 1449519 := bstep (se 1 (by rfl) ⟨1087139, by rfl⟩ : syracuseStep 1449519 = 2174279) B2174279
theorem B19824335 : Blo 1447543 19824335 := bstep (se 1 (by rfl) ⟨14868251, by rfl⟩ : syracuseStep 19824335 = 29736503) B29736503
theorem B17629127 : Blo 1447543 17629127 := bstep (se 1 (by rfl) ⟨13221845, by rfl⟩ : syracuseStep 17629127 = 26443691) B26443691
theorem B31342565 : Blo 1447543 31342565 := bstep (se 4 (by rfl) ⟨2938365, by rfl⟩ : syracuseStep 31342565 = 5876731) B5876731
theorem B4890779 : Blo 1447543 4890779 := bstep (se 1 (by rfl) ⟨3668084, by rfl⟩ : syracuseStep 4890779 = 7336169) B7336169
theorem B3260699 : Blo 1447543 3260699 := bstep (se 1 (by rfl) ⟨2445524, by rfl⟩ : syracuseStep 3260699 = 4891049) B4891049
theorem B11739449 : Blo 1447543 11739449 := bstep (se 2 (by rfl) ⟨4402293, by rfl⟩ : syracuseStep 11739449 = 8804587) B8804587
theorem B1630687 : Blo 1447543 1630687 := bstep (se 1 (by rfl) ⟨1223015, by rfl⟩ : syracuseStep 1630687 = 2446031) B2446031
theorem B16507475 : Blo 1447543 16507475 := bstep (se 1 (by rfl) ⟨12380606, by rfl⟩ : syracuseStep 16507475 = 24761213) B24761213
theorem B2171687 : Blo 1447543 2171687 := bstep (se 1 (by rfl) ⟨1628765, by rfl⟩ : syracuseStep 2171687 = 3257531) B3257531
theorem B5497739 : Blo 1447543 5497739 := bstep (se 1 (by rfl) ⟨4123304, by rfl⟩ : syracuseStep 5497739 = 8246609) B8246609
theorem B2319391 : Blo 1447543 2319391 := bstep (se 1 (by rfl) ⟨1739543, by rfl⟩ : syracuseStep 2319391 = 3479087) B3479087
theorem B2172281 : Blo 1447543 2172281 := bstep (se 2 (by rfl) ⟨814605, by rfl⟩ : syracuseStep 2172281 = 1629211) B1629211
theorem B6964861 : Blo 1447543 6964861 := bstep (se 3 (by rfl) ⟨1305911, by rfl⟩ : syracuseStep 6964861 = 2611823) B2611823
theorem B31327955 : Blo 1447543 31327955 := bstep (se 1 (by rfl) ⟨23495966, by rfl⟩ : syracuseStep 31327955 = 46991933) B46991933
theorem B4122359 : Blo 1447543 4122359 := bstep (se 1 (by rfl) ⟨3091769, by rfl⟩ : syracuseStep 4122359 = 6183539) B6183539
theorem B2173103 : Blo 1447543 2173103 := bstep (se 1 (by rfl) ⟨1629827, by rfl⟩ : syracuseStep 2173103 = 3259655) B3259655
theorem B13216223 : Blo 1447543 13216223 := bstep (se 1 (by rfl) ⟨9912167, by rfl⟩ : syracuseStep 13216223 = 19824335) B19824335
theorem B2173817 : Blo 1447543 2173817 := bstep (se 2 (by rfl) ⟨815181, by rfl⟩ : syracuseStep 2173817 = 1630363) B1630363
theorem B2444519 : Blo 1447543 2444519 := bstep (se 1 (by rfl) ⟨1833389, by rfl⟩ : syracuseStep 2444519 = 3666779) B3666779
theorem B1764671 : Blo 1447543 1764671 := bstep (se 1 (by rfl) ⟨1323503, by rfl⟩ : syracuseStep 1764671 = 2647007) B2647007
theorem B22597177 : Blo 1447543 22597177 := bstep (se 2 (by rfl) ⟨8473941, by rfl⟩ : syracuseStep 22597177 = 16947883) B16947883
theorem B3665513 : Blo 1447543 3665513 := bstep (se 2 (by rfl) ⟨1374567, by rfl⟩ : syracuseStep 3665513 = 2749135) B2749135
theorem B39636641 : Blo 1447543 39636641 := bstep (se 2 (by rfl) ⟨14863740, by rfl⟩ : syracuseStep 39636641 = 29727481) B29727481
theorem B57233243 : Blo 1447543 57233243 := bstep (se 1 (by rfl) ⟨42924932, by rfl⟩ : syracuseStep 57233243 = 85849865) B85849865
theorem B2445167 : Blo 1447543 2445167 := bstep (se 1 (by rfl) ⟨1833875, by rfl⟩ : syracuseStep 2445167 = 3667751) B3667751
theorem B10997693 : Blo 1447543 10997693 := bstep (se 3 (by rfl) ⟨2062067, by rfl⟩ : syracuseStep 10997693 = 4124135) B4124135
theorem B2445383 : Blo 1447543 2445383 := bstep (se 1 (by rfl) ⟨1834037, by rfl⟩ : syracuseStep 2445383 = 3668075) B3668075
theorem B4886675 : Blo 1447543 4886675 := bstep (se 1 (by rfl) ⟨3665006, by rfl⟩ : syracuseStep 4886675 = 7330013) B7330013
theorem B7336331 : Blo 1447543 7336331 := bstep (se 1 (by rfl) ⟨5502248, by rfl⟩ : syracuseStep 7336331 = 11004497) B11004497
theorem B2445815 : Blo 1447543 2445815 := bstep (se 1 (by rfl) ⟨1834361, by rfl⟩ : syracuseStep 2445815 = 3668723) B3668723
theorem B15667823 : Blo 1447543 15667823 := bstep (se 1 (by rfl) ⟨11750867, by rfl⟩ : syracuseStep 15667823 = 23501735) B23501735
theorem B13923035 : Blo 1447543 13923035 := bstep (se 1 (by rfl) ⟨10442276, by rfl⟩ : syracuseStep 13923035 = 20884553) B20884553
theorem B17609519 : Blo 1447543 17609519 := bstep (se 1 (by rfl) ⟨13207139, by rfl⟩ : syracuseStep 17609519 = 26414279) B26414279
theorem B11752751 : Blo 1447543 11752751 := bstep (se 1 (by rfl) ⟨8814563, by rfl⟩ : syracuseStep 11752751 = 17629127) B17629127
theorem B20895043 : Blo 1447543 20895043 := bstep (se 1 (by rfl) ⟨15671282, by rfl⟩ : syracuseStep 20895043 = 31342565) B31342565
theorem B3258359 : Blo 1447543 3258359 := bstep (se 1 (by rfl) ⟨2443769, by rfl⟩ : syracuseStep 3258359 = 4887539) B4887539
theorem B16488521 : Blo 1447543 16488521 := bstep (se 2 (by rfl) ⟨6183195, by rfl⟩ : syracuseStep 16488521 = 12366391) B12366391
theorem B4954279 : Blo 1447543 4954279 := bstep (se 1 (by rfl) ⟨3715709, by rfl⟩ : syracuseStep 4954279 = 7431419) B7431419
theorem B1448143 : Blo 1447543 1448143 := bstep (se 1 (by rfl) ⟨1086107, by rfl⟩ : syracuseStep 1448143 = 2172215) B2172215
theorem B5953823 : Blo 1447543 5953823 := bstep (se 1 (by rfl) ⟨4465367, by rfl⟩ : syracuseStep 5953823 = 8930735) B8930735
theorem B1448447 : Blo 1447543 1448447 := bstep (se 1 (by rfl) ⟨1086335, by rfl⟩ : syracuseStep 1448447 = 2172671) B2172671
theorem B4643497 : Blo 1447543 4643497 := bstep (se 2 (by rfl) ⟨1741311, by rfl⟩ : syracuseStep 4643497 = 3482623) B3482623
theorem B3259385 : Blo 1447543 3259385 := bstep (se 2 (by rfl) ⟨1222269, by rfl⟩ : syracuseStep 3259385 = 2444539) B2444539
theorem B56482829 : Blo 1447543 56482829 := bstep (se 3 (by rfl) ⟨10590530, by rfl⟩ : syracuseStep 56482829 = 21181061) B21181061
theorem B10435817 : Blo 1447543 10435817 := bstep (se 2 (by rfl) ⟨3913431, by rfl⟩ : syracuseStep 10435817 = 7826863) B7826863
theorem B8248999 : Blo 1447543 8248999 := bstep (se 1 (by rfl) ⟨6186749, by rfl⟩ : syracuseStep 8248999 = 12373499) B12373499
theorem B1630255 : Blo 1447543 1630255 := bstep (se 1 (by rfl) ⟨1222691, by rfl⟩ : syracuseStep 1630255 = 2445383) B2445383
theorem B3260519 : Blo 1447543 3260519 := bstep (se 1 (by rfl) ⟨2445389, by rfl⟩ : syracuseStep 3260519 = 4890779) B4890779
theorem B4890887 : Blo 1447543 4890887 := bstep (se 1 (by rfl) ⟨3668165, by rfl⟩ : syracuseStep 4890887 = 7336331) B7336331
theorem B1630543 : Blo 1447543 1630543 := bstep (se 1 (by rfl) ⟨1222907, by rfl⟩ : syracuseStep 1630543 = 2445815) B2445815
theorem B10445215 : Blo 1447543 10445215 := bstep (se 1 (by rfl) ⟨7833911, by rfl⟩ : syracuseStep 10445215 = 15667823) B15667823
theorem B9282023 : Blo 1447543 9282023 := bstep (se 1 (by rfl) ⟨6961517, by rfl⟩ : syracuseStep 9282023 = 13923035) B13923035
theorem B27828845 : Blo 1447543 27828845 := bstep (se 3 (by rfl) ⟨5217908, by rfl⟩ : syracuseStep 27828845 = 10435817) B10435817
theorem B35243261 : Blo 1447543 35243261 := bstep (se 3 (by rfl) ⟨6608111, by rfl⟩ : syracuseStep 35243261 = 13216223) B13216223
theorem B2172239 : Blo 1447543 2172239 := bstep (se 1 (by rfl) ⟨1629179, by rfl⟩ : syracuseStep 2172239 = 3258359) B3258359
theorem B2172923 : Blo 1447543 2172923 := bstep (se 1 (by rfl) ⟨1629692, by rfl⟩ : syracuseStep 2172923 = 3259385) B3259385
theorem B46958717 : Blo 1447543 46958717 := bstep (se 3 (by rfl) ⟨8804759, by rfl⟩ : syracuseStep 46958717 = 17609519) B17609519
theorem B2443675 : Blo 1447543 2443675 := bstep (se 1 (by rfl) ⟨1832756, by rfl⟩ : syracuseStep 2443675 = 3665513) B3665513
theorem B2173799 : Blo 1447543 2173799 := bstep (se 1 (by rfl) ⟨1630349, by rfl⟩ : syracuseStep 2173799 = 3260699) B3260699
theorem B6605705 : Blo 1447543 6605705 := bstep (se 2 (by rfl) ⟨2477139, by rfl⟩ : syracuseStep 6605705 = 4954279) B4954279
theorem B11004983 : Blo 1447543 11004983 := bstep (se 1 (by rfl) ⟨8253737, by rfl⟩ : syracuseStep 11004983 = 16507475) B16507475
theorem B3665159 : Blo 1447543 3665159 := bstep (se 1 (by rfl) ⟨2748869, by rfl⟩ : syracuseStep 3665159 = 5497739) B5497739
theorem B2174249 : Blo 1447543 2174249 := bstep (se 2 (by rfl) ⟨815343, by rfl⟩ : syracuseStep 2174249 = 1630687) B1630687
theorem B31305197 : Blo 1447543 31305197 := bstep (se 3 (by rfl) ⟨5869724, by rfl⟩ : syracuseStep 31305197 = 11739449) B11739449
theorem B4705789 : Blo 1447543 4705789 := bstep (se 3 (by rfl) ⟨882335, by rfl⟩ : syracuseStep 4705789 = 1764671) B1764671
theorem B7835167 : Blo 1447543 7835167 := bstep (se 1 (by rfl) ⟨5876375, by rfl⟩ : syracuseStep 7835167 = 11752751) B11752751
theorem B20885303 : Blo 1447543 20885303 := bstep (se 1 (by rfl) ⟨15663977, by rfl⟩ : syracuseStep 20885303 = 31327955) B31327955
theorem B2748239 : Blo 1447543 2748239 := bstep (se 1 (by rfl) ⟨2061179, by rfl⟩ : syracuseStep 2748239 = 4122359) B4122359
theorem B3092521 : Blo 1447543 3092521 := bstep (se 2 (by rfl) ⟨1159695, by rfl⟩ : syracuseStep 3092521 = 2319391) B2319391
theorem B3969215 : Blo 1447543 3969215 := bstep (se 1 (by rfl) ⟨2976911, by rfl⟩ : syracuseStep 3969215 = 5953823) B5953823
theorem B105697709 : Blo 1447543 105697709 := bstep (se 3 (by rfl) ⟨19818320, by rfl⟩ : syracuseStep 105697709 = 39636641) B39636641
theorem B37655219 : Blo 1447543 37655219 := bstep (se 1 (by rfl) ⟨28241414, by rfl⟩ : syracuseStep 37655219 = 56482829) B56482829
theorem B9286481 : Blo 1447543 9286481 := bstep (se 2 (by rfl) ⟨3482430, by rfl⟩ : syracuseStep 9286481 = 6964861) B6964861
theorem B10998665 : Blo 1447543 10998665 := bstep (se 2 (by rfl) ⟨4124499, by rfl⟩ : syracuseStep 10998665 = 8248999) B8248999
theorem B38155495 : Blo 1447543 38155495 := bstep (se 1 (by rfl) ⟨28616621, by rfl⟩ : syracuseStep 38155495 = 57233243) B57233243
theorem B3257783 : Blo 1447543 3257783 := bstep (se 1 (by rfl) ⟨2443337, by rfl⟩ : syracuseStep 3257783 = 4886675) B4886675
theorem B1447791 : Blo 1447543 1447791 := bstep (se 1 (by rfl) ⟨1085843, by rfl⟩ : syracuseStep 1447791 = 2171687) B2171687
theorem B6191329 : Blo 1447543 6191329 := bstep (se 2 (by rfl) ⟨2321748, by rfl⟩ : syracuseStep 6191329 = 4643497) B4643497
theorem B1448187 : Blo 1447543 1448187 := bstep (se 1 (by rfl) ⟨1086140, by rfl⟩ : syracuseStep 1448187 = 2172281) B2172281
theorem B10992347 : Blo 1447543 10992347 := bstep (se 1 (by rfl) ⟨8244260, by rfl⟩ : syracuseStep 10992347 = 16488521) B16488521
theorem B1448735 : Blo 1447543 1448735 := bstep (se 1 (by rfl) ⟨1086551, by rfl⟩ : syracuseStep 1448735 = 2173103) B2173103
theorem B27860057 : Blo 1447543 27860057 := bstep (se 2 (by rfl) ⟨10447521, by rfl⟩ : syracuseStep 27860057 = 20895043) B20895043
theorem B1449211 : Blo 1447543 1449211 := bstep (se 1 (by rfl) ⟨1086908, by rfl⟩ : syracuseStep 1449211 = 2173817) B2173817
theorem B30129569 : Blo 1447543 30129569 := bstep (se 2 (by rfl) ⟨11298588, by rfl⟩ : syracuseStep 30129569 = 22597177) B22597177
theorem B1629679 : Blo 1447543 1629679 := bstep (se 1 (by rfl) ⟨1222259, by rfl⟩ : syracuseStep 1629679 = 2444519) B2444519
theorem B1630111 : Blo 1447543 1630111 := bstep (se 1 (by rfl) ⟨1222583, by rfl⟩ : syracuseStep 1630111 = 2445167) B2445167
theorem B7331795 : Blo 1447543 7331795 := bstep (se 1 (by rfl) ⟨5498846, by rfl⟩ : syracuseStep 7331795 = 10997693) B10997693
theorem B2646143 : Blo 1447543 2646143 := bstep (se 1 (by rfl) ⟨1984607, by rfl⟩ : syracuseStep 2646143 = 3969215) B3969215
theorem B3260591 : Blo 1447543 3260591 := bstep (se 1 (by rfl) ⟨2445443, by rfl⟩ : syracuseStep 3260591 = 4890887) B4890887
theorem B13926953 : Blo 1447543 13926953 := bstep (se 2 (by rfl) ⟨5222607, by rfl⟩ : syracuseStep 13926953 = 10445215) B10445215
theorem B7332443 : Blo 1447543 7332443 := bstep (se 1 (by rfl) ⟨5499332, by rfl⟩ : syracuseStep 7332443 = 10998665) B10998665
theorem B23495507 : Blo 1447543 23495507 := bstep (se 1 (by rfl) ⟨17621630, by rfl⟩ : syracuseStep 23495507 = 35243261) B35243261
theorem B2171855 : Blo 1447543 2171855 := bstep (se 1 (by rfl) ⟨1628891, by rfl⟩ : syracuseStep 2171855 = 3257783) B3257783
theorem B50873993 : Blo 1447543 50873993 := bstep (se 2 (by rfl) ⟨19077747, by rfl⟩ : syracuseStep 50873993 = 38155495) B38155495
theorem B2172905 : Blo 1447543 2172905 := bstep (se 2 (by rfl) ⟨814839, by rfl⟩ : syracuseStep 2172905 = 1629679) B1629679
theorem B10446889 : Blo 1447543 10446889 := bstep (se 2 (by rfl) ⟨3917583, by rfl⟩ : syracuseStep 10446889 = 7835167) B7835167
theorem B18573371 : Blo 1447543 18573371 := bstep (se 1 (by rfl) ⟨13930028, by rfl⟩ : syracuseStep 18573371 = 27860057) B27860057
theorem B2443439 : Blo 1447543 2443439 := bstep (se 1 (by rfl) ⟨1832579, by rfl⟩ : syracuseStep 2443439 = 3665159) B3665159
theorem B2173481 : Blo 1447543 2173481 := bstep (se 2 (by rfl) ⟨815055, by rfl⟩ : syracuseStep 2173481 = 1630111) B1630111
theorem B4123361 : Blo 1447543 4123361 := bstep (se 2 (by rfl) ⟨1546260, by rfl⟩ : syracuseStep 4123361 = 3092521) B3092521
theorem B2173673 : Blo 1447543 2173673 := bstep (se 2 (by rfl) ⟨815127, by rfl⟩ : syracuseStep 2173673 = 1630255) B1630255
theorem B2173679 : Blo 1447543 2173679 := bstep (se 1 (by rfl) ⟨1630259, by rfl⟩ : syracuseStep 2173679 = 3260519) B3260519
theorem B6188015 : Blo 1447543 6188015 := bstep (se 1 (by rfl) ⟨4641011, by rfl⟩ : syracuseStep 6188015 = 9282023) B9282023
theorem B2174057 : Blo 1447543 2174057 := bstep (se 2 (by rfl) ⟨815271, by rfl⟩ : syracuseStep 2174057 = 1630543) B1630543
theorem B25103479 : Blo 1447543 25103479 := bstep (se 1 (by rfl) ⟨18827609, by rfl⟩ : syracuseStep 25103479 = 37655219) B37655219
theorem B31305811 : Blo 1447543 31305811 := bstep (se 1 (by rfl) ⟨23479358, by rfl⟩ : syracuseStep 31305811 = 46958717) B46958717
theorem B7328231 : Blo 1447543 7328231 := bstep (se 1 (by rfl) ⟨5496173, by rfl⟩ : syracuseStep 7328231 = 10992347) B10992347
theorem B4403803 : Blo 1447543 4403803 := bstep (se 1 (by rfl) ⟨3302852, by rfl⟩ : syracuseStep 4403803 = 6605705) B6605705
theorem B7336655 : Blo 1447543 7336655 := bstep (se 1 (by rfl) ⟨5502491, by rfl⟩ : syracuseStep 7336655 = 11004983) B11004983
theorem B20870131 : Blo 1447543 20870131 := bstep (se 1 (by rfl) ⟨15652598, by rfl⟩ : syracuseStep 20870131 = 31305197) B31305197
theorem B13923535 : Blo 1447543 13923535 := bstep (se 1 (by rfl) ⟨10442651, by rfl⟩ : syracuseStep 13923535 = 20885303) B20885303
theorem B1832159 : Blo 1447543 1832159 := bstep (se 1 (by rfl) ⟨1374119, by rfl⟩ : syracuseStep 1832159 = 2748239) B2748239
theorem B4887863 : Blo 1447543 4887863 := bstep (se 1 (by rfl) ⟨3665897, by rfl⟩ : syracuseStep 4887863 = 7331795) B7331795
theorem B70465139 : Blo 1447543 70465139 := bstep (se 1 (by rfl) ⟨52848854, by rfl⟩ : syracuseStep 70465139 = 105697709) B105697709
theorem B8255105 : Blo 1447543 8255105 := bstep (se 2 (by rfl) ⟨3095664, by rfl⟩ : syracuseStep 8255105 = 6191329) B6191329
theorem B18552563 : Blo 1447543 18552563 := bstep (se 1 (by rfl) ⟨13914422, by rfl⟩ : syracuseStep 18552563 = 27828845) B27828845
theorem B3258233 : Blo 1447543 3258233 := bstep (se 2 (by rfl) ⟨1221837, by rfl⟩ : syracuseStep 3258233 = 2443675) B2443675
theorem B6190987 : Blo 1447543 6190987 := bstep (se 1 (by rfl) ⟨4643240, by rfl⟩ : syracuseStep 6190987 = 9286481) B9286481
theorem B1448159 : Blo 1447543 1448159 := bstep (se 1 (by rfl) ⟨1086119, by rfl⟩ : syracuseStep 1448159 = 2172239) B2172239
theorem B1448615 : Blo 1447543 1448615 := bstep (se 1 (by rfl) ⟨1086461, by rfl⟩ : syracuseStep 1448615 = 2172923) B2172923
theorem B1449199 : Blo 1447543 1449199 := bstep (se 1 (by rfl) ⟨1086899, by rfl⟩ : syracuseStep 1449199 = 2173799) B2173799
theorem B6274385 : Blo 1447543 6274385 := bstep (se 2 (by rfl) ⟨2352894, by rfl⟩ : syracuseStep 6274385 = 4705789) B4705789
theorem B1449499 : Blo 1447543 1449499 := bstep (se 1 (by rfl) ⟨1087124, by rfl⟩ : syracuseStep 1449499 = 2174249) B2174249
theorem B20086379 : Blo 1447543 20086379 := bstep (se 1 (by rfl) ⟨15064784, by rfl⟩ : syracuseStep 20086379 = 30129569) B30129569
theorem B4891103 : Blo 1447543 4891103 := bstep (se 1 (by rfl) ⟨3668327, by rfl⟩ : syracuseStep 4891103 = 7336655) B7336655
theorem B15663671 : Blo 1447543 15663671 := bstep (se 1 (by rfl) ⟨11747753, by rfl⟩ : syracuseStep 15663671 = 23495507) B23495507
theorem B33915995 : Blo 1447543 33915995 := bstep (se 1 (by rfl) ⟨25436996, by rfl⟩ : syracuseStep 33915995 = 50873993) B50873993
theorem B2172155 : Blo 1447543 2172155 := bstep (se 1 (by rfl) ⟨1629116, by rfl⟩ : syracuseStep 2172155 = 3258233) B3258233
theorem B18564713 : Blo 1447543 18564713 := bstep (se 2 (by rfl) ⟨6961767, by rfl⟩ : syracuseStep 18564713 = 13923535) B13923535
theorem B13929185 : Blo 1447543 13929185 := bstep (se 2 (by rfl) ⟨5223444, by rfl⟩ : syracuseStep 13929185 = 10446889) B10446889
theorem B41741081 : Blo 1447543 41741081 := bstep (se 2 (by rfl) ⟨15652905, by rfl⟩ : syracuseStep 41741081 = 31305811) B31305811
theorem B2173727 : Blo 1447543 2173727 := bstep (se 1 (by rfl) ⟨1630295, by rfl⟩ : syracuseStep 2173727 = 3260591) B3260591
theorem B4885487 : Blo 1447543 4885487 := bstep (se 1 (by rfl) ⟨3664115, by rfl⟩ : syracuseStep 4885487 = 7328231) B7328231
theorem B9284635 : Blo 1447543 9284635 := bstep (se 1 (by rfl) ⟨6963476, by rfl⟩ : syracuseStep 9284635 = 13926953) B13926953
theorem B4885757 : Blo 1447543 4885757 := bstep (se 3 (by rfl) ⟨916079, by rfl⟩ : syracuseStep 4885757 = 1832159) B1832159
theorem B46976759 : Blo 1447543 46976759 := bstep (se 1 (by rfl) ⟨35232569, by rfl⟩ : syracuseStep 46976759 = 70465139) B70465139
theorem B28225525 : Blo 1447543 28225525 := bstep (se 5 (by rfl) ⟨1323071, by rfl⟩ : syracuseStep 28225525 = 2646143) B2646143
theorem B12382247 : Blo 1447543 12382247 := bstep (se 1 (by rfl) ⟨9286685, by rfl⟩ : syracuseStep 12382247 = 18573371) B18573371
theorem B2748907 : Blo 1447543 2748907 := bstep (se 1 (by rfl) ⟨2061680, by rfl⟩ : syracuseStep 2748907 = 4123361) B4123361
theorem B4125343 : Blo 1447543 4125343 := bstep (se 1 (by rfl) ⟨3094007, by rfl⟩ : syracuseStep 4125343 = 6188015) B6188015
theorem B4182923 : Blo 1447543 4182923 := bstep (se 1 (by rfl) ⟨3137192, by rfl⟩ : syracuseStep 4182923 = 6274385) B6274385
theorem B13390919 : Blo 1447543 13390919 := bstep (se 1 (by rfl) ⟨10043189, by rfl⟩ : syracuseStep 13390919 = 20086379) B20086379
theorem B8254649 : Blo 1447543 8254649 := bstep (se 2 (by rfl) ⟨3095493, by rfl⟩ : syracuseStep 8254649 = 6190987) B6190987
theorem B4888295 : Blo 1447543 4888295 := bstep (se 1 (by rfl) ⟨3666221, by rfl⟩ : syracuseStep 4888295 = 7332443) B7332443
theorem B1447903 : Blo 1447543 1447903 := bstep (se 1 (by rfl) ⟨1085927, by rfl⟩ : syracuseStep 1447903 = 2171855) B2171855
theorem B5871737 : Blo 1447543 5871737 := bstep (se 2 (by rfl) ⟨2201901, by rfl⟩ : syracuseStep 5871737 = 4403803) B4403803
theorem B3258575 : Blo 1447543 3258575 := bstep (se 1 (by rfl) ⟨2443931, by rfl⟩ : syracuseStep 3258575 = 4887863) B4887863
theorem B5503403 : Blo 1447543 5503403 := bstep (se 1 (by rfl) ⟨4127552, by rfl⟩ : syracuseStep 5503403 = 8255105) B8255105
theorem B12368375 : Blo 1447543 12368375 := bstep (se 1 (by rfl) ⟨9276281, by rfl⟩ : syracuseStep 12368375 = 18552563) B18552563
theorem B27826841 : Blo 1447543 27826841 := bstep (se 2 (by rfl) ⟨10435065, by rfl⟩ : syracuseStep 27826841 = 20870131) B20870131
theorem B1448603 : Blo 1447543 1448603 := bstep (se 1 (by rfl) ⟨1086452, by rfl⟩ : syracuseStep 1448603 = 2172905) B2172905
theorem B1628959 : Blo 1447543 1628959 := bstep (se 1 (by rfl) ⟨1221719, by rfl⟩ : syracuseStep 1628959 = 2443439) B2443439
theorem B33471305 : Blo 1447543 33471305 := bstep (se 2 (by rfl) ⟨12551739, by rfl⟩ : syracuseStep 33471305 = 25103479) B25103479
theorem B1448987 : Blo 1447543 1448987 := bstep (se 1 (by rfl) ⟨1086740, by rfl⟩ : syracuseStep 1448987 = 2173481) B2173481
theorem B1449115 : Blo 1447543 1449115 := bstep (se 1 (by rfl) ⟨1086836, by rfl⟩ : syracuseStep 1449115 = 2173673) B2173673
theorem B1449119 : Blo 1447543 1449119 := bstep (se 1 (by rfl) ⟨1086839, by rfl⟩ : syracuseStep 1449119 = 2173679) B2173679
theorem B1449371 : Blo 1447543 1449371 := bstep (se 1 (by rfl) ⟨1087028, by rfl⟩ : syracuseStep 1449371 = 2174057) B2174057
theorem B3260735 : Blo 1447543 3260735 := bstep (se 1 (by rfl) ⟨2445551, by rfl⟩ : syracuseStep 3260735 = 4891103) B4891103
theorem B22610663 : Blo 1447543 22610663 := bstep (se 1 (by rfl) ⟨16957997, by rfl⟩ : syracuseStep 22610663 = 33915995) B33915995
theorem B2171945 : Blo 1447543 2171945 := bstep (se 2 (by rfl) ⟨814479, by rfl⟩ : syracuseStep 2171945 = 1628959) B1628959
theorem B12379513 : Blo 1447543 12379513 := bstep (se 2 (by rfl) ⟨4642317, by rfl⟩ : syracuseStep 12379513 = 9284635) B9284635
theorem B2172383 : Blo 1447543 2172383 := bstep (se 1 (by rfl) ⟨1629287, by rfl⟩ : syracuseStep 2172383 = 3258575) B3258575
theorem B2788615 : Blo 1447543 2788615 := bstep (se 1 (by rfl) ⟨2091461, by rfl⟩ : syracuseStep 2788615 = 4182923) B4182923
theorem B3665209 : Blo 1447543 3665209 := bstep (se 2 (by rfl) ⟨1374453, by rfl⟩ : syracuseStep 3665209 = 2748907) B2748907
theorem B5500457 : Blo 1447543 5500457 := bstep (se 2 (by rfl) ⟨2062671, by rfl⟩ : syracuseStep 5500457 = 4125343) B4125343
theorem B8245583 : Blo 1447543 8245583 := bstep (se 1 (by rfl) ⟨6184187, by rfl⟩ : syracuseStep 8245583 = 12368375) B12368375
theorem B18551227 : Blo 1447543 18551227 := bstep (se 1 (by rfl) ⟨13913420, by rfl⟩ : syracuseStep 18551227 = 27826841) B27826841
theorem B9286123 : Blo 1447543 9286123 := bstep (se 1 (by rfl) ⟨6964592, by rfl⟩ : syracuseStep 9286123 = 13929185) B13929185
theorem B3256991 : Blo 1447543 3256991 := bstep (se 1 (by rfl) ⟨2442743, by rfl⟩ : syracuseStep 3256991 = 4885487) B4885487
theorem B3257171 : Blo 1447543 3257171 := bstep (se 1 (by rfl) ⟨2442878, by rfl⟩ : syracuseStep 3257171 = 4885757) B4885757
theorem B8254831 : Blo 1447543 8254831 := bstep (se 1 (by rfl) ⟨6191123, by rfl⟩ : syracuseStep 8254831 = 12382247) B12382247
theorem B10442447 : Blo 1447543 10442447 := bstep (se 1 (by rfl) ⟨7831835, by rfl⟩ : syracuseStep 10442447 = 15663671) B15663671
theorem B8927279 : Blo 1447543 8927279 := bstep (se 1 (by rfl) ⟨6695459, by rfl⟩ : syracuseStep 8927279 = 13390919) B13390919
theorem B5503099 : Blo 1447543 5503099 := bstep (se 1 (by rfl) ⟨4127324, by rfl⟩ : syracuseStep 5503099 = 8254649) B8254649
theorem B1448103 : Blo 1447543 1448103 := bstep (se 1 (by rfl) ⟨1086077, by rfl⟩ : syracuseStep 1448103 = 2172155) B2172155
theorem B12376475 : Blo 1447543 12376475 := bstep (se 1 (by rfl) ⟨9282356, by rfl⟩ : syracuseStep 12376475 = 18564713) B18564713
theorem B3258863 : Blo 1447543 3258863 := bstep (se 1 (by rfl) ⟨2444147, by rfl⟩ : syracuseStep 3258863 = 4888295) B4888295
theorem B3914491 : Blo 1447543 3914491 := bstep (se 1 (by rfl) ⟨2935868, by rfl⟩ : syracuseStep 3914491 = 5871737) B5871737
theorem B3668935 : Blo 1447543 3668935 := bstep (se 1 (by rfl) ⟨2751701, by rfl⟩ : syracuseStep 3668935 = 5503403) B5503403
theorem B27827387 : Blo 1447543 27827387 := bstep (se 1 (by rfl) ⟨20870540, by rfl⟩ : syracuseStep 27827387 = 41741081) B41741081
theorem B1449151 : Blo 1447543 1449151 := bstep (se 1 (by rfl) ⟨1086863, by rfl⟩ : syracuseStep 1449151 = 2173727) B2173727
theorem B22314203 : Blo 1447543 22314203 := bstep (se 1 (by rfl) ⟨16735652, by rfl⟩ : syracuseStep 22314203 = 33471305) B33471305
theorem B31317839 : Blo 1447543 31317839 := bstep (se 1 (by rfl) ⟨23488379, by rfl⟩ : syracuseStep 31317839 = 46976759) B46976759
theorem B37634033 : Blo 1447543 37634033 := bstep (se 2 (by rfl) ⟨14112762, by rfl⟩ : syracuseStep 37634033 = 28225525) B28225525
theorem B5497055 : Blo 1447543 5497055 := bstep (se 1 (by rfl) ⟨4122791, by rfl⟩ : syracuseStep 5497055 = 8245583) B8245583
theorem B2171327 : Blo 1447543 2171327 := bstep (se 1 (by rfl) ⟨1628495, by rfl⟩ : syracuseStep 2171327 = 3256991) B3256991
theorem B15073775 : Blo 1447543 15073775 := bstep (se 1 (by rfl) ⟨11305331, by rfl⟩ : syracuseStep 15073775 = 22610663) B22610663
theorem B2171447 : Blo 1447543 2171447 := bstep (se 1 (by rfl) ⟨1628585, by rfl⟩ : syracuseStep 2171447 = 3257171) B3257171
theorem B5219321 : Blo 1447543 5219321 := bstep (se 2 (by rfl) ⟨1957245, by rfl⟩ : syracuseStep 5219321 = 3914491) B3914491
theorem B4891913 : Blo 1447543 4891913 := bstep (se 2 (by rfl) ⟨1834467, by rfl⟩ : syracuseStep 4891913 = 3668935) B3668935
theorem B8250983 : Blo 1447543 8250983 := bstep (se 1 (by rfl) ⟨6188237, by rfl⟩ : syracuseStep 8250983 = 12376475) B12376475
theorem B2172575 : Blo 1447543 2172575 := bstep (se 1 (by rfl) ⟨1629431, by rfl⟩ : syracuseStep 2172575 = 3258863) B3258863
theorem B2173823 : Blo 1447543 2173823 := bstep (se 1 (by rfl) ⟨1630367, by rfl⟩ : syracuseStep 2173823 = 3260735) B3260735
theorem B24734969 : Blo 1447543 24734969 := bstep (se 2 (by rfl) ⟨9275613, by rfl⟩ : syracuseStep 24734969 = 18551227) B18551227
theorem B12381497 : Blo 1447543 12381497 := bstep (se 2 (by rfl) ⟨4643061, by rfl⟩ : syracuseStep 12381497 = 9286123) B9286123
theorem B5951519 : Blo 1447543 5951519 := bstep (se 1 (by rfl) ⟨4463639, by rfl⟩ : syracuseStep 5951519 = 8927279) B8927279
theorem B4886945 : Blo 1447543 4886945 := bstep (se 2 (by rfl) ⟨1832604, by rfl⟩ : syracuseStep 4886945 = 3665209) B3665209
theorem B11006441 : Blo 1447543 11006441 := bstep (se 2 (by rfl) ⟨4127415, by rfl⟩ : syracuseStep 11006441 = 8254831) B8254831
theorem B18551591 : Blo 1447543 18551591 := bstep (se 1 (by rfl) ⟨13913693, by rfl⟩ : syracuseStep 18551591 = 27827387) B27827387
theorem B3666971 : Blo 1447543 3666971 := bstep (se 1 (by rfl) ⟨2750228, by rfl⟩ : syracuseStep 3666971 = 5500457) B5500457
theorem B20878559 : Blo 1447543 20878559 := bstep (se 1 (by rfl) ⟨15658919, by rfl⟩ : syracuseStep 20878559 = 31317839) B31317839
theorem B25089355 : Blo 1447543 25089355 := bstep (se 1 (by rfl) ⟨18817016, by rfl⟩ : syracuseStep 25089355 = 37634033) B37634033
theorem B7337465 : Blo 1447543 7337465 := bstep (se 2 (by rfl) ⟨2751549, by rfl⟩ : syracuseStep 7337465 = 5503099) B5503099
theorem B1447963 : Blo 1447543 1447963 := bstep (se 1 (by rfl) ⟨1085972, by rfl⟩ : syracuseStep 1447963 = 2171945) B2171945
theorem B1448255 : Blo 1447543 1448255 := bstep (se 1 (by rfl) ⟨1086191, by rfl⟩ : syracuseStep 1448255 = 2172383) B2172383
theorem B6961631 : Blo 1447543 6961631 := bstep (se 1 (by rfl) ⟨5221223, by rfl⟩ : syracuseStep 6961631 = 10442447) B10442447
theorem B3718153 : Blo 1447543 3718153 := bstep (se 2 (by rfl) ⟨1394307, by rfl⟩ : syracuseStep 3718153 = 2788615) B2788615
theorem B16506017 : Blo 1447543 16506017 := bstep (se 2 (by rfl) ⟨6189756, by rfl⟩ : syracuseStep 16506017 = 12379513) B12379513
theorem B14876135 : Blo 1447543 14876135 := bstep (se 1 (by rfl) ⟨11157101, by rfl⟩ : syracuseStep 14876135 = 22314203) B22314203
theorem B13919039 : Blo 1447543 13919039 := bstep (se 1 (by rfl) ⟨10439279, by rfl⟩ : syracuseStep 13919039 = 20878559) B20878559
theorem B3261275 : Blo 1447543 3261275 := bstep (se 1 (by rfl) ⟨2445956, by rfl⟩ : syracuseStep 3261275 = 4891913) B4891913
theorem B4891643 : Blo 1447543 4891643 := bstep (se 1 (by rfl) ⟨3668732, by rfl⟩ : syracuseStep 4891643 = 7337465) B7337465
theorem B18564349 : Blo 1447543 18564349 := bstep (se 3 (by rfl) ⟨3480815, by rfl⟩ : syracuseStep 18564349 = 6961631) B6961631
theorem B4957537 : Blo 1447543 4957537 := bstep (se 2 (by rfl) ⟨1859076, by rfl⟩ : syracuseStep 4957537 = 3718153) B3718153
theorem B11004011 : Blo 1447543 11004011 := bstep (se 1 (by rfl) ⟨8253008, by rfl⟩ : syracuseStep 11004011 = 16506017) B16506017
theorem B3967679 : Blo 1447543 3967679 := bstep (se 1 (by rfl) ⟨2975759, by rfl⟩ : syracuseStep 3967679 = 5951519) B5951519
theorem B3664703 : Blo 1447543 3664703 := bstep (se 1 (by rfl) ⟨2748527, by rfl⟩ : syracuseStep 3664703 = 5497055) B5497055
theorem B2444647 : Blo 1447543 2444647 := bstep (se 1 (by rfl) ⟨1833485, by rfl⟩ : syracuseStep 2444647 = 3666971) B3666971
theorem B5500655 : Blo 1447543 5500655 := bstep (se 1 (by rfl) ⟨4125491, by rfl⟩ : syracuseStep 5500655 = 8250983) B8250983
theorem B33452473 : Blo 1447543 33452473 := bstep (se 2 (by rfl) ⟨12544677, by rfl⟩ : syracuseStep 33452473 = 25089355) B25089355
theorem B8254331 : Blo 1447543 8254331 := bstep (se 1 (by rfl) ⟨6190748, by rfl⟩ : syracuseStep 8254331 = 12381497) B12381497
theorem B9917423 : Blo 1447543 9917423 := bstep (se 1 (by rfl) ⟨7438067, by rfl⟩ : syracuseStep 9917423 = 14876135) B14876135
theorem B3257963 : Blo 1447543 3257963 := bstep (se 1 (by rfl) ⟨2443472, by rfl⟩ : syracuseStep 3257963 = 4886945) B4886945
theorem B1447551 : Blo 1447543 1447551 := bstep (se 1 (by rfl) ⟨1085663, by rfl⟩ : syracuseStep 1447551 = 2171327) B2171327
theorem B7337627 : Blo 1447543 7337627 := bstep (se 1 (by rfl) ⟨5503220, by rfl⟩ : syracuseStep 7337627 = 11006441) B11006441
theorem B10049183 : Blo 1447543 10049183 := bstep (se 1 (by rfl) ⟨7536887, by rfl⟩ : syracuseStep 10049183 = 15073775) B15073775
theorem B1447631 : Blo 1447543 1447631 := bstep (se 1 (by rfl) ⟨1085723, by rfl⟩ : syracuseStep 1447631 = 2171447) B2171447
theorem B12367727 : Blo 1447543 12367727 := bstep (se 1 (by rfl) ⟨9275795, by rfl⟩ : syracuseStep 12367727 = 18551591) B18551591
theorem B1448383 : Blo 1447543 1448383 := bstep (se 1 (by rfl) ⟨1086287, by rfl⟩ : syracuseStep 1448383 = 2172575) B2172575
theorem B1449215 : Blo 1447543 1449215 := bstep (se 1 (by rfl) ⟨1086911, by rfl⟩ : syracuseStep 1449215 = 2173823) B2173823
theorem B16489979 : Blo 1447543 16489979 := bstep (se 1 (by rfl) ⟨12367484, by rfl⟩ : syracuseStep 16489979 = 24734969) B24734969
theorem B13918189 : Blo 1447543 13918189 := bstep (se 3 (by rfl) ⟨2609660, by rfl⟩ : syracuseStep 13918189 = 5219321) B5219321
theorem B6611615 : Blo 1447543 6611615 := bstep (se 1 (by rfl) ⟨4958711, by rfl⟩ : syracuseStep 6611615 = 9917423) B9917423
theorem B3261095 : Blo 1447543 3261095 := bstep (se 1 (by rfl) ⟨2445821, by rfl⟩ : syracuseStep 3261095 = 4891643) B4891643
theorem B2171975 : Blo 1447543 2171975 := bstep (se 1 (by rfl) ⟨1628981, by rfl⟩ : syracuseStep 2171975 = 3257963) B3257963
theorem B4891751 : Blo 1447543 4891751 := bstep (se 1 (by rfl) ⟨3668813, by rfl⟩ : syracuseStep 4891751 = 7337627) B7337627
theorem B2443135 : Blo 1447543 2443135 := bstep (se 1 (by rfl) ⟨1832351, by rfl⟩ : syracuseStep 2443135 = 3664703) B3664703
theorem B18557585 : Blo 1447543 18557585 := bstep (se 2 (by rfl) ⟨6959094, by rfl⟩ : syracuseStep 18557585 = 13918189) B13918189
theorem B2174183 : Blo 1447543 2174183 := bstep (se 1 (by rfl) ⟨1630637, by rfl⟩ : syracuseStep 2174183 = 3261275) B3261275
theorem B8245151 : Blo 1447543 8245151 := bstep (se 1 (by rfl) ⟨6183863, by rfl⟩ : syracuseStep 8245151 = 12367727) B12367727
theorem B7336007 : Blo 1447543 7336007 := bstep (se 1 (by rfl) ⟨5502005, by rfl⟩ : syracuseStep 7336007 = 11004011) B11004011
theorem B24752465 : Blo 1447543 24752465 := bstep (se 2 (by rfl) ⟨9282174, by rfl⟩ : syracuseStep 24752465 = 18564349) B18564349
theorem B3667103 : Blo 1447543 3667103 := bstep (se 1 (by rfl) ⟨2750327, by rfl⟩ : syracuseStep 3667103 = 5500655) B5500655
theorem B9279359 : Blo 1447543 9279359 := bstep (se 1 (by rfl) ⟨6959519, by rfl⟩ : syracuseStep 9279359 = 13919039) B13919039
theorem B44603297 : Blo 1447543 44603297 := bstep (se 2 (by rfl) ⟨16726236, by rfl⟩ : syracuseStep 44603297 = 33452473) B33452473
theorem B5502887 : Blo 1447543 5502887 := bstep (se 1 (by rfl) ⟨4127165, by rfl⟩ : syracuseStep 5502887 = 8254331) B8254331
theorem B6699455 : Blo 1447543 6699455 := bstep (se 1 (by rfl) ⟨5024591, by rfl⟩ : syracuseStep 6699455 = 10049183) B10049183
theorem B2645119 : Blo 1447543 2645119 := bstep (se 1 (by rfl) ⟨1983839, by rfl⟩ : syracuseStep 2645119 = 3967679) B3967679
theorem B6610049 : Blo 1447543 6610049 := bstep (se 2 (by rfl) ⟨2478768, by rfl⟩ : syracuseStep 6610049 = 4957537) B4957537
theorem B3259529 : Blo 1447543 3259529 := bstep (se 2 (by rfl) ⟨1222323, by rfl⟩ : syracuseStep 3259529 = 2444647) B2444647
theorem B10993319 : Blo 1447543 10993319 := bstep (se 1 (by rfl) ⟨8244989, by rfl⟩ : syracuseStep 10993319 = 16489979) B16489979
theorem B4890671 : Blo 1447543 4890671 := bstep (se 1 (by rfl) ⟨3668003, by rfl⟩ : syracuseStep 4890671 = 7336007) B7336007
theorem B4407743 : Blo 1447543 4407743 := bstep (se 1 (by rfl) ⟨3305807, by rfl⟩ : syracuseStep 4407743 = 6611615) B6611615
theorem B14107301 : Blo 1447543 14107301 := bstep (se 4 (by rfl) ⟨1322559, by rfl⟩ : syracuseStep 14107301 = 2645119) B2645119
theorem B3261167 : Blo 1447543 3261167 := bstep (se 1 (by rfl) ⟨2445875, by rfl⟩ : syracuseStep 3261167 = 4891751) B4891751
theorem B6186239 : Blo 1447543 6186239 := bstep (se 1 (by rfl) ⟨4639679, by rfl⟩ : syracuseStep 6186239 = 9279359) B9279359
theorem B4466303 : Blo 1447543 4466303 := bstep (se 1 (by rfl) ⟨3349727, by rfl⟩ : syracuseStep 4466303 = 6699455) B6699455
theorem B12371723 : Blo 1447543 12371723 := bstep (se 1 (by rfl) ⟨9278792, by rfl⟩ : syracuseStep 12371723 = 18557585) B18557585
theorem B2173019 : Blo 1447543 2173019 := bstep (se 1 (by rfl) ⟨1629764, by rfl⟩ : syracuseStep 2173019 = 3259529) B3259529
theorem B16501643 : Blo 1447543 16501643 := bstep (se 1 (by rfl) ⟨12376232, by rfl⟩ : syracuseStep 16501643 = 24752465) B24752465
theorem B2174063 : Blo 1447543 2174063 := bstep (se 1 (by rfl) ⟨1630547, by rfl⟩ : syracuseStep 2174063 = 3261095) B3261095
theorem B2444735 : Blo 1447543 2444735 := bstep (se 1 (by rfl) ⟨1833551, by rfl⟩ : syracuseStep 2444735 = 3667103) B3667103
theorem B7328879 : Blo 1447543 7328879 := bstep (se 1 (by rfl) ⟨5496659, by rfl⟩ : syracuseStep 7328879 = 10993319) B10993319
theorem B3257513 : Blo 1447543 3257513 := bstep (se 2 (by rfl) ⟨1221567, by rfl⟩ : syracuseStep 3257513 = 2443135) B2443135
theorem B1447983 : Blo 1447543 1447983 := bstep (se 1 (by rfl) ⟨1085987, by rfl⟩ : syracuseStep 1447983 = 2171975) B2171975
theorem B29735531 : Blo 1447543 29735531 := bstep (se 1 (by rfl) ⟨22301648, by rfl⟩ : syracuseStep 29735531 = 44603297) B44603297
theorem B3668591 : Blo 1447543 3668591 := bstep (se 1 (by rfl) ⟨2751443, by rfl⟩ : syracuseStep 3668591 = 5502887) B5502887
theorem B4406699 : Blo 1447543 4406699 := bstep (se 1 (by rfl) ⟨3305024, by rfl⟩ : syracuseStep 4406699 = 6610049) B6610049
theorem B1449455 : Blo 1447543 1449455 := bstep (se 1 (by rfl) ⟨1087091, by rfl⟩ : syracuseStep 1449455 = 2174183) B2174183
theorem B5496767 : Blo 1447543 5496767 := bstep (se 1 (by rfl) ⟨4122575, by rfl⟩ : syracuseStep 5496767 = 8245151) B8245151
theorem B3260447 : Blo 1447543 3260447 := bstep (se 1 (by rfl) ⟨2445335, by rfl⟩ : syracuseStep 3260447 = 4890671) B4890671
theorem B9404867 : Blo 1447543 9404867 := bstep (se 1 (by rfl) ⟨7053650, by rfl⟩ : syracuseStep 9404867 = 14107301) B14107301
theorem B2171675 : Blo 1447543 2171675 := bstep (se 1 (by rfl) ⟨1628756, by rfl⟩ : syracuseStep 2171675 = 3257513) B3257513
theorem B3664511 : Blo 1447543 3664511 := bstep (se 1 (by rfl) ⟨2748383, by rfl⟩ : syracuseStep 3664511 = 5496767) B5496767
theorem B2174111 : Blo 1447543 2174111 := bstep (se 1 (by rfl) ⟨1630583, by rfl⟩ : syracuseStep 2174111 = 3261167) B3261167
theorem B4885919 : Blo 1447543 4885919 := bstep (se 1 (by rfl) ⟨3664439, by rfl⟩ : syracuseStep 4885919 = 7328879) B7328879
theorem B4124159 : Blo 1447543 4124159 := bstep (se 1 (by rfl) ⟨3093119, by rfl⟩ : syracuseStep 4124159 = 6186239) B6186239
theorem B2977535 : Blo 1447543 2977535 := bstep (se 1 (by rfl) ⟨2233151, by rfl⟩ : syracuseStep 2977535 = 4466303) B4466303
theorem B2445727 : Blo 1447543 2445727 := bstep (se 1 (by rfl) ⟨1834295, by rfl⟩ : syracuseStep 2445727 = 3668591) B3668591
theorem B2937799 : Blo 1447543 2937799 := bstep (se 1 (by rfl) ⟨2203349, by rfl⟩ : syracuseStep 2937799 = 4406699) B4406699
theorem B11753981 : Blo 1447543 11753981 := bstep (se 3 (by rfl) ⟨2203871, by rfl⟩ : syracuseStep 11753981 = 4407743) B4407743
theorem B8247815 : Blo 1447543 8247815 := bstep (se 1 (by rfl) ⟨6185861, by rfl⟩ : syracuseStep 8247815 = 12371723) B12371723
theorem B1448679 : Blo 1447543 1448679 := bstep (se 1 (by rfl) ⟨1086509, by rfl⟩ : syracuseStep 1448679 = 2173019) B2173019
theorem B19823687 : Blo 1447543 19823687 := bstep (se 1 (by rfl) ⟨14867765, by rfl⟩ : syracuseStep 19823687 = 29735531) B29735531
theorem B11001095 : Blo 1447543 11001095 := bstep (se 1 (by rfl) ⟨8250821, by rfl⟩ : syracuseStep 11001095 = 16501643) B16501643
theorem B1449375 : Blo 1447543 1449375 := bstep (se 1 (by rfl) ⟨1087031, by rfl⟩ : syracuseStep 1449375 = 2174063) B2174063
theorem B1629823 : Blo 1447543 1629823 := bstep (se 1 (by rfl) ⟨1222367, by rfl⟩ : syracuseStep 1629823 = 2444735) B2444735
theorem B3260969 : Blo 1447543 3260969 := bstep (se 2 (by rfl) ⟨1222863, by rfl⟩ : syracuseStep 3260969 = 2445727) B2445727
theorem B5498543 : Blo 1447543 5498543 := bstep (se 1 (by rfl) ⟨4123907, by rfl⟩ : syracuseStep 5498543 = 8247815) B8247815
theorem B2443007 : Blo 1447543 2443007 := bstep (se 1 (by rfl) ⟨1832255, by rfl⟩ : syracuseStep 2443007 = 3664511) B3664511
theorem B13215791 : Blo 1447543 13215791 := bstep (se 1 (by rfl) ⟨9911843, by rfl⟩ : syracuseStep 13215791 = 19823687) B19823687
theorem B2173097 : Blo 1447543 2173097 := bstep (se 2 (by rfl) ⟨814911, by rfl⟩ : syracuseStep 2173097 = 1629823) B1629823
theorem B7334063 : Blo 1447543 7334063 := bstep (se 1 (by rfl) ⟨5500547, by rfl⟩ : syracuseStep 7334063 = 11001095) B11001095
theorem B1985023 : Blo 1447543 1985023 := bstep (se 1 (by rfl) ⟨1488767, by rfl⟩ : syracuseStep 1985023 = 2977535) B2977535
theorem B2173631 : Blo 1447543 2173631 := bstep (se 1 (by rfl) ⟨1630223, by rfl⟩ : syracuseStep 2173631 = 3260447) B3260447
theorem B25079645 : Blo 1447543 25079645 := bstep (se 3 (by rfl) ⟨4702433, by rfl⟩ : syracuseStep 25079645 = 9404867) B9404867
theorem B7835987 : Blo 1447543 7835987 := bstep (se 1 (by rfl) ⟨5876990, by rfl⟩ : syracuseStep 7835987 = 11753981) B11753981
theorem B3257279 : Blo 1447543 3257279 := bstep (se 1 (by rfl) ⟨2442959, by rfl⟩ : syracuseStep 3257279 = 4885919) B4885919
theorem B2749439 : Blo 1447543 2749439 := bstep (se 1 (by rfl) ⟨2062079, by rfl⟩ : syracuseStep 2749439 = 4124159) B4124159
theorem B15668261 : Blo 1447543 15668261 := bstep (se 4 (by rfl) ⟨1468899, by rfl⟩ : syracuseStep 15668261 = 2937799) B2937799
theorem B1447783 : Blo 1447543 1447783 := bstep (se 1 (by rfl) ⟨1085837, by rfl⟩ : syracuseStep 1447783 = 2171675) B2171675
theorem B1449407 : Blo 1447543 1449407 := bstep (se 1 (by rfl) ⟨1087055, by rfl⟩ : syracuseStep 1449407 = 2174111) B2174111
theorem B2171519 : Blo 1447543 2171519 := bstep (se 1 (by rfl) ⟨1628639, by rfl⟩ : syracuseStep 2171519 = 3257279) B3257279
theorem B10445507 : Blo 1447543 10445507 := bstep (se 1 (by rfl) ⟨7834130, by rfl⟩ : syracuseStep 10445507 = 15668261) B15668261
theorem B10586789 : Blo 1447543 10586789 := bstep (se 4 (by rfl) ⟨992511, by rfl⟩ : syracuseStep 10586789 = 1985023) B1985023
theorem B2173979 : Blo 1447543 2173979 := bstep (se 1 (by rfl) ⟨1630484, by rfl⟩ : syracuseStep 2173979 = 3260969) B3260969
theorem B3665695 : Blo 1447543 3665695 := bstep (se 1 (by rfl) ⟨2749271, by rfl⟩ : syracuseStep 3665695 = 5498543) B5498543
theorem B8810527 : Blo 1447543 8810527 := bstep (se 1 (by rfl) ⟨6607895, by rfl⟩ : syracuseStep 8810527 = 13215791) B13215791
theorem B1832959 : Blo 1447543 1832959 := bstep (se 1 (by rfl) ⟨1374719, by rfl⟩ : syracuseStep 1832959 = 2749439) B2749439
theorem B20895965 : Blo 1447543 20895965 := bstep (se 3 (by rfl) ⟨3917993, by rfl⟩ : syracuseStep 20895965 = 7835987) B7835987
theorem B1628671 : Blo 1447543 1628671 := bstep (se 1 (by rfl) ⟨1221503, by rfl⟩ : syracuseStep 1628671 = 2443007) B2443007
theorem B1448731 : Blo 1447543 1448731 := bstep (se 1 (by rfl) ⟨1086548, by rfl⟩ : syracuseStep 1448731 = 2173097) B2173097
theorem B4889375 : Blo 1447543 4889375 := bstep (se 1 (by rfl) ⟨3667031, by rfl⟩ : syracuseStep 4889375 = 7334063) B7334063
theorem B1449087 : Blo 1447543 1449087 := bstep (se 1 (by rfl) ⟨1086815, by rfl⟩ : syracuseStep 1449087 = 2173631) B2173631
theorem B66879053 : Blo 1447543 66879053 := bstep (se 3 (by rfl) ⟨12539822, by rfl⟩ : syracuseStep 66879053 = 25079645) B25079645
theorem B11747369 : Blo 1447543 11747369 := bstep (se 2 (by rfl) ⟨4405263, by rfl⟩ : syracuseStep 11747369 = 8810527) B8810527
theorem B6963671 : Blo 1447543 6963671 := bstep (se 1 (by rfl) ⟨5222753, by rfl⟩ : syracuseStep 6963671 = 10445507) B10445507
theorem B2171561 : Blo 1447543 2171561 := bstep (se 2 (by rfl) ⟨814335, by rfl⟩ : syracuseStep 2171561 = 1628671) B1628671
theorem B2443945 : Blo 1447543 2443945 := bstep (se 2 (by rfl) ⟨916479, by rfl⟩ : syracuseStep 2443945 = 1832959) B1832959
theorem B13930643 : Blo 1447543 13930643 := bstep (se 1 (by rfl) ⟨10447982, by rfl⟩ : syracuseStep 13930643 = 20895965) B20895965
theorem B7057859 : Blo 1447543 7057859 := bstep (se 1 (by rfl) ⟨5293394, by rfl⟩ : syracuseStep 7057859 = 10586789) B10586789
theorem B4887593 : Blo 1447543 4887593 := bstep (se 2 (by rfl) ⟨1832847, by rfl⟩ : syracuseStep 4887593 = 3665695) B3665695
theorem B44586035 : Blo 1447543 44586035 := bstep (se 1 (by rfl) ⟨33439526, by rfl⟩ : syracuseStep 44586035 = 66879053) B66879053
theorem B1447679 : Blo 1447543 1447679 := bstep (se 1 (by rfl) ⟨1085759, by rfl⟩ : syracuseStep 1447679 = 2171519) B2171519
theorem B3259583 : Blo 1447543 3259583 := bstep (se 1 (by rfl) ⟨2444687, by rfl⟩ : syracuseStep 3259583 = 4889375) B4889375
theorem B1449319 : Blo 1447543 1449319 := bstep (se 1 (by rfl) ⟨1086989, by rfl⟩ : syracuseStep 1449319 = 2173979) B2173979
theorem B7831579 : Blo 1447543 7831579 := bstep (se 1 (by rfl) ⟨5873684, by rfl⟩ : syracuseStep 7831579 = 11747369) B11747369
theorem B2173055 : Blo 1447543 2173055 := bstep (se 1 (by rfl) ⟨1629791, by rfl⟩ : syracuseStep 2173055 = 3259583) B3259583
theorem B29724023 : Blo 1447543 29724023 := bstep (se 1 (by rfl) ⟨22293017, by rfl⟩ : syracuseStep 29724023 = 44586035) B44586035
theorem B18820957 : Blo 1447543 18820957 := bstep (se 3 (by rfl) ⟨3528929, by rfl⟩ : syracuseStep 18820957 = 7057859) B7057859
theorem B4642447 : Blo 1447543 4642447 := bstep (se 1 (by rfl) ⟨3481835, by rfl⟩ : syracuseStep 4642447 = 6963671) B6963671
theorem B37148381 : Blo 1447543 37148381 := bstep (se 3 (by rfl) ⟨6965321, by rfl⟩ : syracuseStep 37148381 = 13930643) B13930643
theorem B1447707 : Blo 1447543 1447707 := bstep (se 1 (by rfl) ⟨1085780, by rfl⟩ : syracuseStep 1447707 = 2171561) B2171561
theorem B3258395 : Blo 1447543 3258395 := bstep (se 1 (by rfl) ⟨2443796, by rfl⟩ : syracuseStep 3258395 = 4887593) B4887593
theorem B3258593 : Blo 1447543 3258593 := bstep (se 2 (by rfl) ⟨1221972, by rfl⟩ : syracuseStep 3258593 = 2443945) B2443945
theorem B24765587 : Blo 1447543 24765587 := bstep (se 1 (by rfl) ⟨18574190, by rfl⟩ : syracuseStep 24765587 = 37148381) B37148381
theorem B2172263 : Blo 1447543 2172263 := bstep (se 1 (by rfl) ⟨1629197, by rfl⟩ : syracuseStep 2172263 = 3258395) B3258395
theorem B2172395 : Blo 1447543 2172395 := bstep (se 1 (by rfl) ⟨1629296, by rfl⟩ : syracuseStep 2172395 = 3258593) B3258593
theorem B25094609 : Blo 1447543 25094609 := bstep (se 2 (by rfl) ⟨9410478, by rfl⟩ : syracuseStep 25094609 = 18820957) B18820957
theorem B6189929 : Blo 1447543 6189929 := bstep (se 2 (by rfl) ⟨2321223, by rfl⟩ : syracuseStep 6189929 = 4642447) B4642447
theorem B10442105 : Blo 1447543 10442105 := bstep (se 2 (by rfl) ⟨3915789, by rfl⟩ : syracuseStep 10442105 = 7831579) B7831579
theorem B1448703 : Blo 1447543 1448703 := bstep (se 1 (by rfl) ⟨1086527, by rfl⟩ : syracuseStep 1448703 = 2173055) B2173055
theorem B19816015 : Blo 1447543 19816015 := bstep (se 1 (by rfl) ⟨14862011, by rfl⟩ : syracuseStep 19816015 = 29724023) B29724023
theorem B16729739 : Blo 1447543 16729739 := bstep (se 1 (by rfl) ⟨12547304, by rfl⟩ : syracuseStep 16729739 = 25094609) B25094609
theorem B26421353 : Blo 1447543 26421353 := bstep (se 2 (by rfl) ⟨9908007, by rfl⟩ : syracuseStep 26421353 = 19816015) B19816015
theorem B16510391 : Blo 1447543 16510391 := bstep (se 1 (by rfl) ⟨12382793, by rfl⟩ : syracuseStep 16510391 = 24765587) B24765587
theorem B4126619 : Blo 1447543 4126619 := bstep (se 1 (by rfl) ⟨3094964, by rfl⟩ : syracuseStep 4126619 = 6189929) B6189929
theorem B1448175 : Blo 1447543 1448175 := bstep (se 1 (by rfl) ⟨1086131, by rfl⟩ : syracuseStep 1448175 = 2172263) B2172263
theorem B6961403 : Blo 1447543 6961403 := bstep (se 1 (by rfl) ⟨5221052, by rfl⟩ : syracuseStep 6961403 = 10442105) B10442105
theorem B1448263 : Blo 1447543 1448263 := bstep (se 1 (by rfl) ⟨1086197, by rfl⟩ : syracuseStep 1448263 = 2172395) B2172395
theorem B17614235 : Blo 1447543 17614235 := bstep (se 1 (by rfl) ⟨13210676, by rfl⟩ : syracuseStep 17614235 = 26421353) B26421353
theorem B11153159 : Blo 1447543 11153159 := bstep (se 1 (by rfl) ⟨8364869, by rfl⟩ : syracuseStep 11153159 = 16729739) B16729739
theorem B4640935 : Blo 1447543 4640935 := bstep (se 1 (by rfl) ⟨3480701, by rfl⟩ : syracuseStep 4640935 = 6961403) B6961403
theorem B11006927 : Blo 1447543 11006927 := bstep (se 1 (by rfl) ⟨8255195, by rfl⟩ : syracuseStep 11006927 = 16510391) B16510391
theorem B2751079 : Blo 1447543 2751079 := bstep (se 1 (by rfl) ⟨2063309, by rfl⟩ : syracuseStep 2751079 = 4126619) B4126619
theorem B6187913 : Blo 1447543 6187913 := bstep (se 2 (by rfl) ⟨2320467, by rfl⟩ : syracuseStep 6187913 = 4640935) B4640935
theorem B11742823 : Blo 1447543 11742823 := bstep (se 1 (by rfl) ⟨8807117, by rfl⟩ : syracuseStep 11742823 = 17614235) B17614235
theorem B7435439 : Blo 1447543 7435439 := bstep (se 1 (by rfl) ⟨5576579, by rfl⟩ : syracuseStep 7435439 = 11153159) B11153159
theorem B7337951 : Blo 1447543 7337951 := bstep (se 1 (by rfl) ⟨5503463, by rfl⟩ : syracuseStep 7337951 = 11006927) B11006927
theorem B3668105 : Blo 1447543 3668105 := bstep (se 2 (by rfl) ⟨1375539, by rfl⟩ : syracuseStep 3668105 = 2751079) B2751079
theorem B62628389 : Blo 1447543 62628389 := bstep (se 4 (by rfl) ⟨5871411, by rfl⟩ : syracuseStep 62628389 = 11742823) B11742823
theorem B4956959 : Blo 1447543 4956959 := bstep (se 1 (by rfl) ⟨3717719, by rfl⟩ : syracuseStep 4956959 = 7435439) B7435439
theorem B4891967 : Blo 1447543 4891967 := bstep (se 1 (by rfl) ⟨3668975, by rfl⟩ : syracuseStep 4891967 = 7337951) B7337951
theorem B2445403 : Blo 1447543 2445403 := bstep (se 1 (by rfl) ⟨1834052, by rfl⟩ : syracuseStep 2445403 = 3668105) B3668105
theorem B4125275 : Blo 1447543 4125275 := bstep (se 1 (by rfl) ⟨3093956, by rfl⟩ : syracuseStep 4125275 = 6187913) B6187913
theorem B3260537 : Blo 1447543 3260537 := bstep (se 2 (by rfl) ⟨1222701, by rfl⟩ : syracuseStep 3260537 = 2445403) B2445403
theorem B3261311 : Blo 1447543 3261311 := bstep (se 1 (by rfl) ⟨2445983, by rfl⟩ : syracuseStep 3261311 = 4891967) B4891967
theorem B13218557 : Blo 1447543 13218557 := bstep (se 3 (by rfl) ⟨2478479, by rfl⟩ : syracuseStep 13218557 = 4956959) B4956959
theorem B41752259 : Blo 1447543 41752259 := bstep (se 1 (by rfl) ⟨31314194, by rfl⟩ : syracuseStep 41752259 = 62628389) B62628389
theorem B2750183 : Blo 1447543 2750183 := bstep (se 1 (by rfl) ⟨2062637, by rfl⟩ : syracuseStep 2750183 = 4125275) B4125275
theorem B2173691 : Blo 1447543 2173691 := bstep (se 1 (by rfl) ⟨1630268, by rfl⟩ : syracuseStep 2173691 = 3260537) B3260537
theorem B2174207 : Blo 1447543 2174207 := bstep (se 1 (by rfl) ⟨1630655, by rfl⟩ : syracuseStep 2174207 = 3261311) B3261311
theorem B140997941 : Blo 1447543 140997941 := bstep (se 5 (by rfl) ⟨6609278, by rfl⟩ : syracuseStep 140997941 = 13218557) B13218557
theorem B27834839 : Blo 1447543 27834839 := bstep (se 1 (by rfl) ⟨20876129, by rfl⟩ : syracuseStep 27834839 = 41752259) B41752259
theorem B1833455 : Blo 1447543 1833455 := bstep (se 1 (by rfl) ⟨1375091, by rfl⟩ : syracuseStep 1833455 = 2750183) B2750183
theorem B18556559 : Blo 1447543 18556559 := bstep (se 1 (by rfl) ⟨13917419, by rfl⟩ : syracuseStep 18556559 = 27834839) B27834839
theorem B93998627 : Blo 1447543 93998627 := bstep (se 1 (by rfl) ⟨70498970, by rfl⟩ : syracuseStep 93998627 = 140997941) B140997941
theorem B4889213 : Blo 1447543 4889213 := bstep (se 3 (by rfl) ⟨916727, by rfl⟩ : syracuseStep 4889213 = 1833455) B1833455
theorem B1449127 : Blo 1447543 1449127 := bstep (se 1 (by rfl) ⟨1086845, by rfl⟩ : syracuseStep 1449127 = 2173691) B2173691
theorem B1449471 : Blo 1447543 1449471 := bstep (se 1 (by rfl) ⟨1087103, by rfl⟩ : syracuseStep 1449471 = 2174207) B2174207
theorem B12371039 : Blo 1447543 12371039 := bstep (se 1 (by rfl) ⟨9278279, by rfl⟩ : syracuseStep 12371039 = 18556559) B18556559
theorem B62665751 : Blo 1447543 62665751 := bstep (se 1 (by rfl) ⟨46999313, by rfl⟩ : syracuseStep 62665751 = 93998627) B93998627
theorem B3259475 : Blo 1447543 3259475 := bstep (se 1 (by rfl) ⟨2444606, by rfl⟩ : syracuseStep 3259475 = 4889213) B4889213
theorem B2172983 : Blo 1447543 2172983 := bstep (se 1 (by rfl) ⟨1629737, by rfl⟩ : syracuseStep 2172983 = 3259475) B3259475
theorem B41777167 : Blo 1447543 41777167 := bstep (se 1 (by rfl) ⟨31332875, by rfl⟩ : syracuseStep 41777167 = 62665751) B62665751
theorem B8247359 : Blo 1447543 8247359 := bstep (se 1 (by rfl) ⟨6185519, by rfl⟩ : syracuseStep 8247359 = 12371039) B12371039
theorem B5498239 : Blo 1447543 5498239 := bstep (se 1 (by rfl) ⟨4123679, by rfl⟩ : syracuseStep 5498239 = 8247359) B8247359
theorem B55702889 : Blo 1447543 55702889 := bstep (se 2 (by rfl) ⟨20888583, by rfl⟩ : syracuseStep 55702889 = 41777167) B41777167
theorem B1448655 : Blo 1447543 1448655 := bstep (se 1 (by rfl) ⟨1086491, by rfl⟩ : syracuseStep 1448655 = 2172983) B2172983
theorem B37135259 : Blo 1447543 37135259 := bstep (se 1 (by rfl) ⟨27851444, by rfl⟩ : syracuseStep 37135259 = 55702889) B55702889
theorem B7330985 : Blo 1447543 7330985 := bstep (se 2 (by rfl) ⟨2749119, by rfl⟩ : syracuseStep 7330985 = 5498239) B5498239
theorem B24756839 : Blo 1447543 24756839 := bstep (se 1 (by rfl) ⟨18567629, by rfl⟩ : syracuseStep 24756839 = 37135259) B37135259
theorem B4887323 : Blo 1447543 4887323 := bstep (se 1 (by rfl) ⟨3665492, by rfl⟩ : syracuseStep 4887323 = 7330985) B7330985
theorem B16504559 : Blo 1447543 16504559 := bstep (se 1 (by rfl) ⟨12378419, by rfl⟩ : syracuseStep 16504559 = 24756839) B24756839
theorem B3258215 : Blo 1447543 3258215 := bstep (se 1 (by rfl) ⟨2443661, by rfl⟩ : syracuseStep 3258215 = 4887323) B4887323
theorem B11003039 : Blo 1447543 11003039 := bstep (se 1 (by rfl) ⟨8252279, by rfl⟩ : syracuseStep 11003039 = 16504559) B16504559
theorem B2172143 : Blo 1447543 2172143 := bstep (se 1 (by rfl) ⟨1629107, by rfl⟩ : syracuseStep 2172143 = 3258215) B3258215
theorem B7335359 : Blo 1447543 7335359 := bstep (se 1 (by rfl) ⟨5501519, by rfl⟩ : syracuseStep 7335359 = 11003039) B11003039
theorem B1448095 : Blo 1447543 1448095 := bstep (se 1 (by rfl) ⟨1086071, by rfl⟩ : syracuseStep 1448095 = 2172143) B2172143
theorem B4890239 : Blo 1447543 4890239 := bstep (se 1 (by rfl) ⟨3667679, by rfl⟩ : syracuseStep 4890239 = 7335359) B7335359
theorem B3260159 : Blo 1447543 3260159 := bstep (se 1 (by rfl) ⟨2445119, by rfl⟩ : syracuseStep 3260159 = 4890239) B4890239
theorem B2173439 : Blo 1447543 2173439 := bstep (se 1 (by rfl) ⟨1630079, by rfl⟩ : syracuseStep 2173439 = 3260159) B3260159
theorem B1448959 : Blo 1447543 1448959 := bstep (se 1 (by rfl) ⟨1086719, by rfl⟩ : syracuseStep 1448959 = 2173439) B2173439

theorem C0 (j : ℕ) (h1 : 361885 ≤ j) (h2 : j ≤ 362385) : Blo 1447543 (4 * j + 3) := by
  interval_cases j
  · exact B1447543
  · exact B1447547
  · exact B1447551
  · exact B1447555
  · exact B1447559
  · exact B1447563
  · exact B1447567
  · exact B1447571
  · exact B1447575
  · exact B1447579
  · exact B1447583
  · exact B1447587
  · exact B1447591
  · exact B1447595
  · exact B1447599
  · exact B1447603
  · exact B1447607
  · exact B1447611
  · exact B1447615
  · exact B1447619
  · exact B1447623
  · exact B1447627
  · exact B1447631
  · exact B1447635
  · exact B1447639
  · exact B1447643
  · exact B1447647
  · exact B1447651
  · exact B1447655
  · exact B1447659
  · exact B1447663
  · exact B1447667
  · exact B1447671
  · exact B1447675
  · exact B1447679
  · exact B1447683
  · exact B1447687
  · exact B1447691
  · exact B1447695
  · exact B1447699
  · exact B1447703
  · exact B1447707
  · exact B1447711
  · exact B1447715
  · exact B1447719
  · exact B1447723
  · exact B1447727
  · exact B1447731
  · exact B1447735
  · exact B1447739
  · exact B1447743
  · exact B1447747
  · exact B1447751
  · exact B1447755
  · exact B1447759
  · exact B1447763
  · exact B1447767
  · exact B1447771
  · exact B1447775
  · exact B1447779
  · exact B1447783
  · exact B1447787
  · exact B1447791
  · exact B1447795
  · exact B1447799
  · exact B1447803
  · exact B1447807
  · exact B1447811
  · exact B1447815
  · exact B1447819
  · exact B1447823
  · exact B1447827
  · exact B1447831
  · exact B1447835
  · exact B1447839
  · exact B1447843
  · exact B1447847
  · exact B1447851
  · exact B1447855
  · exact B1447859
  · exact B1447863
  · exact B1447867
  · exact B1447871
  · exact B1447875
  · exact B1447879
  · exact B1447883
  · exact B1447887
  · exact B1447891
  · exact B1447895
  · exact B1447899
  · exact B1447903
  · exact B1447907
  · exact B1447911
  · exact B1447915
  · exact B1447919
  · exact B1447923
  · exact B1447927
  · exact B1447931
  · exact B1447935
  · exact B1447939
  · exact B1447943
  · exact B1447947
  · exact B1447951
  · exact B1447955
  · exact B1447959
  · exact B1447963
  · exact B1447967
  · exact B1447971
  · exact B1447975
  · exact B1447979
  · exact B1447983
  · exact B1447987
  · exact B1447991
  · exact B1447995
  · exact B1447999
  · exact B1448003
  · exact B1448007
  · exact B1448011
  · exact B1448015
  · exact B1448019
  · exact B1448023
  · exact B1448027
  · exact B1448031
  · exact B1448035
  · exact B1448039
  · exact B1448043
  · exact B1448047
  · exact B1448051
  · exact B1448055
  · exact B1448059
  · exact B1448063
  · exact B1448067
  · exact B1448071
  · exact B1448075
  · exact B1448079
  · exact B1448083
  · exact B1448087
  · exact B1448091
  · exact B1448095
  · exact B1448099
  · exact B1448103
  · exact B1448107
  · exact B1448111
  · exact B1448115
  · exact B1448119
  · exact B1448123
  · exact B1448127
  · exact B1448131
  · exact B1448135
  · exact B1448139
  · exact B1448143
  · exact B1448147
  · exact B1448151
  · exact B1448155
  · exact B1448159
  · exact B1448163
  · exact B1448167
  · exact B1448171
  · exact B1448175
  · exact B1448179
  · exact B1448183
  · exact B1448187
  · exact B1448191
  · exact B1448195
  · exact B1448199
  · exact B1448203
  · exact B1448207
  · exact B1448211
  · exact B1448215
  · exact B1448219
  · exact B1448223
  · exact B1448227
  · exact B1448231
  · exact B1448235
  · exact B1448239
  · exact B1448243
  · exact B1448247
  · exact B1448251
  · exact B1448255
  · exact B1448259
  · exact B1448263
  · exact B1448267
  · exact B1448271
  · exact B1448275
  · exact B1448279
  · exact B1448283
  · exact B1448287
  · exact B1448291
  · exact B1448295
  · exact B1448299
  · exact B1448303
  · exact B1448307
  · exact B1448311
  · exact B1448315
  · exact B1448319
  · exact B1448323
  · exact B1448327
  · exact B1448331
  · exact B1448335
  · exact B1448339
  · exact B1448343
  · exact B1448347
  · exact B1448351
  · exact B1448355
  · exact B1448359
  · exact B1448363
  · exact B1448367
  · exact B1448371
  · exact B1448375
  · exact B1448379
  · exact B1448383
  · exact B1448387
  · exact B1448391
  · exact B1448395
  · exact B1448399
  · exact B1448403
  · exact B1448407
  · exact B1448411
  · exact B1448415
  · exact B1448419
  · exact B1448423
  · exact B1448427
  · exact B1448431
  · exact B1448435
  · exact B1448439
  · exact B1448443
  · exact B1448447
  · exact B1448451
  · exact B1448455
  · exact B1448459
  · exact B1448463
  · exact B1448467
  · exact B1448471
  · exact B1448475
  · exact B1448479
  · exact B1448483
  · exact B1448487
  · exact B1448491
  · exact B1448495
  · exact B1448499
  · exact B1448503
  · exact B1448507
  · exact B1448511
  · exact B1448515
  · exact B1448519
  · exact B1448523
  · exact B1448527
  · exact B1448531
  · exact B1448535
  · exact B1448539
  · exact B1448543
  · exact B1448547
  · exact B1448551
  · exact B1448555
  · exact B1448559
  · exact B1448563
  · exact B1448567
  · exact B1448571
  · exact B1448575
  · exact B1448579
  · exact B1448583
  · exact B1448587
  · exact B1448591
  · exact B1448595
  · exact B1448599
  · exact B1448603
  · exact B1448607
  · exact B1448611
  · exact B1448615
  · exact B1448619
  · exact B1448623
  · exact B1448627
  · exact B1448631
  · exact B1448635
  · exact B1448639
  · exact B1448643
  · exact B1448647
  · exact B1448651
  · exact B1448655
  · exact B1448659
  · exact B1448663
  · exact B1448667
  · exact B1448671
  · exact B1448675
  · exact B1448679
  · exact B1448683
  · exact B1448687
  · exact B1448691
  · exact B1448695
  · exact B1448699
  · exact B1448703
  · exact B1448707
  · exact B1448711
  · exact B1448715
  · exact B1448719
  · exact B1448723
  · exact B1448727
  · exact B1448731
  · exact B1448735
  · exact B1448739
  · exact B1448743
  · exact B1448747
  · exact B1448751
  · exact B1448755
  · exact B1448759
  · exact B1448763
  · exact B1448767
  · exact B1448771
  · exact B1448775
  · exact B1448779
  · exact B1448783
  · exact B1448787
  · exact B1448791
  · exact B1448795
  · exact B1448799
  · exact B1448803
  · exact B1448807
  · exact B1448811
  · exact B1448815
  · exact B1448819
  · exact B1448823
  · exact B1448827
  · exact B1448831
  · exact B1448835
  · exact B1448839
  · exact B1448843
  · exact B1448847
  · exact B1448851
  · exact B1448855
  · exact B1448859
  · exact B1448863
  · exact B1448867
  · exact B1448871
  · exact B1448875
  · exact B1448879
  · exact B1448883
  · exact B1448887
  · exact B1448891
  · exact B1448895
  · exact B1448899
  · exact B1448903
  · exact B1448907
  · exact B1448911
  · exact B1448915
  · exact B1448919
  · exact B1448923
  · exact B1448927
  · exact B1448931
  · exact B1448935
  · exact B1448939
  · exact B1448943
  · exact B1448947
  · exact B1448951
  · exact B1448955
  · exact B1448959
  · exact B1448963
  · exact B1448967
  · exact B1448971
  · exact B1448975
  · exact B1448979
  · exact B1448983
  · exact B1448987
  · exact B1448991
  · exact B1448995
  · exact B1448999
  · exact B1449003
  · exact B1449007
  · exact B1449011
  · exact B1449015
  · exact B1449019
  · exact B1449023
  · exact B1449027
  · exact B1449031
  · exact B1449035
  · exact B1449039
  · exact B1449043
  · exact B1449047
  · exact B1449051
  · exact B1449055
  · exact B1449059
  · exact B1449063
  · exact B1449067
  · exact B1449071
  · exact B1449075
  · exact B1449079
  · exact B1449083
  · exact B1449087
  · exact B1449091
  · exact B1449095
  · exact B1449099
  · exact B1449103
  · exact B1449107
  · exact B1449111
  · exact B1449115
  · exact B1449119
  · exact B1449123
  · exact B1449127
  · exact B1449131
  · exact B1449135
  · exact B1449139
  · exact B1449143
  · exact B1449147
  · exact B1449151
  · exact B1449155
  · exact B1449159
  · exact B1449163
  · exact B1449167
  · exact B1449171
  · exact B1449175
  · exact B1449179
  · exact B1449183
  · exact B1449187
  · exact B1449191
  · exact B1449195
  · exact B1449199
  · exact B1449203
  · exact B1449207
  · exact B1449211
  · exact B1449215
  · exact B1449219
  · exact B1449223
  · exact B1449227
  · exact B1449231
  · exact B1449235
  · exact B1449239
  · exact B1449243
  · exact B1449247
  · exact B1449251
  · exact B1449255
  · exact B1449259
  · exact B1449263
  · exact B1449267
  · exact B1449271
  · exact B1449275
  · exact B1449279
  · exact B1449283
  · exact B1449287
  · exact B1449291
  · exact B1449295
  · exact B1449299
  · exact B1449303
  · exact B1449307
  · exact B1449311
  · exact B1449315
  · exact B1449319
  · exact B1449323
  · exact B1449327
  · exact B1449331
  · exact B1449335
  · exact B1449339
  · exact B1449343
  · exact B1449347
  · exact B1449351
  · exact B1449355
  · exact B1449359
  · exact B1449363
  · exact B1449367
  · exact B1449371
  · exact B1449375
  · exact B1449379
  · exact B1449383
  · exact B1449387
  · exact B1449391
  · exact B1449395
  · exact B1449399
  · exact B1449403
  · exact B1449407
  · exact B1449411
  · exact B1449415
  · exact B1449419
  · exact B1449423
  · exact B1449427
  · exact B1449431
  · exact B1449435
  · exact B1449439
  · exact B1449443
  · exact B1449447
  · exact B1449451
  · exact B1449455
  · exact B1449459
  · exact B1449463
  · exact B1449467
  · exact B1449471
  · exact B1449475
  · exact B1449479
  · exact B1449483
  · exact B1449487
  · exact B1449491
  · exact B1449495
  · exact B1449499
  · exact B1449503
  · exact B1449507
  · exact B1449511
  · exact B1449515
  · exact B1449519
  · exact B1449523
  · exact B1449527
  · exact B1449531
  · exact B1449535
  · exact B1449539
  · exact B1449543

theorem solution (m : ℕ) (hlo : 1447543 ≤ m) (hhi : m ≤ 1449543) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 361885 ≤ j := by omega
    have hj2 : j ≤ 362385 := by omega
    have hb : Blo 1447543 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
