-- Prove2me | solution 1 for syracuse_descends_range_1843623_1845623
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T01:04:42.172846+00:00
-- url     : https://prove2.me/submissions/41fd5d40-ea29-4110-85a5-07c4a13150c5

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


theorem B3416077 : Blo 1843623 3416077 := bbase (se 3 (by rfl) ⟨640514, by rfl⟩ : syracuseStep 3416077 = 1281029) (by norm_num)
theorem B10510357 : Blo 1843623 10510357 := bbase (se 6 (by rfl) ⟨246336, by rfl⟩ : syracuseStep 10510357 = 492673) (by norm_num)
theorem B3113005 : Blo 1843623 3113005 := bbase (se 3 (by rfl) ⟨583688, by rfl⟩ : syracuseStep 3113005 = 1167377) (by norm_num)
theorem B4431925 : Blo 1843623 4431925 := bbase (se 5 (by rfl) ⟨207746, by rfl⟩ : syracuseStep 4431925 = 415493) (by norm_num)
theorem B5611589 : Blo 1843623 5611589 := bbase (se 4 (by rfl) ⟨526086, by rfl⟩ : syracuseStep 5611589 = 1052173) (by norm_num)
theorem B6226037 : Blo 1843623 6226037 := bbase (se 5 (by rfl) ⟨291845, by rfl⟩ : syracuseStep 6226037 = 583691) (by norm_num)
theorem B2334845 : Blo 1843623 2334845 := bbase (se 3 (by rfl) ⟨437783, by rfl⟩ : syracuseStep 2334845 = 875567) (by norm_num)
theorem B3113093 : Blo 1843623 3113093 := bbase (se 4 (by rfl) ⟨291852, by rfl⟩ : syracuseStep 3113093 = 583705) (by norm_num)
theorem B4669589 : Blo 1843623 4669589 := bbase (se 6 (by rfl) ⟨109443, by rfl⟩ : syracuseStep 4669589 = 218887) (by norm_num)
theorem B2334901 : Blo 1843623 2334901 := bbase (se 5 (by rfl) ⟨109448, by rfl⟩ : syracuseStep 2334901 = 218897) (by norm_num)
theorem B3113221 : Blo 1843623 3113221 := bbase (se 4 (by rfl) ⟨291864, by rfl⟩ : syracuseStep 3113221 = 583729) (by norm_num)
theorem B2334997 : Blo 1843623 2334997 := bbase (se 6 (by rfl) ⟨54726, by rfl⟩ : syracuseStep 2334997 = 109453) (by norm_num)
theorem B3113309 : Blo 1843623 3113309 := bbase (se 3 (by rfl) ⟨583745, by rfl⟩ : syracuseStep 3113309 = 1167491) (by norm_num)
theorem B8864117 : Blo 1843623 8864117 := bbase (se 5 (by rfl) ⟨415505, by rfl⟩ : syracuseStep 8864117 = 831011) (by norm_num)
theorem B5906837 : Blo 1843623 5906837 := bbase (se 6 (by rfl) ⟨138441, by rfl⟩ : syracuseStep 5906837 = 276883) (by norm_num)
theorem B2335169 : Blo 1843623 2335169 := bbase (se 2 (by rfl) ⟨875688, by rfl⟩ : syracuseStep 2335169 = 1751377) (by norm_num)
theorem B3113437 : Blo 1843623 3113437 := bbase (se 3 (by rfl) ⟨583769, by rfl⟩ : syracuseStep 3113437 = 1167539) (by norm_num)
theorem B4669933 : Blo 1843623 4669933 := bbase (se 3 (by rfl) ⟨875612, by rfl⟩ : syracuseStep 4669933 = 1751225) (by norm_num)
theorem B2335225 : Blo 1843623 2335225 := bbase (se 2 (by rfl) ⟨875709, by rfl⟩ : syracuseStep 2335225 = 1751419) (by norm_num)
theorem B6226469 : Blo 1843623 6226469 := bbase (se 4 (by rfl) ⟨583731, by rfl⟩ : syracuseStep 6226469 = 1167463) (by norm_num)
theorem B9970229 : Blo 1843623 9970229 := bbase (se 5 (by rfl) ⟨467354, by rfl⟩ : syracuseStep 9970229 = 934709) (by norm_num)
theorem B3113525 : Blo 1843623 3113525 := bbase (se 5 (by rfl) ⟨145946, by rfl⟩ : syracuseStep 3113525 = 291893) (by norm_num)
theorem B9339461 : Blo 1843623 9339461 := bbase (se 4 (by rfl) ⟨875574, by rfl⟩ : syracuseStep 9339461 = 1751149) (by norm_num)
theorem B2335321 : Blo 1843623 2335321 := bbase (se 2 (by rfl) ⟨875745, by rfl⟩ : syracuseStep 2335321 = 1751491) (by norm_num)
theorem B4670045 : Blo 1843623 4670045 := bbase (se 3 (by rfl) ⟨875633, by rfl⟩ : syracuseStep 4670045 = 1751267) (by norm_num)
theorem B14008949 : Blo 1843623 14008949 := bbase (se 5 (by rfl) ⟨656669, by rfl⟩ : syracuseStep 14008949 = 1313339) (by norm_num)
theorem B3113653 : Blo 1843623 3113653 := bbase (se 5 (by rfl) ⟨145952, by rfl⟩ : syracuseStep 3113653 = 291905) (by norm_num)
theorem B3154637 : Blo 1843623 3154637 := bbase (se 3 (by rfl) ⟨591494, by rfl⟩ : syracuseStep 3154637 = 1182989) (by norm_num)
theorem B4432589 : Blo 1843623 4432589 := bbase (se 3 (by rfl) ⟨831110, by rfl⟩ : syracuseStep 4432589 = 1662221) (by norm_num)
theorem B18924245 : Blo 1843623 18924245 := bbase (se 7 (by rfl) ⟨221768, by rfl⟩ : syracuseStep 18924245 = 443537) (by norm_num)
theorem B3941077 : Blo 1843623 3941077 := bbase (se 7 (by rfl) ⟨46184, by rfl⟩ : syracuseStep 3941077 = 92369) (by norm_num)
theorem B53207765 : Blo 1843623 53207765 := bbase (se 7 (by rfl) ⟨623528, by rfl⟩ : syracuseStep 53207765 = 1247057) (by norm_num)
theorem B2335493 : Blo 1843623 2335493 := bbase (se 4 (by rfl) ⟨218952, by rfl⟩ : syracuseStep 2335493 = 437905) (by norm_num)
theorem B3113741 : Blo 1843623 3113741 := bbase (se 3 (by rfl) ⟨583826, by rfl⟩ : syracuseStep 3113741 = 1167653) (by norm_num)
theorem B4670237 : Blo 1843623 4670237 := bbase (se 3 (by rfl) ⟨875669, by rfl⟩ : syracuseStep 4670237 = 1751339) (by norm_num)
theorem B2335549 : Blo 1843623 2335549 := bbase (se 3 (by rfl) ⟨437915, by rfl⟩ : syracuseStep 2335549 = 875831) (by norm_num)
theorem B23634773 : Blo 1843623 23634773 := bbase (se 9 (by rfl) ⟨69242, by rfl⟩ : syracuseStep 23634773 = 138485) (by norm_num)
theorem B3113869 : Blo 1843623 3113869 := bbase (se 3 (by rfl) ⟨583850, by rfl⟩ : syracuseStep 3113869 = 1167701) (by norm_num)
theorem B2335645 : Blo 1843623 2335645 := bbase (se 3 (by rfl) ⟨437933, by rfl⟩ : syracuseStep 2335645 = 875867) (by norm_num)
theorem B2245573 : Blo 1843623 2245573 := bbase (se 4 (by rfl) ⟨210522, by rfl⟩ : syracuseStep 2245573 = 421045) (by norm_num)
theorem B6226901 : Blo 1843623 6226901 := bbase (se 7 (by rfl) ⟨72971, by rfl⟩ : syracuseStep 6226901 = 145943) (by norm_num)
theorem B3113957 : Blo 1843623 3113957 := bbase (se 4 (by rfl) ⟨291933, by rfl⟩ : syracuseStep 3113957 = 583867) (by norm_num)
theorem B3548173 : Blo 1843623 3548173 := bbase (se 3 (by rfl) ⟨665282, by rfl⟩ : syracuseStep 3548173 = 1330565) (by norm_num)
theorem B14001173 : Blo 1843623 14001173 := bbase (se 6 (by rfl) ⟨328152, by rfl⟩ : syracuseStep 14001173 = 656305) (by norm_num)
theorem B2335817 : Blo 1843623 2335817 := bbase (se 2 (by rfl) ⟨875931, by rfl⟩ : syracuseStep 2335817 = 1751863) (by norm_num)
theorem B3941453 : Blo 1843623 3941453 := bbase (se 3 (by rfl) ⟨739022, by rfl⟩ : syracuseStep 3941453 = 1478045) (by norm_num)
theorem B2663509 : Blo 1843623 2663509 := bbase (se 8 (by rfl) ⟨15606, by rfl⟩ : syracuseStep 2663509 = 31213) (by norm_num)
theorem B3114085 : Blo 1843623 3114085 := bbase (se 4 (by rfl) ⟨291945, by rfl⟩ : syracuseStep 3114085 = 583891) (by norm_num)
theorem B4670581 : Blo 1843623 4670581 := bbase (se 5 (by rfl) ⟨218933, by rfl⟩ : syracuseStep 4670581 = 437867) (by norm_num)
theorem B3114173 : Blo 1843623 3114173 := bbase (se 3 (by rfl) ⟨583907, by rfl⟩ : syracuseStep 3114173 = 1167815) (by norm_num)
theorem B5252309 : Blo 1843623 5252309 := bbase (se 7 (by rfl) ⟨61550, by rfl⟩ : syracuseStep 5252309 = 123101) (by norm_num)
theorem B56796373 : Blo 1843623 56796373 := bbase (se 7 (by rfl) ⟨665582, by rfl⟩ : syracuseStep 56796373 = 1331165) (by norm_num)
theorem B3548389 : Blo 1843623 3548389 := bbase (se 4 (by rfl) ⟨332661, by rfl⟩ : syracuseStep 3548389 = 665323) (by norm_num)
theorem B4670693 : Blo 1843623 4670693 := bbase (se 4 (by rfl) ⟨437877, by rfl⟩ : syracuseStep 4670693 = 875755) (by norm_num)
theorem B3114301 : Blo 1843623 3114301 := bbase (se 3 (by rfl) ⟨583931, by rfl⟩ : syracuseStep 3114301 = 1167863) (by norm_num)
theorem B12617045 : Blo 1843623 12617045 := bbase (se 12 (by rfl) ⟨4620, by rfl⟩ : syracuseStep 12617045 = 9241) (by norm_num)
theorem B7882069 : Blo 1843623 7882069 := bbase (se 12 (by rfl) ⟨2886, by rfl⟩ : syracuseStep 7882069 = 5773) (by norm_num)
theorem B7882085 : Blo 1843623 7882085 := bbase (se 4 (by rfl) ⟨738945, by rfl⟩ : syracuseStep 7882085 = 1477891) (by norm_num)
theorem B6227333 : Blo 1843623 6227333 := bbase (se 4 (by rfl) ⟨583812, by rfl⟩ : syracuseStep 6227333 = 1167625) (by norm_num)
theorem B3114389 : Blo 1843623 3114389 := bbase (se 6 (by rfl) ⟨72993, by rfl⟩ : syracuseStep 3114389 = 145987) (by norm_num)
theorem B4670885 : Blo 1843623 4670885 := bbase (se 4 (by rfl) ⟨437895, by rfl⟩ : syracuseStep 4670885 = 875791) (by norm_num)
theorem B2074081 : Blo 1843623 2074081 := bbase (se 2 (by rfl) ⟨777780, by rfl⟩ : syracuseStep 2074081 = 1555561) (by norm_num)
theorem B2074117 : Blo 1843623 2074117 := bbase (se 4 (by rfl) ⟨194448, by rfl⟩ : syracuseStep 2074117 = 388897) (by norm_num)
theorem B2074153 : Blo 1843623 2074153 := bbase (se 2 (by rfl) ⟨777807, by rfl⟩ : syracuseStep 2074153 = 1555615) (by norm_num)
theorem B2074189 : Blo 1843623 2074189 := bbase (se 3 (by rfl) ⟨388910, by rfl⟩ : syracuseStep 2074189 = 777821) (by norm_num)
theorem B7005797 : Blo 1843623 7005797 := bbase (se 4 (by rfl) ⟨656793, by rfl⟩ : syracuseStep 7005797 = 1313587) (by norm_num)
theorem B2074225 : Blo 1843623 2074225 := bbase (se 2 (by rfl) ⟨777834, by rfl⟩ : syracuseStep 2074225 = 1555669) (by norm_num)
theorem B5760629 : Blo 1843623 5760629 := bbase (se 5 (by rfl) ⟨270029, by rfl⟩ : syracuseStep 5760629 = 540059) (by norm_num)
theorem B2074261 : Blo 1843623 2074261 := bbase (se 6 (by rfl) ⟨48615, by rfl⟩ : syracuseStep 2074261 = 97231) (by norm_num)
theorem B2074297 : Blo 1843623 2074297 := bbase (se 2 (by rfl) ⟨777861, by rfl⟩ : syracuseStep 2074297 = 1555723) (by norm_num)
theorem B2074333 : Blo 1843623 2074333 := bbase (se 3 (by rfl) ⟨388937, by rfl⟩ : syracuseStep 2074333 = 777875) (by norm_num)
theorem B4671229 : Blo 1843623 4671229 := bbase (se 3 (by rfl) ⟨875855, by rfl⟩ : syracuseStep 4671229 = 1751711) (by norm_num)
theorem B2074369 : Blo 1843623 2074369 := bbase (se 2 (by rfl) ⟨777888, by rfl⟩ : syracuseStep 2074369 = 1555777) (by norm_num)
theorem B2074405 : Blo 1843623 2074405 := bbase (se 4 (by rfl) ⟨194475, by rfl⟩ : syracuseStep 2074405 = 388951) (by norm_num)
theorem B6227765 : Blo 1843623 6227765 := bbase (se 5 (by rfl) ⟨291926, by rfl⟩ : syracuseStep 6227765 = 583853) (by norm_num)
theorem B2074441 : Blo 1843623 2074441 := bbase (se 2 (by rfl) ⟨777915, by rfl⟩ : syracuseStep 2074441 = 1555831) (by norm_num)
theorem B9340757 : Blo 1843623 9340757 := bbase (se 9 (by rfl) ⟨27365, by rfl⟩ : syracuseStep 9340757 = 54731) (by norm_num)
theorem B2074477 : Blo 1843623 2074477 := bbase (se 3 (by rfl) ⟨388964, by rfl⟩ : syracuseStep 2074477 = 777929) (by norm_num)
theorem B4671341 : Blo 1843623 4671341 := bbase (se 3 (by rfl) ⟨875876, by rfl⟩ : syracuseStep 4671341 = 1751753) (by norm_num)
theorem B3549053 : Blo 1843623 3549053 := bbase (se 3 (by rfl) ⟨665447, by rfl⟩ : syracuseStep 3549053 = 1330895) (by norm_num)
theorem B7006085 : Blo 1843623 7006085 := bbase (se 4 (by rfl) ⟨656820, by rfl⟩ : syracuseStep 7006085 = 1313641) (by norm_num)
theorem B2074513 : Blo 1843623 2074513 := bbase (se 2 (by rfl) ⟨777942, by rfl⟩ : syracuseStep 2074513 = 1555885) (by norm_num)
theorem B14960533 : Blo 1843623 14960533 := bbase (se 6 (by rfl) ⟨350637, by rfl⟩ : syracuseStep 14960533 = 701275) (by norm_num)
theorem B15763349 : Blo 1843623 15763349 := bbase (se 6 (by rfl) ⟨369453, by rfl⟩ : syracuseStep 15763349 = 738907) (by norm_num)
theorem B2074549 : Blo 1843623 2074549 := bbase (se 5 (by rfl) ⟨97244, by rfl⟩ : syracuseStep 2074549 = 194489) (by norm_num)
theorem B8865733 : Blo 1843623 8865733 := bbase (se 4 (by rfl) ⟨831162, by rfl⟩ : syracuseStep 8865733 = 1662325) (by norm_num)
theorem B2074585 : Blo 1843623 2074585 := bbase (se 2 (by rfl) ⟨777969, by rfl⟩ : syracuseStep 2074585 = 1555939) (by norm_num)
theorem B3500005 : Blo 1843623 3500005 := bbase (se 4 (by rfl) ⟨328125, by rfl⟩ : syracuseStep 3500005 = 656251) (by norm_num)
theorem B2074621 : Blo 1843623 2074621 := bbase (se 3 (by rfl) ⟨388991, by rfl⟩ : syracuseStep 2074621 = 777983) (by norm_num)
theorem B29919253 : Blo 1843623 29919253 := bbase (se 6 (by rfl) ⟨701232, by rfl⟩ : syracuseStep 29919253 = 1402465) (by norm_num)
theorem B2074657 : Blo 1843623 2074657 := bbase (se 2 (by rfl) ⟨777996, by rfl⟩ : syracuseStep 2074657 = 1555993) (by norm_num)
theorem B4671533 : Blo 1843623 4671533 := bbase (se 3 (by rfl) ⟨875912, by rfl⟩ : syracuseStep 4671533 = 1751825) (by norm_num)
theorem B2074693 : Blo 1843623 2074693 := bbase (se 4 (by rfl) ⟨194502, by rfl⟩ : syracuseStep 2074693 = 389005) (by norm_num)
theorem B3737701 : Blo 1843623 3737701 := bbase (se 4 (by rfl) ⟨350409, by rfl⟩ : syracuseStep 3737701 = 700819) (by norm_num)
theorem B2074729 : Blo 1843623 2074729 := bbase (se 2 (by rfl) ⟨778023, by rfl⟩ : syracuseStep 2074729 = 1556047) (by norm_num)
theorem B3500165 : Blo 1843623 3500165 := bbase (se 4 (by rfl) ⟨328140, by rfl⟩ : syracuseStep 3500165 = 656281) (by norm_num)
theorem B2074765 : Blo 1843623 2074765 := bbase (se 3 (by rfl) ⟨389018, by rfl⟩ : syracuseStep 2074765 = 778037) (by norm_num)
theorem B2074801 : Blo 1843623 2074801 := bbase (se 2 (by rfl) ⟨778050, by rfl⟩ : syracuseStep 2074801 = 1556101) (by norm_num)
theorem B2074837 : Blo 1843623 2074837 := bbase (se 7 (by rfl) ⟨24314, by rfl⟩ : syracuseStep 2074837 = 48629) (by norm_num)
theorem B6228197 : Blo 1843623 6228197 := bbase (se 4 (by rfl) ⟨583893, by rfl⟩ : syracuseStep 6228197 = 1167787) (by norm_num)
theorem B2074873 : Blo 1843623 2074873 := bbase (se 2 (by rfl) ⟨778077, by rfl⟩ : syracuseStep 2074873 = 1556155) (by norm_num)
theorem B2803981 : Blo 1843623 2803981 := bbase (se 3 (by rfl) ⟨525746, by rfl⟩ : syracuseStep 2803981 = 1051493) (by norm_num)
theorem B3500309 : Blo 1843623 3500309 := bbase (se 6 (by rfl) ⟨82038, by rfl⟩ : syracuseStep 3500309 = 164077) (by norm_num)
theorem B2074909 : Blo 1843623 2074909 := bbase (se 3 (by rfl) ⟨389045, by rfl⟩ : syracuseStep 2074909 = 778091) (by norm_num)
theorem B2074945 : Blo 1843623 2074945 := bbase (se 2 (by rfl) ⟨778104, by rfl⟩ : syracuseStep 2074945 = 1556209) (by norm_num)
theorem B2074981 : Blo 1843623 2074981 := bbase (se 4 (by rfl) ⟨194529, by rfl⟩ : syracuseStep 2074981 = 389059) (by norm_num)
theorem B5253493 : Blo 1843623 5253493 := bbase (se 5 (by rfl) ⟨246257, by rfl⟩ : syracuseStep 5253493 = 492515) (by norm_num)
theorem B2075017 : Blo 1843623 2075017 := bbase (se 2 (by rfl) ⟨778131, by rfl⟩ : syracuseStep 2075017 = 1556263) (by norm_num)
theorem B18925973 : Blo 1843623 18925973 := bbase (se 6 (by rfl) ⟨443577, by rfl⟩ : syracuseStep 18925973 = 887155) (by norm_num)
theorem B2075053 : Blo 1843623 2075053 := bbase (se 3 (by rfl) ⟨389072, by rfl⟩ : syracuseStep 2075053 = 778145) (by norm_num)
theorem B4434365 : Blo 1843623 4434365 := bbase (se 3 (by rfl) ⟨831443, by rfl⟩ : syracuseStep 4434365 = 1662887) (by norm_num)
theorem B2075089 : Blo 1843623 2075089 := bbase (se 2 (by rfl) ⟨778158, by rfl⟩ : syracuseStep 2075089 = 1556317) (by norm_num)
theorem B2075125 : Blo 1843623 2075125 := bbase (se 5 (by rfl) ⟨97271, by rfl⟩ : syracuseStep 2075125 = 194543) (by norm_num)
theorem B5327365 : Blo 1843623 5327365 := bbase (se 4 (by rfl) ⟨499440, by rfl⟩ : syracuseStep 5327365 = 998881) (by norm_num)
theorem B5253653 : Blo 1843623 5253653 := bbase (se 6 (by rfl) ⟨123132, by rfl⟩ : syracuseStep 5253653 = 246265) (by norm_num)
theorem B2075161 : Blo 1843623 2075161 := bbase (se 2 (by rfl) ⟨778185, by rfl⟩ : syracuseStep 2075161 = 1556371) (by norm_num)
theorem B3500597 : Blo 1843623 3500597 := bbase (se 5 (by rfl) ⟨164090, by rfl⟩ : syracuseStep 3500597 = 328181) (by norm_num)
theorem B2075197 : Blo 1843623 2075197 := bbase (se 3 (by rfl) ⟨389099, by rfl⟩ : syracuseStep 2075197 = 778199) (by norm_num)
theorem B2075233 : Blo 1843623 2075233 := bbase (se 2 (by rfl) ⟨778212, by rfl⟩ : syracuseStep 2075233 = 1556425) (by norm_num)
theorem B7096949 : Blo 1843623 7096949 := bbase (se 5 (by rfl) ⟨332669, by rfl⟩ : syracuseStep 7096949 = 665339) (by norm_num)
theorem B11815541 : Blo 1843623 11815541 := bbase (se 5 (by rfl) ⟨553853, by rfl⟩ : syracuseStep 11815541 = 1107707) (by norm_num)
theorem B2075269 : Blo 1843623 2075269 := bbase (se 4 (by rfl) ⟨194556, by rfl⟩ : syracuseStep 2075269 = 389113) (by norm_num)
theorem B6228629 : Blo 1843623 6228629 := bbase (se 6 (by rfl) ⟨145983, by rfl⟩ : syracuseStep 6228629 = 291967) (by norm_num)
theorem B1870489 : Blo 1843623 1870489 := bbase (se 2 (by rfl) ⟨701433, by rfl⟩ : syracuseStep 1870489 = 1402867) (by norm_num)
theorem B2075305 : Blo 1843623 2075305 := bbase (se 2 (by rfl) ⟨778239, by rfl⟩ : syracuseStep 2075305 = 1556479) (by norm_num)
theorem B3500749 : Blo 1843623 3500749 := bbase (se 3 (by rfl) ⟨656390, by rfl⟩ : syracuseStep 3500749 = 1312781) (by norm_num)
theorem B2075341 : Blo 1843623 2075341 := bbase (se 3 (by rfl) ⟨389126, by rfl⟩ : syracuseStep 2075341 = 778253) (by norm_num)
theorem B1968877 : Blo 1843623 1968877 := bbase (se 3 (by rfl) ⟨369164, by rfl⟩ : syracuseStep 1968877 = 738329) (by norm_num)
theorem B1968881 : Blo 1843623 1968881 := bbase (se 2 (by rfl) ⟨738330, by rfl⟩ : syracuseStep 1968881 = 1476661) (by norm_num)
theorem B2075377 : Blo 1843623 2075377 := bbase (se 2 (by rfl) ⟨778266, by rfl⟩ : syracuseStep 2075377 = 1556533) (by norm_num)
theorem B5253893 : Blo 1843623 5253893 := bbase (se 4 (by rfl) ⟨492552, by rfl⟩ : syracuseStep 5253893 = 985105) (by norm_num)
theorem B2075413 : Blo 1843623 2075413 := bbase (se 6 (by rfl) ⟨48642, by rfl⟩ : syracuseStep 2075413 = 97285) (by norm_num)
theorem B7482149 : Blo 1843623 7482149 := bbase (se 4 (by rfl) ⟨701451, by rfl⟩ : syracuseStep 7482149 = 1402903) (by norm_num)
theorem B2075449 : Blo 1843623 2075449 := bbase (se 2 (by rfl) ⟨778293, by rfl⟩ : syracuseStep 2075449 = 1556587) (by norm_num)
theorem B2075485 : Blo 1843623 2075485 := bbase (se 3 (by rfl) ⟨389153, by rfl⟩ : syracuseStep 2075485 = 778307) (by norm_num)
theorem B2075521 : Blo 1843623 2075521 := bbase (se 2 (by rfl) ⟨778320, by rfl⟩ : syracuseStep 2075521 = 1556641) (by norm_num)
theorem B2075557 : Blo 1843623 2075557 := bbase (se 4 (by rfl) ⟨194583, by rfl⟩ : syracuseStep 2075557 = 389167) (by norm_num)
theorem B5254085 : Blo 1843623 5254085 := bbase (se 4 (by rfl) ⟨492570, by rfl⟩ : syracuseStep 5254085 = 985141) (by norm_num)
theorem B2075593 : Blo 1843623 2075593 := bbase (se 2 (by rfl) ⟨778347, by rfl⟩ : syracuseStep 2075593 = 1556695) (by norm_num)
theorem B4148189 : Blo 1843623 4148189 := bbase (se 3 (by rfl) ⟨777785, by rfl⟩ : syracuseStep 4148189 = 1555571) (by norm_num)
theorem B2075629 : Blo 1843623 2075629 := bbase (se 3 (by rfl) ⟨389180, by rfl⟩ : syracuseStep 2075629 = 778361) (by norm_num)
theorem B3501053 : Blo 1843623 3501053 := bbase (se 3 (by rfl) ⟨656447, by rfl⟩ : syracuseStep 3501053 = 1312895) (by norm_num)
theorem B2075665 : Blo 1843623 2075665 := bbase (se 2 (by rfl) ⟨778374, by rfl⟩ : syracuseStep 2075665 = 1556749) (by norm_num)
theorem B4148261 : Blo 1843623 4148261 := bbase (se 4 (by rfl) ⟨388899, by rfl⟩ : syracuseStep 4148261 = 777799) (by norm_num)
theorem B7007269 : Blo 1843623 7007269 := bbase (se 4 (by rfl) ⟨656931, by rfl⟩ : syracuseStep 7007269 = 1313863) (by norm_num)
theorem B2075701 : Blo 1843623 2075701 := bbase (se 5 (by rfl) ⟨97298, by rfl⟩ : syracuseStep 2075701 = 194597) (by norm_num)
theorem B4320325 : Blo 1843623 4320325 := bbase (se 4 (by rfl) ⟨405030, by rfl⟩ : syracuseStep 4320325 = 810061) (by norm_num)
theorem B2075737 : Blo 1843623 2075737 := bbase (se 2 (by rfl) ⟨778401, by rfl⟩ : syracuseStep 2075737 = 1556803) (by norm_num)
theorem B9342053 : Blo 1843623 9342053 := bbase (se 4 (by rfl) ⟨875817, by rfl⟩ : syracuseStep 9342053 = 1751635) (by norm_num)
theorem B4148333 : Blo 1843623 4148333 := bbase (se 3 (by rfl) ⟨777812, by rfl⟩ : syracuseStep 4148333 = 1555625) (by norm_num)
theorem B2075773 : Blo 1843623 2075773 := bbase (se 3 (by rfl) ⟨389207, by rfl⟩ : syracuseStep 2075773 = 778415) (by norm_num)
theorem B3599509 : Blo 1843623 3599509 := bbase (se 6 (by rfl) ⟨84363, by rfl⟩ : syracuseStep 3599509 = 168727) (by norm_num)
theorem B2075809 : Blo 1843623 2075809 := bbase (se 2 (by rfl) ⟨778428, by rfl⟩ : syracuseStep 2075809 = 1556857) (by norm_num)
theorem B5909669 : Blo 1843623 5909669 := bbase (se 4 (by rfl) ⟨554031, by rfl⟩ : syracuseStep 5909669 = 1108063) (by norm_num)
theorem B4148405 : Blo 1843623 4148405 := bbase (se 5 (by rfl) ⟨194456, by rfl⟩ : syracuseStep 4148405 = 388913) (by norm_num)
theorem B2075845 : Blo 1843623 2075845 := bbase (se 4 (by rfl) ⟨194610, by rfl⟩ : syracuseStep 2075845 = 389221) (by norm_num)
theorem B2215145 : Blo 1843623 2215145 := bbase (se 2 (by rfl) ⟨830679, by rfl⟩ : syracuseStep 2215145 = 1661359) (by norm_num)
theorem B2075881 : Blo 1843623 2075881 := bbase (se 2 (by rfl) ⟨778455, by rfl⟩ : syracuseStep 2075881 = 1556911) (by norm_num)
theorem B4148477 : Blo 1843623 4148477 := bbase (se 3 (by rfl) ⟨777839, by rfl⟩ : syracuseStep 4148477 = 1555679) (by norm_num)
theorem B2075917 : Blo 1843623 2075917 := bbase (se 3 (by rfl) ⟨389234, by rfl⟩ : syracuseStep 2075917 = 778469) (by norm_num)
theorem B2493725 : Blo 1843623 2493725 := bbase (se 3 (by rfl) ⟨467573, by rfl⟩ : syracuseStep 2493725 = 935147) (by norm_num)
theorem B1969445 : Blo 1843623 1969445 := bbase (se 4 (by rfl) ⟨184635, by rfl⟩ : syracuseStep 1969445 = 369271) (by norm_num)
theorem B2075953 : Blo 1843623 2075953 := bbase (se 2 (by rfl) ⟨778482, by rfl⟩ : syracuseStep 2075953 = 1556965) (by norm_num)
theorem B4148549 : Blo 1843623 4148549 := bbase (se 4 (by rfl) ⟨388926, by rfl⟩ : syracuseStep 4148549 = 777853) (by norm_num)
theorem B56773973 : Blo 1843623 56773973 := bbase (se 11 (by rfl) ⟨41582, by rfl⟩ : syracuseStep 56773973 = 83165) (by norm_num)
theorem B2075989 : Blo 1843623 2075989 := bbase (se 11 (by rfl) ⟨1520, by rfl⟩ : syracuseStep 2075989 = 3041) (by norm_num)
theorem B7007573 : Blo 1843623 7007573 := bbase (se 11 (by rfl) ⟨5132, by rfl⟩ : syracuseStep 7007573 = 10265) (by norm_num)
theorem B2076025 : Blo 1843623 2076025 := bbase (se 2 (by rfl) ⟨778509, by rfl⟩ : syracuseStep 2076025 = 1557019) (by norm_num)
theorem B4148621 : Blo 1843623 4148621 := bbase (se 3 (by rfl) ⟨777866, by rfl⟩ : syracuseStep 4148621 = 1555733) (by norm_num)
theorem B2076061 : Blo 1843623 2076061 := bbase (se 3 (by rfl) ⟨389261, by rfl⟩ : syracuseStep 2076061 = 778523) (by norm_num)
theorem B2076097 : Blo 1843623 2076097 := bbase (se 2 (by rfl) ⟨778536, by rfl⟩ : syracuseStep 2076097 = 1557073) (by norm_num)
theorem B6311365 : Blo 1843623 6311365 := bbase (se 4 (by rfl) ⟨591690, by rfl⟩ : syracuseStep 6311365 = 1183381) (by norm_num)
theorem B4148693 : Blo 1843623 4148693 := bbase (se 7 (by rfl) ⟨48617, by rfl⟩ : syracuseStep 4148693 = 97235) (by norm_num)
theorem B1969633 : Blo 1843623 1969633 := bbase (se 2 (by rfl) ⟨738612, by rfl⟩ : syracuseStep 1969633 = 1477225) (by norm_num)
theorem B2076133 : Blo 1843623 2076133 := bbase (se 4 (by rfl) ⟨194637, by rfl⟩ : syracuseStep 2076133 = 389275) (by norm_num)
theorem B9334277 : Blo 1843623 9334277 := bbase (se 4 (by rfl) ⟨875088, by rfl⟩ : syracuseStep 9334277 = 1750177) (by norm_num)
theorem B2076169 : Blo 1843623 2076169 := bbase (se 2 (by rfl) ⟨778563, by rfl⟩ : syracuseStep 2076169 = 1557127) (by norm_num)
theorem B4148765 : Blo 1843623 4148765 := bbase (se 3 (by rfl) ⟨777893, by rfl⟩ : syracuseStep 4148765 = 1555787) (by norm_num)
theorem B2215453 : Blo 1843623 2215453 := bbase (se 3 (by rfl) ⟨415397, by rfl⟩ : syracuseStep 2215453 = 830795) (by norm_num)
theorem B2625061 : Blo 1843623 2625061 := bbase (se 4 (by rfl) ⟨246099, by rfl⟩ : syracuseStep 2625061 = 492199) (by norm_num)
theorem B2076205 : Blo 1843623 2076205 := bbase (se 3 (by rfl) ⟨389288, by rfl⟩ : syracuseStep 2076205 = 778577) (by norm_num)
theorem B2076241 : Blo 1843623 2076241 := bbase (se 2 (by rfl) ⟨778590, by rfl⟩ : syracuseStep 2076241 = 1557181) (by norm_num)
theorem B4148837 : Blo 1843623 4148837 := bbase (se 4 (by rfl) ⟨388953, by rfl⟩ : syracuseStep 4148837 = 777907) (by norm_num)
theorem B2076277 : Blo 1843623 2076277 := bbase (se 5 (by rfl) ⟨97325, by rfl⟩ : syracuseStep 2076277 = 194651) (by norm_num)
theorem B2215549 : Blo 1843623 2215549 := bbase (se 3 (by rfl) ⟨415415, by rfl⟩ : syracuseStep 2215549 = 830831) (by norm_num)
theorem B2076313 : Blo 1843623 2076313 := bbase (se 2 (by rfl) ⟨778617, by rfl⟩ : syracuseStep 2076313 = 1557235) (by norm_num)
theorem B4148909 : Blo 1843623 4148909 := bbase (se 3 (by rfl) ⟨777920, by rfl⟩ : syracuseStep 4148909 = 1555841) (by norm_num)
theorem B7876277 : Blo 1843623 7876277 := bbase (se 5 (by rfl) ⟨369200, by rfl⟩ : syracuseStep 7876277 = 738401) (by norm_num)
theorem B3501805 : Blo 1843623 3501805 := bbase (se 3 (by rfl) ⟨656588, by rfl⟩ : syracuseStep 3501805 = 1313177) (by norm_num)
theorem B4148981 : Blo 1843623 4148981 := bbase (se 5 (by rfl) ⟨194483, by rfl⟩ : syracuseStep 4148981 = 388967) (by norm_num)
theorem B2215693 : Blo 1843623 2215693 := bbase (se 3 (by rfl) ⟨415442, by rfl⟩ : syracuseStep 2215693 = 830885) (by norm_num)
theorem B3739421 : Blo 1843623 3739421 := bbase (se 3 (by rfl) ⟨701141, by rfl⟩ : syracuseStep 3739421 = 1402283) (by norm_num)
theorem B4149053 : Blo 1843623 4149053 := bbase (se 3 (by rfl) ⟨777947, by rfl⟩ : syracuseStep 4149053 = 1555895) (by norm_num)
theorem B3501949 : Blo 1843623 3501949 := bbase (se 3 (by rfl) ⟨656615, by rfl⟩ : syracuseStep 3501949 = 1313231) (by norm_num)
theorem B4149125 : Blo 1843623 4149125 := bbase (se 4 (by rfl) ⟨388980, by rfl⟩ : syracuseStep 4149125 = 777961) (by norm_num)
theorem B5255077 : Blo 1843623 5255077 := bbase (se 4 (by rfl) ⟨492663, by rfl⟩ : syracuseStep 5255077 = 985327) (by norm_num)
theorem B4149197 : Blo 1843623 4149197 := bbase (se 3 (by rfl) ⟨777974, by rfl⟩ : syracuseStep 4149197 = 1555949) (by norm_num)
theorem B4149269 : Blo 1843623 4149269 := bbase (se 6 (by rfl) ⟨97248, by rfl⟩ : syracuseStep 4149269 = 194497) (by norm_num)
theorem B3502109 : Blo 1843623 3502109 := bbase (se 3 (by rfl) ⟨656645, by rfl⟩ : syracuseStep 3502109 = 1313291) (by norm_num)
theorem B5910565 : Blo 1843623 5910565 := bbase (se 4 (by rfl) ⟨554115, by rfl⟩ : syracuseStep 5910565 = 1108231) (by norm_num)
theorem B4149341 : Blo 1843623 4149341 := bbase (se 3 (by rfl) ⟨778001, by rfl⟩ : syracuseStep 4149341 = 1556003) (by norm_num)
theorem B2625653 : Blo 1843623 2625653 := bbase (se 5 (by rfl) ⟨123077, by rfl⟩ : syracuseStep 2625653 = 246155) (by norm_num)
theorem B4149413 : Blo 1843623 4149413 := bbase (se 4 (by rfl) ⟨389007, by rfl⟩ : syracuseStep 4149413 = 778015) (by norm_num)
theorem B3502253 : Blo 1843623 3502253 := bbase (se 3 (by rfl) ⟨656672, by rfl⟩ : syracuseStep 3502253 = 1313345) (by norm_num)
theorem B2625733 : Blo 1843623 2625733 := bbase (se 4 (by rfl) ⟨246162, by rfl⟩ : syracuseStep 2625733 = 492325) (by norm_num)
theorem B4149485 : Blo 1843623 4149485 := bbase (se 3 (by rfl) ⟨778028, by rfl⟩ : syracuseStep 4149485 = 1556057) (by norm_num)
theorem B1970453 : Blo 1843623 1970453 := bbase (se 6 (by rfl) ⟨46182, by rfl⟩ : syracuseStep 1970453 = 92365) (by norm_num)
theorem B4149557 : Blo 1843623 4149557 := bbase (se 5 (by rfl) ⟨194510, by rfl⟩ : syracuseStep 4149557 = 389021) (by norm_num)
theorem B2625853 : Blo 1843623 2625853 := bbase (se 3 (by rfl) ⟨492347, by rfl⟩ : syracuseStep 2625853 = 984695) (by norm_num)
theorem B4206941 : Blo 1843623 4206941 := bbase (se 3 (by rfl) ⟨788801, by rfl⟩ : syracuseStep 4206941 = 1577603) (by norm_num)
theorem B3740021 : Blo 1843623 3740021 := bbase (se 5 (by rfl) ⟨175313, by rfl⟩ : syracuseStep 3740021 = 350627) (by norm_num)
theorem B9343349 : Blo 1843623 9343349 := bbase (se 5 (by rfl) ⟨437969, by rfl⟩ : syracuseStep 9343349 = 875939) (by norm_num)
theorem B4149629 : Blo 1843623 4149629 := bbase (se 3 (by rfl) ⟨778055, by rfl⟩ : syracuseStep 4149629 = 1556111) (by norm_num)
theorem B2625949 : Blo 1843623 2625949 := bbase (se 3 (by rfl) ⟨492365, by rfl⟩ : syracuseStep 2625949 = 984731) (by norm_num)
theorem B4149701 : Blo 1843623 4149701 := bbase (se 4 (by rfl) ⟨389034, by rfl⟩ : syracuseStep 4149701 = 778069) (by norm_num)
theorem B3502541 : Blo 1843623 3502541 := bbase (se 3 (by rfl) ⟨656726, by rfl⟩ : syracuseStep 3502541 = 1313453) (by norm_num)
theorem B4149773 : Blo 1843623 4149773 := bbase (se 3 (by rfl) ⟨778082, by rfl⟩ : syracuseStep 4149773 = 1556165) (by norm_num)
theorem B4149845 : Blo 1843623 4149845 := bbase (se 8 (by rfl) ⟨24315, by rfl⟩ : syracuseStep 4149845 = 48631) (by norm_num)
theorem B2953829 : Blo 1843623 2953829 := bbase (se 4 (by rfl) ⟨276921, by rfl⟩ : syracuseStep 2953829 = 553843) (by norm_num)
theorem B3502693 : Blo 1843623 3502693 := bbase (se 4 (by rfl) ⟨328377, by rfl⟩ : syracuseStep 3502693 = 656755) (by norm_num)
theorem B2765453 : Blo 1843623 2765453 := bbase (se 3 (by rfl) ⟨518522, by rfl⟩ : syracuseStep 2765453 = 1037045) (by norm_num)
theorem B4149917 : Blo 1843623 4149917 := bbase (se 3 (by rfl) ⟨778109, by rfl⟩ : syracuseStep 4149917 = 1556219) (by norm_num)
theorem B2765477 : Blo 1843623 2765477 := bbase (se 4 (by rfl) ⟨259263, by rfl⟩ : syracuseStep 2765477 = 518527) (by norm_num)
theorem B4207285 : Blo 1843623 4207285 := bbase (se 5 (by rfl) ⟨197216, by rfl⟩ : syracuseStep 4207285 = 394433) (by norm_num)
theorem B2765501 : Blo 1843623 2765501 := bbase (se 3 (by rfl) ⟨518531, by rfl⟩ : syracuseStep 2765501 = 1037063) (by norm_num)
theorem B2765525 : Blo 1843623 2765525 := bbase (se 7 (by rfl) ⟨32408, by rfl⟩ : syracuseStep 2765525 = 64817) (by norm_num)
theorem B4149989 : Blo 1843623 4149989 := bbase (se 4 (by rfl) ⟨389061, by rfl⟩ : syracuseStep 4149989 = 778123) (by norm_num)
theorem B2765549 : Blo 1843623 2765549 := bbase (se 3 (by rfl) ⟨518540, by rfl⟩ : syracuseStep 2765549 = 1037081) (by norm_num)
theorem B6222581 : Blo 1843623 6222581 := bbase (se 5 (by rfl) ⟨291683, by rfl⟩ : syracuseStep 6222581 = 583367) (by norm_num)
theorem B2216693 : Blo 1843623 2216693 := bbase (se 5 (by rfl) ⟨103907, by rfl⟩ : syracuseStep 2216693 = 207815) (by norm_num)
theorem B2765573 : Blo 1843623 2765573 := bbase (se 4 (by rfl) ⟨259272, by rfl⟩ : syracuseStep 2765573 = 518545) (by norm_num)
theorem B9335573 : Blo 1843623 9335573 := bbase (se 6 (by rfl) ⟨218802, by rfl⟩ : syracuseStep 9335573 = 437605) (by norm_num)
theorem B2765597 : Blo 1843623 2765597 := bbase (se 3 (by rfl) ⟨518549, by rfl⟩ : syracuseStep 2765597 = 1037099) (by norm_num)
theorem B4150061 : Blo 1843623 4150061 := bbase (se 3 (by rfl) ⟨778136, by rfl⟩ : syracuseStep 4150061 = 1556273) (by norm_num)
theorem B2765621 : Blo 1843623 2765621 := bbase (se 5 (by rfl) ⟨129638, by rfl⟩ : syracuseStep 2765621 = 259277) (by norm_num)
theorem B15766325 : Blo 1843623 15766325 := bbase (se 5 (by rfl) ⟨739046, by rfl⟩ : syracuseStep 15766325 = 1478093) (by norm_num)
theorem B2765645 : Blo 1843623 2765645 := bbase (se 3 (by rfl) ⟨518558, by rfl⟩ : syracuseStep 2765645 = 1037117) (by norm_num)
theorem B2765669 : Blo 1843623 2765669 := bbase (se 4 (by rfl) ⟨259281, by rfl⟩ : syracuseStep 2765669 = 518563) (by norm_num)
theorem B4150133 : Blo 1843623 4150133 := bbase (se 5 (by rfl) ⟨194537, by rfl⟩ : syracuseStep 4150133 = 389075) (by norm_num)
theorem B2765693 : Blo 1843623 2765693 := bbase (se 3 (by rfl) ⟨518567, by rfl⟩ : syracuseStep 2765693 = 1037135) (by norm_num)
theorem B7476101 : Blo 1843623 7476101 := bbase (se 4 (by rfl) ⟨700884, by rfl⟩ : syracuseStep 7476101 = 1401769) (by norm_num)
theorem B2626445 : Blo 1843623 2626445 := bbase (se 3 (by rfl) ⟨492458, by rfl⟩ : syracuseStep 2626445 = 984917) (by norm_num)
theorem B2765717 : Blo 1843623 2765717 := bbase (se 6 (by rfl) ⟨64821, by rfl⟩ : syracuseStep 2765717 = 129643) (by norm_num)
theorem B3502997 : Blo 1843623 3502997 := bbase (se 6 (by rfl) ⟨82101, by rfl⟩ : syracuseStep 3502997 = 164203) (by norm_num)
theorem B2765741 : Blo 1843623 2765741 := bbase (se 3 (by rfl) ⟨518576, by rfl⟩ : syracuseStep 2765741 = 1037153) (by norm_num)
theorem B4150205 : Blo 1843623 4150205 := bbase (se 3 (by rfl) ⟨778163, by rfl⟩ : syracuseStep 4150205 = 1556327) (by norm_num)
theorem B2765765 : Blo 1843623 2765765 := bbase (se 4 (by rfl) ⟨259290, by rfl⟩ : syracuseStep 2765765 = 518581) (by norm_num)
theorem B2765789 : Blo 1843623 2765789 := bbase (se 3 (by rfl) ⟨518585, by rfl⟩ : syracuseStep 2765789 = 1037171) (by norm_num)
theorem B2765813 : Blo 1843623 2765813 := bbase (se 5 (by rfl) ⟨129647, by rfl⟩ : syracuseStep 2765813 = 259295) (by norm_num)
theorem B3322885 : Blo 1843623 3322885 := bbase (se 4 (by rfl) ⟨311520, by rfl⟩ : syracuseStep 3322885 = 623041) (by norm_num)
theorem B4150277 : Blo 1843623 4150277 := bbase (se 4 (by rfl) ⟨389088, by rfl⟩ : syracuseStep 4150277 = 778177) (by norm_num)
theorem B2765837 : Blo 1843623 2765837 := bbase (se 3 (by rfl) ⟨518594, by rfl⟩ : syracuseStep 2765837 = 1037189) (by norm_num)
theorem B2765861 : Blo 1843623 2765861 := bbase (se 4 (by rfl) ⟨259299, by rfl⟩ : syracuseStep 2765861 = 518599) (by norm_num)
theorem B2765885 : Blo 1843623 2765885 := bbase (se 3 (by rfl) ⟨518603, by rfl⟩ : syracuseStep 2765885 = 1037207) (by norm_num)
theorem B4150349 : Blo 1843623 4150349 := bbase (se 3 (by rfl) ⟨778190, by rfl⟩ : syracuseStep 4150349 = 1556381) (by norm_num)
theorem B2765909 : Blo 1843623 2765909 := bbase (se 8 (by rfl) ⟨16206, by rfl⟩ : syracuseStep 2765909 = 32413) (by norm_num)
theorem B8983637 : Blo 1843623 8983637 := bbase (se 8 (by rfl) ⟨52638, by rfl⟩ : syracuseStep 8983637 = 105277) (by norm_num)
theorem B2954341 : Blo 1843623 2954341 := bbase (se 4 (by rfl) ⟨276969, by rfl⟩ : syracuseStep 2954341 = 553939) (by norm_num)
theorem B2765933 : Blo 1843623 2765933 := bbase (se 3 (by rfl) ⟨518612, by rfl⟩ : syracuseStep 2765933 = 1037225) (by norm_num)
theorem B2765957 : Blo 1843623 2765957 := bbase (se 4 (by rfl) ⟨259308, by rfl⟩ : syracuseStep 2765957 = 518617) (by norm_num)
theorem B4150421 : Blo 1843623 4150421 := bbase (se 6 (by rfl) ⟨97275, by rfl⟩ : syracuseStep 4150421 = 194551) (by norm_num)
theorem B2765981 : Blo 1843623 2765981 := bbase (se 3 (by rfl) ⟨518621, by rfl⟩ : syracuseStep 2765981 = 1037243) (by norm_num)
theorem B6223013 : Blo 1843623 6223013 := bbase (se 4 (by rfl) ⟨583407, by rfl⟩ : syracuseStep 6223013 = 1166815) (by norm_num)
theorem B2102449 : Blo 1843623 2102449 := bbase (se 2 (by rfl) ⟨788418, by rfl⟩ : syracuseStep 2102449 = 1576837) (by norm_num)
theorem B2766005 : Blo 1843623 2766005 := bbase (se 5 (by rfl) ⟨129656, by rfl⟩ : syracuseStep 2766005 = 259313) (by norm_num)
theorem B2766029 : Blo 1843623 2766029 := bbase (se 3 (by rfl) ⟨518630, by rfl⟩ : syracuseStep 2766029 = 1037261) (by norm_num)
theorem B4150493 : Blo 1843623 4150493 := bbase (se 3 (by rfl) ⟨778217, by rfl⟩ : syracuseStep 4150493 = 1556435) (by norm_num)
theorem B2766053 : Blo 1843623 2766053 := bbase (se 4 (by rfl) ⟨259317, by rfl⟩ : syracuseStep 2766053 = 518635) (by norm_num)
theorem B16831733 : Blo 1843623 16831733 := bbase (se 5 (by rfl) ⟨788987, by rfl⟩ : syracuseStep 16831733 = 1577975) (by norm_num)
theorem B2766077 : Blo 1843623 2766077 := bbase (se 3 (by rfl) ⟨518639, by rfl⟩ : syracuseStep 2766077 = 1037279) (by norm_num)
theorem B2766101 : Blo 1843623 2766101 := bbase (se 6 (by rfl) ⟨64830, by rfl⟩ : syracuseStep 2766101 = 129661) (by norm_num)
theorem B4150565 : Blo 1843623 4150565 := bbase (se 4 (by rfl) ⟨389115, by rfl⟩ : syracuseStep 4150565 = 778231) (by norm_num)
theorem B2766125 : Blo 1843623 2766125 := bbase (se 3 (by rfl) ⟨518648, by rfl⟩ : syracuseStep 2766125 = 1037297) (by norm_num)
theorem B4666693 : Blo 1843623 4666693 := bbase (se 4 (by rfl) ⟨437502, by rfl⟩ : syracuseStep 4666693 = 875005) (by norm_num)
theorem B2766149 : Blo 1843623 2766149 := bbase (se 4 (by rfl) ⟨259326, by rfl⟩ : syracuseStep 2766149 = 518653) (by norm_num)
theorem B2766173 : Blo 1843623 2766173 := bbase (se 3 (by rfl) ⟨518657, by rfl⟩ : syracuseStep 2766173 = 1037315) (by norm_num)
theorem B4150637 : Blo 1843623 4150637 := bbase (se 3 (by rfl) ⟨778244, by rfl⟩ : syracuseStep 4150637 = 1556489) (by norm_num)
theorem B2766197 : Blo 1843623 2766197 := bbase (se 5 (by rfl) ⟨129665, by rfl⟩ : syracuseStep 2766197 = 259331) (by norm_num)
theorem B2766221 : Blo 1843623 2766221 := bbase (se 3 (by rfl) ⟨518666, by rfl⟩ : syracuseStep 2766221 = 1037333) (by norm_num)
theorem B3995021 : Blo 1843623 3995021 := bbase (se 3 (by rfl) ⟨749066, by rfl⟩ : syracuseStep 3995021 = 1498133) (by norm_num)
theorem B2766245 : Blo 1843623 2766245 := bbase (se 4 (by rfl) ⟨259335, by rfl⟩ : syracuseStep 2766245 = 518671) (by norm_num)
theorem B7878053 : Blo 1843623 7878053 := bbase (se 4 (by rfl) ⟨738567, by rfl⟩ : syracuseStep 7878053 = 1477135) (by norm_num)
theorem B4666805 : Blo 1843623 4666805 := bbase (se 5 (by rfl) ⟨218756, by rfl⟩ : syracuseStep 4666805 = 437513) (by norm_num)
theorem B4150709 : Blo 1843623 4150709 := bbase (se 5 (by rfl) ⟨194564, by rfl⟩ : syracuseStep 4150709 = 389129) (by norm_num)
theorem B2626997 : Blo 1843623 2626997 := bbase (se 5 (by rfl) ⟨123140, by rfl⟩ : syracuseStep 2626997 = 246281) (by norm_num)
theorem B2766269 : Blo 1843623 2766269 := bbase (se 3 (by rfl) ⟨518675, by rfl⟩ : syracuseStep 2766269 = 1037351) (by norm_num)
theorem B2766293 : Blo 1843623 2766293 := bbase (se 7 (by rfl) ⟨32417, by rfl⟩ : syracuseStep 2766293 = 64835) (by norm_num)
theorem B2766317 : Blo 1843623 2766317 := bbase (se 3 (by rfl) ⟨518684, by rfl⟩ : syracuseStep 2766317 = 1037369) (by norm_num)
theorem B4150781 : Blo 1843623 4150781 := bbase (se 3 (by rfl) ⟨778271, by rfl⟩ : syracuseStep 4150781 = 1556543) (by norm_num)
theorem B2766341 : Blo 1843623 2766341 := bbase (se 4 (by rfl) ⟨259344, by rfl⟩ : syracuseStep 2766341 = 518689) (by norm_num)
theorem B6313477 : Blo 1843623 6313477 := bbase (se 4 (by rfl) ⟨591888, by rfl⟩ : syracuseStep 6313477 = 1183777) (by norm_num)
theorem B2766365 : Blo 1843623 2766365 := bbase (se 3 (by rfl) ⟨518693, by rfl⟩ : syracuseStep 2766365 = 1037387) (by norm_num)
theorem B2766389 : Blo 1843623 2766389 := bbase (se 5 (by rfl) ⟨129674, by rfl⟩ : syracuseStep 2766389 = 259349) (by norm_num)
theorem B4150853 : Blo 1843623 4150853 := bbase (se 4 (by rfl) ⟨389142, by rfl⟩ : syracuseStep 4150853 = 778285) (by norm_num)
theorem B2766413 : Blo 1843623 2766413 := bbase (se 3 (by rfl) ⟨518702, by rfl⟩ : syracuseStep 2766413 = 1037405) (by norm_num)
theorem B6223445 : Blo 1843623 6223445 := bbase (se 8 (by rfl) ⟨36465, by rfl⟩ : syracuseStep 6223445 = 72931) (by norm_num)
theorem B2766437 : Blo 1843623 2766437 := bbase (se 4 (by rfl) ⟨259353, by rfl⟩ : syracuseStep 2766437 = 518707) (by norm_num)
theorem B4208237 : Blo 1843623 4208237 := bbase (se 3 (by rfl) ⟨789044, by rfl⟩ : syracuseStep 4208237 = 1578089) (by norm_num)
theorem B4666997 : Blo 1843623 4666997 := bbase (se 5 (by rfl) ⟨218765, by rfl⟩ : syracuseStep 4666997 = 437531) (by norm_num)
theorem B2766461 : Blo 1843623 2766461 := bbase (se 3 (by rfl) ⟨518711, by rfl⟩ : syracuseStep 2766461 = 1037423) (by norm_num)
theorem B2954885 : Blo 1843623 2954885 := bbase (se 4 (by rfl) ⟨277020, by rfl⟩ : syracuseStep 2954885 = 554041) (by norm_num)
theorem B3503749 : Blo 1843623 3503749 := bbase (se 4 (by rfl) ⟨328476, by rfl⟩ : syracuseStep 3503749 = 656953) (by norm_num)
theorem B3937933 : Blo 1843623 3937933 := bbase (se 3 (by rfl) ⟨738362, by rfl⟩ : syracuseStep 3937933 = 1476725) (by norm_num)
theorem B4150925 : Blo 1843623 4150925 := bbase (se 3 (by rfl) ⟨778298, by rfl⟩ : syracuseStep 4150925 = 1556597) (by norm_num)
theorem B2766485 : Blo 1843623 2766485 := bbase (se 6 (by rfl) ⟨64839, by rfl⟩ : syracuseStep 2766485 = 129679) (by norm_num)
theorem B7878293 : Blo 1843623 7878293 := bbase (se 6 (by rfl) ⟨184647, by rfl⟩ : syracuseStep 7878293 = 369295) (by norm_num)
theorem B2766509 : Blo 1843623 2766509 := bbase (se 3 (by rfl) ⟨518720, by rfl⟩ : syracuseStep 2766509 = 1037441) (by norm_num)
theorem B2766533 : Blo 1843623 2766533 := bbase (se 4 (by rfl) ⟨259362, by rfl⟩ : syracuseStep 2766533 = 518725) (by norm_num)
theorem B4732613 : Blo 1843623 4732613 := bbase (se 4 (by rfl) ⟨443682, by rfl⟩ : syracuseStep 4732613 = 887365) (by norm_num)
theorem B4150997 : Blo 1843623 4150997 := bbase (se 7 (by rfl) ⟨48644, by rfl⟩ : syracuseStep 4150997 = 97289) (by norm_num)
theorem B2766557 : Blo 1843623 2766557 := bbase (se 3 (by rfl) ⟨518729, by rfl⟩ : syracuseStep 2766557 = 1037459) (by norm_num)
theorem B2766581 : Blo 1843623 2766581 := bbase (se 5 (by rfl) ⟨129683, by rfl⟩ : syracuseStep 2766581 = 259367) (by norm_num)
theorem B1996537 : Blo 1843623 1996537 := bbase (se 2 (by rfl) ⟨748701, by rfl⟩ : syracuseStep 1996537 = 1497403) (by norm_num)
theorem B3938053 : Blo 1843623 3938053 := bbase (se 4 (by rfl) ⟨369192, by rfl⟩ : syracuseStep 3938053 = 738385) (by norm_num)
theorem B2766605 : Blo 1843623 2766605 := bbase (se 3 (by rfl) ⟨518738, by rfl⟩ : syracuseStep 2766605 = 1037477) (by norm_num)
theorem B4151069 : Blo 1843623 4151069 := bbase (se 3 (by rfl) ⟨778325, by rfl⟩ : syracuseStep 4151069 = 1556651) (by norm_num)
theorem B2766629 : Blo 1843623 2766629 := bbase (se 4 (by rfl) ⟨259371, by rfl⟩ : syracuseStep 2766629 = 518743) (by norm_num)
theorem B8984357 : Blo 1843623 8984357 := bbase (se 4 (by rfl) ⟨842283, by rfl⟩ : syracuseStep 8984357 = 1684567) (by norm_num)
theorem B7001909 : Blo 1843623 7001909 := bbase (se 5 (by rfl) ⟨328214, by rfl⟩ : syracuseStep 7001909 = 656429) (by norm_num)
theorem B2766653 : Blo 1843623 2766653 := bbase (se 3 (by rfl) ⟨518747, by rfl⟩ : syracuseStep 2766653 = 1037495) (by norm_num)
theorem B2766677 : Blo 1843623 2766677 := bbase (se 9 (by rfl) ⟨8105, by rfl⟩ : syracuseStep 2766677 = 16211) (by norm_num)
theorem B4151141 : Blo 1843623 4151141 := bbase (se 4 (by rfl) ⟨389169, by rfl⟩ : syracuseStep 4151141 = 778339) (by norm_num)
theorem B2766701 : Blo 1843623 2766701 := bbase (se 3 (by rfl) ⟨518756, by rfl⟩ : syracuseStep 2766701 = 1037513) (by norm_num)
theorem B16824181 : Blo 1843623 16824181 := bbase (se 5 (by rfl) ⟨788633, by rfl⟩ : syracuseStep 16824181 = 1577267) (by norm_num)
theorem B2766725 : Blo 1843623 2766725 := bbase (se 4 (by rfl) ⟨259380, by rfl⟩ : syracuseStep 2766725 = 518761) (by norm_num)
theorem B2766749 : Blo 1843623 2766749 := bbase (se 3 (by rfl) ⟨518765, by rfl⟩ : syracuseStep 2766749 = 1037531) (by norm_num)
theorem B3323813 : Blo 1843623 3323813 := bbase (se 4 (by rfl) ⟨311607, by rfl⟩ : syracuseStep 3323813 = 623215) (by norm_num)
theorem B4151213 : Blo 1843623 4151213 := bbase (se 3 (by rfl) ⟨778352, by rfl⟩ : syracuseStep 4151213 = 1556705) (by norm_num)
theorem B2766773 : Blo 1843623 2766773 := bbase (se 5 (by rfl) ⟨129692, by rfl⟩ : syracuseStep 2766773 = 259385) (by norm_num)
theorem B4667341 : Blo 1843623 4667341 := bbase (se 3 (by rfl) ⟨875126, by rfl⟩ : syracuseStep 4667341 = 1750253) (by norm_num)
theorem B2766797 : Blo 1843623 2766797 := bbase (se 3 (by rfl) ⟨518774, by rfl⟩ : syracuseStep 2766797 = 1037549) (by norm_num)
theorem B2766821 : Blo 1843623 2766821 := bbase (se 4 (by rfl) ⟨259389, by rfl⟩ : syracuseStep 2766821 = 518779) (by norm_num)
theorem B4151285 : Blo 1843623 4151285 := bbase (se 5 (by rfl) ⟨194591, by rfl⟩ : syracuseStep 4151285 = 389183) (by norm_num)
theorem B2766845 : Blo 1843623 2766845 := bbase (se 3 (by rfl) ⟨518783, by rfl⟩ : syracuseStep 2766845 = 1037567) (by norm_num)
theorem B4429829 : Blo 1843623 4429829 := bbase (se 4 (by rfl) ⟨415296, by rfl⟩ : syracuseStep 4429829 = 830593) (by norm_num)
theorem B3938309 : Blo 1843623 3938309 := bbase (se 4 (by rfl) ⟨369216, by rfl⟩ : syracuseStep 3938309 = 738433) (by norm_num)
theorem B6223877 : Blo 1843623 6223877 := bbase (se 4 (by rfl) ⟨583488, by rfl⟩ : syracuseStep 6223877 = 1166977) (by norm_num)
theorem B2766869 : Blo 1843623 2766869 := bbase (se 6 (by rfl) ⟨64848, by rfl⟩ : syracuseStep 2766869 = 129697) (by norm_num)
theorem B6649877 : Blo 1843623 6649877 := bbase (se 6 (by rfl) ⟨155856, by rfl⟩ : syracuseStep 6649877 = 311713) (by norm_num)
theorem B9336869 : Blo 1843623 9336869 := bbase (se 4 (by rfl) ⟨875331, by rfl⟩ : syracuseStep 9336869 = 1750663) (by norm_num)
theorem B2766893 : Blo 1843623 2766893 := bbase (se 3 (by rfl) ⟨518792, by rfl⟩ : syracuseStep 2766893 = 1037585) (by norm_num)
theorem B4667453 : Blo 1843623 4667453 := bbase (se 3 (by rfl) ⟨875147, by rfl⟩ : syracuseStep 4667453 = 1750295) (by norm_num)
theorem B4151357 : Blo 1843623 4151357 := bbase (se 3 (by rfl) ⟨778379, by rfl⟩ : syracuseStep 4151357 = 1556759) (by norm_num)
theorem B2766917 : Blo 1843623 2766917 := bbase (se 4 (by rfl) ⟨259398, by rfl⟩ : syracuseStep 2766917 = 518797) (by norm_num)
theorem B7002197 : Blo 1843623 7002197 := bbase (se 8 (by rfl) ⟨41028, by rfl⟩ : syracuseStep 7002197 = 82057) (by norm_num)
theorem B2766941 : Blo 1843623 2766941 := bbase (se 3 (by rfl) ⟨518801, by rfl⟩ : syracuseStep 2766941 = 1037603) (by norm_num)
theorem B2766965 : Blo 1843623 2766965 := bbase (se 5 (by rfl) ⟨129701, by rfl⟩ : syracuseStep 2766965 = 259403) (by norm_num)
theorem B9599093 : Blo 1843623 9599093 := bbase (se 5 (by rfl) ⟨449957, by rfl⟩ : syracuseStep 9599093 = 899915) (by norm_num)
theorem B4151429 : Blo 1843623 4151429 := bbase (se 4 (by rfl) ⟨389196, by rfl⟩ : syracuseStep 4151429 = 778393) (by norm_num)
theorem B2766989 : Blo 1843623 2766989 := bbase (se 3 (by rfl) ⟨518810, by rfl⟩ : syracuseStep 2766989 = 1037621) (by norm_num)
theorem B16824469 : Blo 1843623 16824469 := bbase (se 6 (by rfl) ⟨394323, by rfl⟩ : syracuseStep 16824469 = 788647) (by norm_num)
theorem B2767013 : Blo 1843623 2767013 := bbase (se 4 (by rfl) ⟨259407, by rfl⟩ : syracuseStep 2767013 = 518815) (by norm_num)
theorem B2627749 : Blo 1843623 2627749 := bbase (se 4 (by rfl) ⟨246351, by rfl⟩ : syracuseStep 2627749 = 492703) (by norm_num)
theorem B2955437 : Blo 1843623 2955437 := bbase (se 3 (by rfl) ⟨554144, by rfl⟩ : syracuseStep 2955437 = 1108289) (by norm_num)
theorem B2767037 : Blo 1843623 2767037 := bbase (se 3 (by rfl) ⟨518819, by rfl⟩ : syracuseStep 2767037 = 1037639) (by norm_num)
theorem B4733117 : Blo 1843623 4733117 := bbase (se 3 (by rfl) ⟨887459, by rfl⟩ : syracuseStep 4733117 = 1774919) (by norm_num)
theorem B2955469 : Blo 1843623 2955469 := bbase (se 3 (by rfl) ⟨554150, by rfl⟩ : syracuseStep 2955469 = 1108301) (by norm_num)
theorem B4151501 : Blo 1843623 4151501 := bbase (se 3 (by rfl) ⟨778406, by rfl⟩ : syracuseStep 4151501 = 1556813) (by norm_num)
theorem B2767061 : Blo 1843623 2767061 := bbase (se 7 (by rfl) ⟨32426, by rfl⟩ : syracuseStep 2767061 = 64853) (by norm_num)
theorem B3111149 : Blo 1843623 3111149 := bbase (se 3 (by rfl) ⟨583340, by rfl⟩ : syracuseStep 3111149 = 1166681) (by norm_num)
theorem B2767085 : Blo 1843623 2767085 := bbase (se 3 (by rfl) ⟨518828, by rfl⟩ : syracuseStep 2767085 = 1037657) (by norm_num)
theorem B4667645 : Blo 1843623 4667645 := bbase (se 3 (by rfl) ⟨875183, by rfl⟩ : syracuseStep 4667645 = 1750367) (by norm_num)
theorem B2767109 : Blo 1843623 2767109 := bbase (se 4 (by rfl) ⟨259416, by rfl⟩ : syracuseStep 2767109 = 518833) (by norm_num)
theorem B4151573 : Blo 1843623 4151573 := bbase (se 6 (by rfl) ⟨97302, by rfl⟩ : syracuseStep 4151573 = 194605) (by norm_num)
theorem B2767133 : Blo 1843623 2767133 := bbase (se 3 (by rfl) ⟨518837, by rfl⟩ : syracuseStep 2767133 = 1037675) (by norm_num)
theorem B2767157 : Blo 1843623 2767157 := bbase (se 5 (by rfl) ⟨129710, by rfl⟩ : syracuseStep 2767157 = 259421) (by norm_num)
theorem B2103617 : Blo 1843623 2103617 := bbase (se 2 (by rfl) ⟨788856, by rfl⟩ : syracuseStep 2103617 = 1577713) (by norm_num)
theorem B2767181 : Blo 1843623 2767181 := bbase (se 3 (by rfl) ⟨518846, by rfl⟩ : syracuseStep 2767181 = 1037693) (by norm_num)
theorem B4151645 : Blo 1843623 4151645 := bbase (se 3 (by rfl) ⟨778433, by rfl⟩ : syracuseStep 4151645 = 1556867) (by norm_num)
theorem B2767205 : Blo 1843623 2767205 := bbase (se 4 (by rfl) ⟨259425, by rfl⟩ : syracuseStep 2767205 = 518851) (by norm_num)
theorem B3111277 : Blo 1843623 3111277 := bbase (se 3 (by rfl) ⟨583364, by rfl⟩ : syracuseStep 3111277 = 1166729) (by norm_num)
theorem B2767229 : Blo 1843623 2767229 := bbase (se 3 (by rfl) ⟨518855, by rfl⟩ : syracuseStep 2767229 = 1037711) (by norm_num)
theorem B2767253 : Blo 1843623 2767253 := bbase (se 6 (by rfl) ⟨64857, by rfl⟩ : syracuseStep 2767253 = 129715) (by norm_num)
theorem B4151717 : Blo 1843623 4151717 := bbase (se 4 (by rfl) ⟨389223, by rfl⟩ : syracuseStep 4151717 = 778447) (by norm_num)
theorem B2767277 : Blo 1843623 2767277 := bbase (se 3 (by rfl) ⟨518864, by rfl⟩ : syracuseStep 2767277 = 1037729) (by norm_num)
theorem B6224309 : Blo 1843623 6224309 := bbase (se 5 (by rfl) ⟨291764, by rfl⟩ : syracuseStep 6224309 = 583529) (by norm_num)
theorem B3111365 : Blo 1843623 3111365 := bbase (se 4 (by rfl) ⟨291690, by rfl⟩ : syracuseStep 3111365 = 583381) (by norm_num)
theorem B2767301 : Blo 1843623 2767301 := bbase (se 4 (by rfl) ⟨259434, by rfl⟩ : syracuseStep 2767301 = 518869) (by norm_num)
theorem B2767325 : Blo 1843623 2767325 := bbase (se 3 (by rfl) ⟨518873, by rfl⟩ : syracuseStep 2767325 = 1037747) (by norm_num)
theorem B4151789 : Blo 1843623 4151789 := bbase (se 3 (by rfl) ⟨778460, by rfl⟩ : syracuseStep 4151789 = 1556921) (by norm_num)
theorem B2767349 : Blo 1843623 2767349 := bbase (se 5 (by rfl) ⟨129719, by rfl⟩ : syracuseStep 2767349 = 259439) (by norm_num)
theorem B2767373 : Blo 1843623 2767373 := bbase (se 3 (by rfl) ⟨518882, by rfl⟩ : syracuseStep 2767373 = 1037765) (by norm_num)
theorem B2767397 : Blo 1843623 2767397 := bbase (se 4 (by rfl) ⟨259443, by rfl⟩ : syracuseStep 2767397 = 518887) (by norm_num)
theorem B4151861 : Blo 1843623 4151861 := bbase (se 5 (by rfl) ⟨194618, by rfl⟩ : syracuseStep 4151861 = 389237) (by norm_num)
theorem B2767421 : Blo 1843623 2767421 := bbase (se 3 (by rfl) ⟨518891, by rfl⟩ : syracuseStep 2767421 = 1037783) (by norm_num)
theorem B3111493 : Blo 1843623 3111493 := bbase (se 4 (by rfl) ⟨291702, by rfl⟩ : syracuseStep 3111493 = 583405) (by norm_num)
theorem B4667989 : Blo 1843623 4667989 := bbase (se 8 (by rfl) ⟨27351, by rfl⟩ : syracuseStep 4667989 = 54703) (by norm_num)
theorem B2767445 : Blo 1843623 2767445 := bbase (se 8 (by rfl) ⟨16215, by rfl⟩ : syracuseStep 2767445 = 32431) (by norm_num)
theorem B2767469 : Blo 1843623 2767469 := bbase (se 3 (by rfl) ⟨518900, by rfl⟩ : syracuseStep 2767469 = 1037801) (by norm_num)
theorem B4151933 : Blo 1843623 4151933 := bbase (se 3 (by rfl) ⟨778487, by rfl⟩ : syracuseStep 4151933 = 1556975) (by norm_num)
theorem B2767493 : Blo 1843623 2767493 := bbase (se 4 (by rfl) ⟨259452, by rfl⟩ : syracuseStep 2767493 = 518905) (by norm_num)
theorem B3324557 : Blo 1843623 3324557 := bbase (se 3 (by rfl) ⟨623354, by rfl⟩ : syracuseStep 3324557 = 1246709) (by norm_num)
theorem B3111581 : Blo 1843623 3111581 := bbase (se 3 (by rfl) ⟨583421, by rfl⟩ : syracuseStep 3111581 = 1166843) (by norm_num)
theorem B2767517 : Blo 1843623 2767517 := bbase (se 3 (by rfl) ⟨518909, by rfl⟩ : syracuseStep 2767517 = 1037819) (by norm_num)
theorem B2767541 : Blo 1843623 2767541 := bbase (se 5 (by rfl) ⟨129728, by rfl⟩ : syracuseStep 2767541 = 259457) (by norm_num)
theorem B2333377 : Blo 1843623 2333377 := bbase (se 2 (by rfl) ⟨875016, by rfl⟩ : syracuseStep 2333377 = 1750033) (by norm_num)
theorem B4668101 : Blo 1843623 4668101 := bbase (se 4 (by rfl) ⟨437634, by rfl⟩ : syracuseStep 4668101 = 875269) (by norm_num)
theorem B4152005 : Blo 1843623 4152005 := bbase (se 4 (by rfl) ⟨389250, by rfl⟩ : syracuseStep 4152005 = 778501) (by norm_num)
theorem B2767565 : Blo 1843623 2767565 := bbase (se 3 (by rfl) ⟨518918, by rfl⟩ : syracuseStep 2767565 = 1037837) (by norm_num)
theorem B2767589 : Blo 1843623 2767589 := bbase (se 4 (by rfl) ⟨259461, by rfl⟩ : syracuseStep 2767589 = 518923) (by norm_num)
theorem B2767613 : Blo 1843623 2767613 := bbase (se 3 (by rfl) ⟨518927, by rfl⟩ : syracuseStep 2767613 = 1037855) (by norm_num)
theorem B4152077 : Blo 1843623 4152077 := bbase (se 3 (by rfl) ⟨778514, by rfl⟩ : syracuseStep 4152077 = 1557029) (by norm_num)
theorem B2767637 : Blo 1843623 2767637 := bbase (se 6 (by rfl) ⟨64866, by rfl⟩ : syracuseStep 2767637 = 129733) (by norm_num)
theorem B3111709 : Blo 1843623 3111709 := bbase (se 3 (by rfl) ⟨583445, by rfl⟩ : syracuseStep 3111709 = 1166891) (by norm_num)
theorem B2767661 : Blo 1843623 2767661 := bbase (se 3 (by rfl) ⟨518936, by rfl⟩ : syracuseStep 2767661 = 1037873) (by norm_num)
theorem B2767685 : Blo 1843623 2767685 := bbase (se 4 (by rfl) ⟨259470, by rfl⟩ : syracuseStep 2767685 = 518941) (by norm_num)
theorem B4152149 : Blo 1843623 4152149 := bbase (se 9 (by rfl) ⟨12164, by rfl⟩ : syracuseStep 4152149 = 24329) (by norm_num)
theorem B2767709 : Blo 1843623 2767709 := bbase (se 3 (by rfl) ⟨518945, by rfl⟩ : syracuseStep 2767709 = 1037891) (by norm_num)
theorem B6224741 : Blo 1843623 6224741 := bbase (se 4 (by rfl) ⟨583569, by rfl⟩ : syracuseStep 6224741 = 1167139) (by norm_num)
theorem B2333549 : Blo 1843623 2333549 := bbase (se 3 (by rfl) ⟨437540, by rfl⟩ : syracuseStep 2333549 = 875081) (by norm_num)
theorem B3111797 : Blo 1843623 3111797 := bbase (se 5 (by rfl) ⟨145865, by rfl⟩ : syracuseStep 3111797 = 291731) (by norm_num)
theorem B4733813 : Blo 1843623 4733813 := bbase (se 5 (by rfl) ⟨221897, by rfl⟩ : syracuseStep 4733813 = 443795) (by norm_num)
theorem B2767733 : Blo 1843623 2767733 := bbase (se 5 (by rfl) ⟨129737, by rfl⟩ : syracuseStep 2767733 = 259475) (by norm_num)
theorem B10509173 : Blo 1843623 10509173 := bbase (se 5 (by rfl) ⟨492617, by rfl⟩ : syracuseStep 10509173 = 985235) (by norm_num)
theorem B3939197 : Blo 1843623 3939197 := bbase (se 3 (by rfl) ⟨738599, by rfl⟩ : syracuseStep 3939197 = 1477199) (by norm_num)
theorem B4668293 : Blo 1843623 4668293 := bbase (se 4 (by rfl) ⟨437652, by rfl⟩ : syracuseStep 4668293 = 875305) (by norm_num)
theorem B2767757 : Blo 1843623 2767757 := bbase (se 3 (by rfl) ⟨518954, by rfl⟩ : syracuseStep 2767757 = 1037909) (by norm_num)
theorem B4152221 : Blo 1843623 4152221 := bbase (se 3 (by rfl) ⟨778541, by rfl⟩ : syracuseStep 4152221 = 1557083) (by norm_num)
theorem B2333605 : Blo 1843623 2333605 := bbase (se 4 (by rfl) ⟨218775, by rfl⟩ : syracuseStep 2333605 = 437551) (by norm_num)
theorem B2767781 : Blo 1843623 2767781 := bbase (se 4 (by rfl) ⟨259479, by rfl⟩ : syracuseStep 2767781 = 518959) (by norm_num)
theorem B2767805 : Blo 1843623 2767805 := bbase (se 3 (by rfl) ⟨518963, by rfl⟩ : syracuseStep 2767805 = 1037927) (by norm_num)
theorem B5987285 : Blo 1843623 5987285 := bbase (se 7 (by rfl) ⟨70163, by rfl⟩ : syracuseStep 5987285 = 140327) (by norm_num)
theorem B2767829 : Blo 1843623 2767829 := bbase (se 7 (by rfl) ⟨32435, by rfl⟩ : syracuseStep 2767829 = 64871) (by norm_num)
theorem B4152293 : Blo 1843623 4152293 := bbase (se 4 (by rfl) ⟨389277, by rfl⟩ : syracuseStep 4152293 = 778555) (by norm_num)
theorem B2767853 : Blo 1843623 2767853 := bbase (se 3 (by rfl) ⟨518972, by rfl⟩ : syracuseStep 2767853 = 1037945) (by norm_num)
theorem B10501109 : Blo 1843623 10501109 := bbase (se 5 (by rfl) ⟨492239, by rfl⟩ : syracuseStep 10501109 = 984479) (by norm_num)
theorem B3111925 : Blo 1843623 3111925 := bbase (se 5 (by rfl) ⟨145871, by rfl⟩ : syracuseStep 3111925 = 291743) (by norm_num)
theorem B2333701 : Blo 1843623 2333701 := bbase (se 4 (by rfl) ⟨218784, by rfl⟩ : syracuseStep 2333701 = 437569) (by norm_num)
theorem B2767877 : Blo 1843623 2767877 := bbase (se 4 (by rfl) ⟨259488, by rfl⟩ : syracuseStep 2767877 = 518977) (by norm_num)
theorem B2767901 : Blo 1843623 2767901 := bbase (se 3 (by rfl) ⟨518981, by rfl⟩ : syracuseStep 2767901 = 1037963) (by norm_num)
theorem B4152365 : Blo 1843623 4152365 := bbase (se 3 (by rfl) ⟨778568, by rfl⟩ : syracuseStep 4152365 = 1557137) (by norm_num)
theorem B2767925 : Blo 1843623 2767925 := bbase (se 5 (by rfl) ⟨129746, by rfl⟩ : syracuseStep 2767925 = 259493) (by norm_num)
theorem B3112013 : Blo 1843623 3112013 := bbase (se 3 (by rfl) ⟨583502, by rfl⟩ : syracuseStep 3112013 = 1167005) (by norm_num)
theorem B2767949 : Blo 1843623 2767949 := bbase (se 3 (by rfl) ⟨518990, by rfl⟩ : syracuseStep 2767949 = 1037981) (by norm_num)
theorem B2767973 : Blo 1843623 2767973 := bbase (se 4 (by rfl) ⟨259497, by rfl⟩ : syracuseStep 2767973 = 518995) (by norm_num)
theorem B3939437 : Blo 1843623 3939437 := bbase (se 3 (by rfl) ⟨738644, by rfl⟩ : syracuseStep 3939437 = 1477289) (by norm_num)
theorem B4152437 : Blo 1843623 4152437 := bbase (se 5 (by rfl) ⟨194645, by rfl⟩ : syracuseStep 4152437 = 389291) (by norm_num)
theorem B2767997 : Blo 1843623 2767997 := bbase (se 3 (by rfl) ⟨518999, by rfl⟩ : syracuseStep 2767997 = 1037999) (by norm_num)
theorem B2768021 : Blo 1843623 2768021 := bbase (se 6 (by rfl) ⟨64875, by rfl⟩ : syracuseStep 2768021 = 129751) (by norm_num)
theorem B2768045 : Blo 1843623 2768045 := bbase (se 3 (by rfl) ⟨519008, by rfl⟩ : syracuseStep 2768045 = 1038017) (by norm_num)
theorem B2333873 : Blo 1843623 2333873 := bbase (se 2 (by rfl) ⟨875202, by rfl⟩ : syracuseStep 2333873 = 1750405) (by norm_num)
theorem B4152509 : Blo 1843623 4152509 := bbase (se 3 (by rfl) ⟨778595, by rfl⟩ : syracuseStep 4152509 = 1557191) (by norm_num)
theorem B2768069 : Blo 1843623 2768069 := bbase (se 4 (by rfl) ⟨259506, by rfl⟩ : syracuseStep 2768069 = 519013) (by norm_num)
theorem B3112141 : Blo 1843623 3112141 := bbase (se 3 (by rfl) ⟨583526, by rfl⟩ : syracuseStep 3112141 = 1167053) (by norm_num)
theorem B4668637 : Blo 1843623 4668637 := bbase (se 3 (by rfl) ⟨875369, by rfl⟩ : syracuseStep 4668637 = 1750739) (by norm_num)
theorem B2768093 : Blo 1843623 2768093 := bbase (se 3 (by rfl) ⟨519017, by rfl⟩ : syracuseStep 2768093 = 1038035) (by norm_num)
theorem B2333929 : Blo 1843623 2333929 := bbase (se 2 (by rfl) ⟨875223, by rfl⟩ : syracuseStep 2333929 = 1750447) (by norm_num)
theorem B7003381 : Blo 1843623 7003381 := bbase (se 5 (by rfl) ⟨328283, by rfl⟩ : syracuseStep 7003381 = 656567) (by norm_num)
theorem B2768117 : Blo 1843623 2768117 := bbase (se 5 (by rfl) ⟨129755, by rfl⟩ : syracuseStep 2768117 = 259511) (by norm_num)
theorem B4152581 : Blo 1843623 4152581 := bbase (se 4 (by rfl) ⟨389304, by rfl⟩ : syracuseStep 4152581 = 778609) (by norm_num)
theorem B2768141 : Blo 1843623 2768141 := bbase (se 3 (by rfl) ⟨519026, by rfl⟩ : syracuseStep 2768141 = 1038053) (by norm_num)
theorem B6225173 : Blo 1843623 6225173 := bbase (se 6 (by rfl) ⟨145902, by rfl⟩ : syracuseStep 6225173 = 291805) (by norm_num)
theorem B4799765 : Blo 1843623 4799765 := bbase (se 6 (by rfl) ⟨112494, by rfl⟩ : syracuseStep 4799765 = 224989) (by norm_num)
theorem B3112229 : Blo 1843623 3112229 := bbase (se 4 (by rfl) ⟨291771, by rfl⟩ : syracuseStep 3112229 = 583543) (by norm_num)
theorem B2768165 : Blo 1843623 2768165 := bbase (se 4 (by rfl) ⟨259515, by rfl⟩ : syracuseStep 2768165 = 519031) (by norm_num)
theorem B9338165 : Blo 1843623 9338165 := bbase (se 5 (by rfl) ⟨437726, by rfl⟩ : syracuseStep 9338165 = 875453) (by norm_num)
theorem B2768189 : Blo 1843623 2768189 := bbase (se 3 (by rfl) ⟨519035, by rfl⟩ : syracuseStep 2768189 = 1038071) (by norm_num)
theorem B2334025 : Blo 1843623 2334025 := bbase (se 2 (by rfl) ⟨875259, by rfl⟩ : syracuseStep 2334025 = 1750519) (by norm_num)
theorem B4668749 : Blo 1843623 4668749 := bbase (se 3 (by rfl) ⟨875390, by rfl⟩ : syracuseStep 4668749 = 1750781) (by norm_num)
theorem B4152653 : Blo 1843623 4152653 := bbase (se 3 (by rfl) ⟨778622, by rfl⟩ : syracuseStep 4152653 = 1557245) (by norm_num)
theorem B11984213 : Blo 1843623 11984213 := bbase (se 11 (by rfl) ⟨8777, by rfl⟩ : syracuseStep 11984213 = 17555) (by norm_num)
theorem B2768213 : Blo 1843623 2768213 := bbase (se 11 (by rfl) ⟨2027, by rfl⟩ : syracuseStep 2768213 = 4055) (by norm_num)
theorem B2768237 : Blo 1843623 2768237 := bbase (se 3 (by rfl) ⟨519044, by rfl⟩ : syracuseStep 2768237 = 1038089) (by norm_num)
theorem B2768261 : Blo 1843623 2768261 := bbase (se 4 (by rfl) ⟨259524, by rfl⟩ : syracuseStep 2768261 = 519049) (by norm_num)
theorem B2768285 : Blo 1843623 2768285 := bbase (se 3 (by rfl) ⟨519053, by rfl⟩ : syracuseStep 2768285 = 1038107) (by norm_num)
theorem B3112357 : Blo 1843623 3112357 := bbase (se 4 (by rfl) ⟨291783, by rfl⟩ : syracuseStep 3112357 = 583567) (by norm_num)
theorem B6651317 : Blo 1843623 6651317 := bbase (se 5 (by rfl) ⟨311780, by rfl⟩ : syracuseStep 6651317 = 623561) (by norm_num)
theorem B2768309 : Blo 1843623 2768309 := bbase (se 5 (by rfl) ⟨129764, by rfl⟩ : syracuseStep 2768309 = 259529) (by norm_num)
theorem B2768333 : Blo 1843623 2768333 := bbase (se 3 (by rfl) ⟨519062, by rfl⟩ : syracuseStep 2768333 = 1038125) (by norm_num)
theorem B2768357 : Blo 1843623 2768357 := bbase (se 4 (by rfl) ⟨259533, by rfl⟩ : syracuseStep 2768357 = 519067) (by norm_num)
theorem B2334197 : Blo 1843623 2334197 := bbase (se 5 (by rfl) ⟨109415, by rfl⟩ : syracuseStep 2334197 = 218831) (by norm_num)
theorem B3112445 : Blo 1843623 3112445 := bbase (se 3 (by rfl) ⟨583583, by rfl⟩ : syracuseStep 3112445 = 1167167) (by norm_num)
theorem B2768381 : Blo 1843623 2768381 := bbase (se 3 (by rfl) ⟨519071, by rfl⟩ : syracuseStep 2768381 = 1038143) (by norm_num)
theorem B4668941 : Blo 1843623 4668941 := bbase (se 3 (by rfl) ⟨875426, by rfl⟩ : syracuseStep 4668941 = 1750853) (by norm_num)
theorem B2768405 : Blo 1843623 2768405 := bbase (se 6 (by rfl) ⟨64884, by rfl⟩ : syracuseStep 2768405 = 129769) (by norm_num)
theorem B7003685 : Blo 1843623 7003685 := bbase (se 4 (by rfl) ⟨656595, by rfl⟩ : syracuseStep 7003685 = 1313191) (by norm_num)
theorem B2334253 : Blo 1843623 2334253 := bbase (se 3 (by rfl) ⟨437672, by rfl⟩ : syracuseStep 2334253 = 875345) (by norm_num)
theorem B4734509 : Blo 1843623 4734509 := bbase (se 3 (by rfl) ⟨887720, by rfl⟩ : syracuseStep 4734509 = 1775441) (by norm_num)
theorem B2768429 : Blo 1843623 2768429 := bbase (se 3 (by rfl) ⟨519080, by rfl⟩ : syracuseStep 2768429 = 1038161) (by norm_num)
theorem B10649141 : Blo 1843623 10649141 := bbase (se 5 (by rfl) ⟨499178, by rfl⟩ : syracuseStep 10649141 = 998357) (by norm_num)
theorem B3939941 : Blo 1843623 3939941 := bbase (se 4 (by rfl) ⟨369369, by rfl⟩ : syracuseStep 3939941 = 738739) (by norm_num)
theorem B3939949 : Blo 1843623 3939949 := bbase (se 3 (by rfl) ⟨738740, by rfl⟩ : syracuseStep 3939949 = 1477481) (by norm_num)
theorem B5987957 : Blo 1843623 5987957 := bbase (se 5 (by rfl) ⟨280685, by rfl⟩ : syracuseStep 5987957 = 561371) (by norm_num)
theorem B3112573 : Blo 1843623 3112573 := bbase (se 3 (by rfl) ⟨583607, by rfl⟩ : syracuseStep 3112573 = 1167215) (by norm_num)
theorem B2662021 : Blo 1843623 2662021 := bbase (se 4 (by rfl) ⟨249564, by rfl⟩ : syracuseStep 2662021 = 499129) (by norm_num)
theorem B3325573 : Blo 1843623 3325573 := bbase (se 4 (by rfl) ⟨311772, by rfl⟩ : syracuseStep 3325573 = 623545) (by norm_num)
theorem B2334349 : Blo 1843623 2334349 := bbase (se 3 (by rfl) ⟨437690, by rfl⟩ : syracuseStep 2334349 = 875381) (by norm_num)
theorem B8412821 : Blo 1843623 8412821 := bbase (se 6 (by rfl) ⟨197175, by rfl⟩ : syracuseStep 8412821 = 394351) (by norm_num)
theorem B6225605 : Blo 1843623 6225605 := bbase (se 4 (by rfl) ⟨583650, by rfl⟩ : syracuseStep 6225605 = 1167301) (by norm_num)
theorem B3112661 : Blo 1843623 3112661 := bbase (se 7 (by rfl) ⟨36476, by rfl⟩ : syracuseStep 3112661 = 72953) (by norm_num)
theorem B2334521 : Blo 1843623 2334521 := bbase (se 2 (by rfl) ⟨875445, by rfl⟩ : syracuseStep 2334521 = 1750891) (by norm_num)
theorem B3112789 : Blo 1843623 3112789 := bbase (se 9 (by rfl) ⟨9119, by rfl⟩ : syracuseStep 3112789 = 18239) (by norm_num)
theorem B3325789 : Blo 1843623 3325789 := bbase (se 3 (by rfl) ⟨623585, by rfl⟩ : syracuseStep 3325789 = 1247171) (by norm_num)
theorem B4669285 : Blo 1843623 4669285 := bbase (se 4 (by rfl) ⟨437745, by rfl⟩ : syracuseStep 4669285 = 875491) (by norm_num)
theorem B2334577 : Blo 1843623 2334577 := bbase (se 2 (by rfl) ⟨875466, by rfl⟩ : syracuseStep 2334577 = 1750933) (by norm_num)
theorem B7880581 : Blo 1843623 7880581 := bbase (se 4 (by rfl) ⟨738804, by rfl⟩ : syracuseStep 7880581 = 1477609) (by norm_num)
theorem B3112877 : Blo 1843623 3112877 := bbase (se 3 (by rfl) ⟨583664, by rfl⟩ : syracuseStep 3112877 = 1167329) (by norm_num)
theorem B2334673 : Blo 1843623 2334673 := bbase (se 2 (by rfl) ⟨875502, by rfl⟩ : syracuseStep 2334673 = 1751005) (by norm_num)
theorem B4669397 : Blo 1843623 4669397 := bbase (se 7 (by rfl) ⟨54719, by rfl⟩ : syracuseStep 4669397 = 109439) (by norm_num)
theorem B2736101 : Blo 1843623 2736101 := bbase (se 4 (by rfl) ⟨256509, by rfl⟩ : syracuseStep 2736101 = 513019) (by norm_num)
theorem B5611493 : Blo 1843623 5611493 := bbase (se 4 (by rfl) ⟨526077, by rfl⟩ : syracuseStep 5611493 = 1052155) (by norm_num)
theorem B11812877 : Blo 1843623 11812877 := bstep (se 3 (by rfl) ⟨2214914, by rfl⟩ : syracuseStep 11812877 = 4429829) B4429829
theorem B2334739 : Blo 1843623 2334739 := bstep (se 1 (by rfl) ⟨1751054, by rfl⟩ : syracuseStep 2334739 = 3502109) B3502109
theorem B7880753 : Blo 1843623 7880753 := bstep (se 2 (by rfl) ⟨2955282, by rfl⟩ : syracuseStep 7880753 = 5910565) B5910565
theorem B18219077 : Blo 1843623 18219077 := bstep (se 4 (by rfl) ⟨1708038, by rfl⟩ : syracuseStep 18219077 = 3416077) B3416077
theorem B3113059 : Blo 1843623 3113059 := bstep (se 1 (by rfl) ⟨2334794, by rfl⟩ : syracuseStep 3113059 = 4669589) B4669589
theorem B2334835 : Blo 1843623 2334835 := bstep (se 1 (by rfl) ⟨1751126, by rfl⟩ : syracuseStep 2334835 = 3502253) B3502253
theorem B3113201 : Blo 1843623 3113201 := bstep (se 2 (by rfl) ⟨1167450, by rfl⟩ : syracuseStep 3113201 = 2334901) B2334901
theorem B3940625 : Blo 1843623 3940625 := bstep (se 2 (by rfl) ⟨1477734, by rfl⟩ : syracuseStep 3940625 = 2955469) B2955469
theorem B6226253 : Blo 1843623 6226253 := bstep (se 3 (by rfl) ⟨1167422, by rfl⟩ : syracuseStep 6226253 = 2334845) B2334845
theorem B3113329 : Blo 1843623 3113329 := bstep (se 2 (by rfl) ⟨1167498, by rfl⟩ : syracuseStep 3113329 = 2334997) B2334997
theorem B6226307 : Blo 1843623 6226307 := bstep (se 1 (by rfl) ⟨4669730, by rfl⟩ : syracuseStep 6226307 = 9339461) B9339461
theorem B3113363 : Blo 1843623 3113363 := bstep (se 1 (by rfl) ⟨2335022, by rfl⟩ : syracuseStep 3113363 = 4670045) B4670045
theorem B9339299 : Blo 1843623 9339299 := bstep (se 1 (by rfl) ⟨7004474, by rfl⟩ : syracuseStep 9339299 = 14008949) B14008949
theorem B1843635 : Blo 1843623 1843635 := bstep (se 1 (by rfl) ⟨1382726, by rfl⟩ : syracuseStep 1843635 = 2765453) B2765453
theorem B1843651 : Blo 1843623 1843651 := bstep (se 1 (by rfl) ⟨1382738, by rfl⟩ : syracuseStep 1843651 = 2765477) B2765477
theorem B1843667 : Blo 1843623 1843667 := bstep (se 1 (by rfl) ⟨1382750, by rfl⟩ : syracuseStep 1843667 = 2765501) B2765501
theorem B1843683 : Blo 1843623 1843683 := bstep (se 1 (by rfl) ⟨1382762, by rfl⟩ : syracuseStep 1843683 = 2765525) B2765525
theorem B12616163 : Blo 1843623 12616163 := bstep (se 1 (by rfl) ⟨9462122, by rfl⟩ : syracuseStep 12616163 = 18924245) B18924245
theorem B35471843 : Blo 1843623 35471843 := bstep (se 1 (by rfl) ⟨26603882, by rfl⟩ : syracuseStep 35471843 = 53207765) B53207765
theorem B7004657 : Blo 1843623 7004657 := bstep (se 2 (by rfl) ⟨2626746, by rfl⟩ : syracuseStep 7004657 = 5253493) B5253493
theorem B1843699 : Blo 1843623 1843699 := bstep (se 1 (by rfl) ⟨1382774, by rfl⟩ : syracuseStep 1843699 = 2765549) B2765549
theorem B1843715 : Blo 1843623 1843715 := bstep (se 1 (by rfl) ⟨1382786, by rfl⟩ : syracuseStep 1843715 = 2765573) B2765573
theorem B1843731 : Blo 1843623 1843731 := bstep (se 1 (by rfl) ⟨1382798, by rfl⟩ : syracuseStep 1843731 = 2765597) B2765597
theorem B3113491 : Blo 1843623 3113491 := bstep (se 1 (by rfl) ⟨2335118, by rfl⟩ : syracuseStep 3113491 = 4670237) B4670237
theorem B1843747 : Blo 1843623 1843747 := bstep (se 1 (by rfl) ⟨1382810, by rfl⟩ : syracuseStep 1843747 = 2765621) B2765621
theorem B10510883 : Blo 1843623 10510883 := bstep (se 1 (by rfl) ⟨7883162, by rfl⟩ : syracuseStep 10510883 = 15766325) B15766325
theorem B1843763 : Blo 1843623 1843763 := bstep (se 1 (by rfl) ⟨1382822, by rfl⟩ : syracuseStep 1843763 = 2765645) B2765645
theorem B1843779 : Blo 1843623 1843779 := bstep (se 1 (by rfl) ⟨1382834, by rfl⟩ : syracuseStep 1843779 = 2765669) B2765669
theorem B1843795 : Blo 1843623 1843795 := bstep (se 1 (by rfl) ⟨1382846, by rfl⟩ : syracuseStep 1843795 = 2765693) B2765693
theorem B1843811 : Blo 1843623 1843811 := bstep (se 1 (by rfl) ⟨1382858, by rfl⟩ : syracuseStep 1843811 = 2765717) B2765717
theorem B2335331 : Blo 1843623 2335331 := bstep (se 1 (by rfl) ⟨1751498, by rfl⟩ : syracuseStep 2335331 = 3502997) B3502997
theorem B5907053 : Blo 1843623 5907053 := bstep (se 3 (by rfl) ⟨1107572, by rfl⟩ : syracuseStep 5907053 = 2215145) B2215145
theorem B1843827 : Blo 1843623 1843827 := bstep (se 1 (by rfl) ⟨1382870, by rfl⟩ : syracuseStep 1843827 = 2765741) B2765741
theorem B1843843 : Blo 1843623 1843843 := bstep (se 1 (by rfl) ⟨1382882, by rfl⟩ : syracuseStep 1843843 = 2765765) B2765765
theorem B44884621 : Blo 1843623 44884621 := bstep (se 3 (by rfl) ⟨8415866, by rfl⟩ : syracuseStep 44884621 = 16831733) B16831733
theorem B6226577 : Blo 1843623 6226577 := bstep (se 2 (by rfl) ⟨2334966, by rfl⟩ : syracuseStep 6226577 = 4669933) B4669933
theorem B1843859 : Blo 1843623 1843859 := bstep (se 1 (by rfl) ⟨1382894, by rfl⟩ : syracuseStep 1843859 = 2765789) B2765789
theorem B3113633 : Blo 1843623 3113633 := bstep (se 2 (by rfl) ⟨1167612, by rfl⟩ : syracuseStep 3113633 = 2335225) B2335225
theorem B1843875 : Blo 1843623 1843875 := bstep (se 1 (by rfl) ⟨1382906, by rfl⟩ : syracuseStep 1843875 = 2765813) B2765813
theorem B7103153 : Blo 1843623 7103153 := bstep (se 2 (by rfl) ⟨2663682, by rfl⟩ : syracuseStep 7103153 = 5327365) B5327365
theorem B1843891 : Blo 1843623 1843891 := bstep (se 1 (by rfl) ⟨1382918, by rfl⟩ : syracuseStep 1843891 = 2765837) B2765837
theorem B1843907 : Blo 1843623 1843907 := bstep (se 1 (by rfl) ⟨1382930, by rfl⟩ : syracuseStep 1843907 = 2765861) B2765861
theorem B1843923 : Blo 1843623 1843923 := bstep (se 1 (by rfl) ⟨1382942, by rfl⟩ : syracuseStep 1843923 = 2765885) B2765885
theorem B1843939 : Blo 1843623 1843939 := bstep (se 1 (by rfl) ⟨1382954, by rfl⟩ : syracuseStep 1843939 = 2765909) B2765909
theorem B5989091 : Blo 1843623 5989091 := bstep (se 1 (by rfl) ⟨4491818, by rfl⟩ : syracuseStep 5989091 = 8983637) B8983637
theorem B1843955 : Blo 1843623 1843955 := bstep (se 1 (by rfl) ⟨1382966, by rfl⟩ : syracuseStep 1843955 = 2765933) B2765933
theorem B1843971 : Blo 1843623 1843971 := bstep (se 1 (by rfl) ⟨1382978, by rfl⟩ : syracuseStep 1843971 = 2765957) B2765957
theorem B5251853 : Blo 1843623 5251853 := bstep (se 3 (by rfl) ⟨984722, by rfl⟩ : syracuseStep 5251853 = 1969445) B1969445
theorem B1843987 : Blo 1843623 1843987 := bstep (se 1 (by rfl) ⟨1382990, by rfl⟩ : syracuseStep 1843987 = 2765981) B2765981
theorem B3113761 : Blo 1843623 3113761 := bstep (se 2 (by rfl) ⟨1167660, by rfl⟩ : syracuseStep 3113761 = 2335321) B2335321
theorem B1844003 : Blo 1843623 1844003 := bstep (se 1 (by rfl) ⟨1383002, by rfl⟩ : syracuseStep 1844003 = 2766005) B2766005
theorem B4670257 : Blo 1843623 4670257 := bstep (se 2 (by rfl) ⟨1751346, by rfl⟩ : syracuseStep 4670257 = 3502693) B3502693
theorem B1844019 : Blo 1843623 1844019 := bstep (se 1 (by rfl) ⟨1383014, by rfl⟩ : syracuseStep 1844019 = 2766029) B2766029
theorem B1844035 : Blo 1843623 1844035 := bstep (se 1 (by rfl) ⟨1383026, by rfl⟩ : syracuseStep 1844035 = 2766053) B2766053
theorem B3113795 : Blo 1843623 3113795 := bstep (se 1 (by rfl) ⟨2335346, by rfl⟩ : syracuseStep 3113795 = 4670693) B4670693
theorem B1844051 : Blo 1843623 1844051 := bstep (se 1 (by rfl) ⟨1383038, by rfl⟩ : syracuseStep 1844051 = 2766077) B2766077
theorem B1844067 : Blo 1843623 1844067 := bstep (se 1 (by rfl) ⟨1383050, by rfl⟩ : syracuseStep 1844067 = 2766101) B2766101
theorem B1844083 : Blo 1843623 1844083 := bstep (se 1 (by rfl) ⟨1383062, by rfl⟩ : syracuseStep 1844083 = 2766125) B2766125
theorem B1844099 : Blo 1843623 1844099 := bstep (se 1 (by rfl) ⟨1383074, by rfl⟩ : syracuseStep 1844099 = 2766149) B2766149
theorem B151397261 : Blo 1843623 151397261 := bstep (se 3 (by rfl) ⟨28386986, by rfl⟩ : syracuseStep 151397261 = 56773973) B56773973
theorem B1844115 : Blo 1843623 1844115 := bstep (se 1 (by rfl) ⟨1383086, by rfl⟩ : syracuseStep 1844115 = 2766173) B2766173
theorem B1844131 : Blo 1843623 1844131 := bstep (se 1 (by rfl) ⟨1383098, by rfl⟩ : syracuseStep 1844131 = 2766197) B2766197
theorem B1844147 : Blo 1843623 1844147 := bstep (se 1 (by rfl) ⟨1383110, by rfl⟩ : syracuseStep 1844147 = 2766221) B2766221
theorem B2663347 : Blo 1843623 2663347 := bstep (se 1 (by rfl) ⟨1997510, by rfl⟩ : syracuseStep 2663347 = 3995021) B3995021
theorem B1844163 : Blo 1843623 1844163 := bstep (se 1 (by rfl) ⟨1383122, by rfl⟩ : syracuseStep 1844163 = 2766245) B2766245
theorem B5252035 : Blo 1843623 5252035 := bstep (se 1 (by rfl) ⟨3939026, by rfl⟩ : syracuseStep 5252035 = 7878053) B7878053
theorem B22438853 : Blo 1843623 22438853 := bstep (se 4 (by rfl) ⟨2103642, by rfl⟩ : syracuseStep 22438853 = 4207285) B4207285
theorem B3113923 : Blo 1843623 3113923 := bstep (se 1 (by rfl) ⟨2335442, by rfl⟩ : syracuseStep 3113923 = 4670885) B4670885
theorem B1844179 : Blo 1843623 1844179 := bstep (se 1 (by rfl) ⟨1383134, by rfl⟩ : syracuseStep 1844179 = 2766269) B2766269
theorem B1844195 : Blo 1843623 1844195 := bstep (se 1 (by rfl) ⟨1383146, by rfl⟩ : syracuseStep 1844195 = 2766293) B2766293
theorem B1844211 : Blo 1843623 1844211 := bstep (se 1 (by rfl) ⟨1383158, by rfl⟩ : syracuseStep 1844211 = 2766317) B2766317
theorem B1844227 : Blo 1843623 1844227 := bstep (se 1 (by rfl) ⟨1383170, by rfl⟩ : syracuseStep 1844227 = 2766341) B2766341
theorem B1844243 : Blo 1843623 1844243 := bstep (se 1 (by rfl) ⟨1383182, by rfl⟩ : syracuseStep 1844243 = 2766365) B2766365
theorem B1844259 : Blo 1843623 1844259 := bstep (se 1 (by rfl) ⟨1383194, by rfl⟩ : syracuseStep 1844259 = 2766389) B2766389
theorem B1844275 : Blo 1843623 1844275 := bstep (se 1 (by rfl) ⟨1383206, by rfl⟩ : syracuseStep 1844275 = 2766413) B2766413
theorem B1844291 : Blo 1843623 1844291 := bstep (se 1 (by rfl) ⟨1383218, by rfl⟩ : syracuseStep 1844291 = 2766437) B2766437
theorem B4670531 : Blo 1843623 4670531 := bstep (se 1 (by rfl) ⟨3502898, by rfl⟩ : syracuseStep 4670531 = 7005797) B7005797
theorem B3114065 : Blo 1843623 3114065 := bstep (se 2 (by rfl) ⟨1167774, by rfl⟩ : syracuseStep 3114065 = 2335549) B2335549
theorem B1844307 : Blo 1843623 1844307 := bstep (se 1 (by rfl) ⟨1383230, by rfl⟩ : syracuseStep 1844307 = 2766461) B2766461
theorem B1844323 : Blo 1843623 1844323 := bstep (se 1 (by rfl) ⟨1383242, by rfl⟩ : syracuseStep 1844323 = 2766485) B2766485
theorem B5252195 : Blo 1843623 5252195 := bstep (se 1 (by rfl) ⟨3939146, by rfl⟩ : syracuseStep 5252195 = 7878293) B7878293
theorem B1844339 : Blo 1843623 1844339 := bstep (se 1 (by rfl) ⟨1383254, by rfl⟩ : syracuseStep 1844339 = 2766509) B2766509
theorem B1844355 : Blo 1843623 1844355 := bstep (se 1 (by rfl) ⟨1383266, by rfl⟩ : syracuseStep 1844355 = 2766533) B2766533
theorem B3155075 : Blo 1843623 3155075 := bstep (se 1 (by rfl) ⟨2366306, by rfl⟩ : syracuseStep 3155075 = 4732613) B4732613
theorem B7005325 : Blo 1843623 7005325 := bstep (se 3 (by rfl) ⟨1313498, by rfl⟩ : syracuseStep 7005325 = 2626997) B2626997
theorem B1844371 : Blo 1843623 1844371 := bstep (se 1 (by rfl) ⟨1383278, by rfl⟩ : syracuseStep 1844371 = 2766557) B2766557
theorem B1844387 : Blo 1843623 1844387 := bstep (se 1 (by rfl) ⟨1383290, by rfl⟩ : syracuseStep 1844387 = 2766581) B2766581
theorem B6227117 : Blo 1843623 6227117 := bstep (se 3 (by rfl) ⟨1167584, by rfl⟩ : syracuseStep 6227117 = 2335169) B2335169
theorem B1844403 : Blo 1843623 1844403 := bstep (se 1 (by rfl) ⟨1383302, by rfl⟩ : syracuseStep 1844403 = 2766605) B2766605
theorem B1844419 : Blo 1843623 1844419 := bstep (se 1 (by rfl) ⟨1383314, by rfl⟩ : syracuseStep 1844419 = 2766629) B2766629
theorem B5989571 : Blo 1843623 5989571 := bstep (se 1 (by rfl) ⟨4492178, by rfl⟩ : syracuseStep 5989571 = 8984357) B8984357
theorem B9340109 : Blo 1843623 9340109 := bstep (se 3 (by rfl) ⟨1751270, by rfl⟩ : syracuseStep 9340109 = 3502541) B3502541
theorem B3114193 : Blo 1843623 3114193 := bstep (se 2 (by rfl) ⟨1167822, by rfl⟩ : syracuseStep 3114193 = 2335645) B2335645
theorem B1844435 : Blo 1843623 1844435 := bstep (se 1 (by rfl) ⟨1383326, by rfl⟩ : syracuseStep 1844435 = 2766653) B2766653
theorem B1844451 : Blo 1843623 1844451 := bstep (se 1 (by rfl) ⟨1383338, by rfl⟩ : syracuseStep 1844451 = 2766677) B2766677
theorem B6227171 : Blo 1843623 6227171 := bstep (se 1 (by rfl) ⟨4670378, by rfl⟩ : syracuseStep 6227171 = 9340757) B9340757
theorem B1844467 : Blo 1843623 1844467 := bstep (se 1 (by rfl) ⟨1383350, by rfl⟩ : syracuseStep 1844467 = 2766701) B2766701
theorem B3114227 : Blo 1843623 3114227 := bstep (se 1 (by rfl) ⟨2335670, by rfl⟩ : syracuseStep 3114227 = 4671341) B4671341
theorem B1844483 : Blo 1843623 1844483 := bstep (se 1 (by rfl) ⟨1383362, by rfl⟩ : syracuseStep 1844483 = 2766725) B2766725
theorem B4670723 : Blo 1843623 4670723 := bstep (se 1 (by rfl) ⟨3503042, by rfl⟩ : syracuseStep 4670723 = 7006085) B7006085
theorem B1844499 : Blo 1843623 1844499 := bstep (se 1 (by rfl) ⟨1383374, by rfl⟩ : syracuseStep 1844499 = 2766749) B2766749
theorem B1844515 : Blo 1843623 1844515 := bstep (se 1 (by rfl) ⟨1383386, by rfl⟩ : syracuseStep 1844515 = 2766773) B2766773
theorem B1844531 : Blo 1843623 1844531 := bstep (se 1 (by rfl) ⟨1383398, by rfl⟩ : syracuseStep 1844531 = 2766797) B2766797
theorem B1844547 : Blo 1843623 1844547 := bstep (se 1 (by rfl) ⟨1383410, by rfl⟩ : syracuseStep 1844547 = 2766821) B2766821
theorem B1844563 : Blo 1843623 1844563 := bstep (se 1 (by rfl) ⟨1383422, by rfl⟩ : syracuseStep 1844563 = 2766845) B2766845
theorem B1844579 : Blo 1843623 1844579 := bstep (se 1 (by rfl) ⟨1383434, by rfl⟩ : syracuseStep 1844579 = 2766869) B2766869
theorem B4433251 : Blo 1843623 4433251 := bstep (se 1 (by rfl) ⟨3324938, by rfl⟩ : syracuseStep 4433251 = 6649877) B6649877
theorem B1844595 : Blo 1843623 1844595 := bstep (se 1 (by rfl) ⟨1383446, by rfl⟩ : syracuseStep 1844595 = 2766893) B2766893
theorem B3114355 : Blo 1843623 3114355 := bstep (se 1 (by rfl) ⟨2335766, by rfl⟩ : syracuseStep 3114355 = 4671533) B4671533
theorem B1844611 : Blo 1843623 1844611 := bstep (se 1 (by rfl) ⟨1383458, by rfl⟩ : syracuseStep 1844611 = 2766917) B2766917
theorem B1844627 : Blo 1843623 1844627 := bstep (se 1 (by rfl) ⟨1383470, by rfl⟩ : syracuseStep 1844627 = 2766941) B2766941
theorem B1844643 : Blo 1843623 1844643 := bstep (se 1 (by rfl) ⟨1383482, by rfl⟩ : syracuseStep 1844643 = 2766965) B2766965
theorem B6399395 : Blo 1843623 6399395 := bstep (se 1 (by rfl) ⟨4799546, by rfl⟩ : syracuseStep 6399395 = 9599093) B9599093
theorem B5760433 : Blo 1843623 5760433 := bstep (se 2 (by rfl) ⟨2160162, by rfl⟩ : syracuseStep 5760433 = 4320325) B4320325
theorem B1844659 : Blo 1843623 1844659 := bstep (se 1 (by rfl) ⟨1383494, by rfl⟩ : syracuseStep 1844659 = 2766989) B2766989
theorem B1844675 : Blo 1843623 1844675 := bstep (se 1 (by rfl) ⟨1383506, by rfl⟩ : syracuseStep 1844675 = 2767013) B2767013
theorem B12625357 : Blo 1843623 12625357 := bstep (se 3 (by rfl) ⟨2367254, by rfl⟩ : syracuseStep 12625357 = 4734509) B4734509
theorem B1844691 : Blo 1843623 1844691 := bstep (se 1 (by rfl) ⟨1383518, by rfl⟩ : syracuseStep 1844691 = 2767037) B2767037
theorem B3155411 : Blo 1843623 3155411 := bstep (se 1 (by rfl) ⟨2366558, by rfl⟩ : syracuseStep 3155411 = 4733117) B4733117
theorem B1844707 : Blo 1843623 1844707 := bstep (se 1 (by rfl) ⟨1383530, by rfl⟩ : syracuseStep 1844707 = 2767061) B2767061
theorem B6227441 : Blo 1843623 6227441 := bstep (se 2 (by rfl) ⟨2335290, by rfl⟩ : syracuseStep 6227441 = 4670581) B4670581
theorem B2074099 : Blo 1843623 2074099 := bstep (se 1 (by rfl) ⟨1555574, by rfl⟩ : syracuseStep 2074099 = 3111149) B3111149
theorem B1844723 : Blo 1843623 1844723 := bstep (se 1 (by rfl) ⟨1383542, by rfl⟩ : syracuseStep 1844723 = 2767085) B2767085
theorem B1844739 : Blo 1843623 1844739 := bstep (se 1 (by rfl) ⟨1383554, by rfl⟩ : syracuseStep 1844739 = 2767109) B2767109
theorem B1844755 : Blo 1843623 1844755 := bstep (se 1 (by rfl) ⟨1383566, by rfl⟩ : syracuseStep 1844755 = 2767133) B2767133
theorem B1844771 : Blo 1843623 1844771 := bstep (se 1 (by rfl) ⟨1383578, by rfl⟩ : syracuseStep 1844771 = 2767157) B2767157
theorem B1844787 : Blo 1843623 1844787 := bstep (se 1 (by rfl) ⟨1383590, by rfl⟩ : syracuseStep 1844787 = 2767181) B2767181
theorem B2803265 : Blo 1843623 2803265 := bstep (se 2 (by rfl) ⟨1051224, by rfl⟩ : syracuseStep 2803265 = 2102449) B2102449
theorem B1844803 : Blo 1843623 1844803 := bstep (se 1 (by rfl) ⟨1383602, by rfl⟩ : syracuseStep 1844803 = 2767205) B2767205
theorem B1844819 : Blo 1843623 1844819 := bstep (se 1 (by rfl) ⟨1383614, by rfl⟩ : syracuseStep 1844819 = 2767229) B2767229
theorem B12617315 : Blo 1843623 12617315 := bstep (se 1 (by rfl) ⟨9462986, by rfl⟩ : syracuseStep 12617315 = 18925973) B18925973
theorem B1844835 : Blo 1843623 1844835 := bstep (se 1 (by rfl) ⟨1383626, by rfl⟩ : syracuseStep 1844835 = 2767253) B2767253
theorem B1844851 : Blo 1843623 1844851 := bstep (se 1 (by rfl) ⟨1383638, by rfl⟩ : syracuseStep 1844851 = 2767277) B2767277
theorem B2074243 : Blo 1843623 2074243 := bstep (se 1 (by rfl) ⟨1555682, by rfl⟩ : syracuseStep 2074243 = 3111365) B3111365
theorem B1844867 : Blo 1843623 1844867 := bstep (se 1 (by rfl) ⟨1383650, by rfl⟩ : syracuseStep 1844867 = 2767301) B2767301
theorem B1844883 : Blo 1843623 1844883 := bstep (se 1 (by rfl) ⟨1383662, by rfl⟩ : syracuseStep 1844883 = 2767325) B2767325
theorem B1844899 : Blo 1843623 1844899 := bstep (se 1 (by rfl) ⟨1383674, by rfl⟩ : syracuseStep 1844899 = 2767349) B2767349
theorem B1844915 : Blo 1843623 1844915 := bstep (se 1 (by rfl) ⟨1383686, by rfl⟩ : syracuseStep 1844915 = 2767373) B2767373
theorem B4671715 : Blo 1843623 4671715 := bstep (se 1 (by rfl) ⟨3503786, by rfl⟩ : syracuseStep 4671715 = 7007573) B7007573
theorem B1844931 : Blo 1843623 1844931 := bstep (se 1 (by rfl) ⟨1383698, by rfl⟩ : syracuseStep 1844931 = 2767397) B2767397
theorem B1844947 : Blo 1843623 1844947 := bstep (se 1 (by rfl) ⟨1383710, by rfl⟩ : syracuseStep 1844947 = 2767421) B2767421
theorem B1844963 : Blo 1843623 1844963 := bstep (se 1 (by rfl) ⟨1383722, by rfl⟩ : syracuseStep 1844963 = 2767445) B2767445
theorem B1844979 : Blo 1843623 1844979 := bstep (se 1 (by rfl) ⟨1383734, by rfl⟩ : syracuseStep 1844979 = 2767469) B2767469
theorem B1844995 : Blo 1843623 1844995 := bstep (se 1 (by rfl) ⟨1383746, by rfl⟩ : syracuseStep 1844995 = 2767493) B2767493
theorem B2074387 : Blo 1843623 2074387 := bstep (se 1 (by rfl) ⟨1555790, by rfl⟩ : syracuseStep 2074387 = 3111581) B3111581
theorem B1845011 : Blo 1843623 1845011 := bstep (se 1 (by rfl) ⟨1383758, by rfl⟩ : syracuseStep 1845011 = 2767517) B2767517
theorem B1845027 : Blo 1843623 1845027 := bstep (se 1 (by rfl) ⟨1383770, by rfl⟩ : syracuseStep 1845027 = 2767541) B2767541
theorem B1845043 : Blo 1843623 1845043 := bstep (se 1 (by rfl) ⟨1383782, by rfl⟩ : syracuseStep 1845043 = 2767565) B2767565
theorem B1845059 : Blo 1843623 1845059 := bstep (se 1 (by rfl) ⟨1383794, by rfl⟩ : syracuseStep 1845059 = 2767589) B2767589
theorem B17737541 : Blo 1843623 17737541 := bstep (se 4 (by rfl) ⟨1662894, by rfl⟩ : syracuseStep 17737541 = 3325789) B3325789
theorem B1845075 : Blo 1843623 1845075 := bstep (se 1 (by rfl) ⟨1383806, by rfl⟩ : syracuseStep 1845075 = 2767613) B2767613
theorem B1845091 : Blo 1843623 1845091 := bstep (se 1 (by rfl) ⟨1383818, by rfl⟩ : syracuseStep 1845091 = 2767637) B2767637
theorem B1845107 : Blo 1843623 1845107 := bstep (se 1 (by rfl) ⟨1383830, by rfl⟩ : syracuseStep 1845107 = 2767661) B2767661
theorem B1845123 : Blo 1843623 1845123 := bstep (se 1 (by rfl) ⟨1383842, by rfl⟩ : syracuseStep 1845123 = 2767685) B2767685
theorem B1845139 : Blo 1843623 1845139 := bstep (se 1 (by rfl) ⟨1383854, by rfl⟩ : syracuseStep 1845139 = 2767709) B2767709
theorem B2074531 : Blo 1843623 2074531 := bstep (se 1 (by rfl) ⟨1555898, by rfl⟩ : syracuseStep 2074531 = 3111797) B3111797
theorem B1845155 : Blo 1843623 1845155 := bstep (se 1 (by rfl) ⟨1383866, by rfl⟩ : syracuseStep 1845155 = 2767733) B2767733
theorem B7006115 : Blo 1843623 7006115 := bstep (se 1 (by rfl) ⟨5254586, by rfl⟩ : syracuseStep 7006115 = 10509173) B10509173
theorem B1845171 : Blo 1843623 1845171 := bstep (se 1 (by rfl) ⟨1383878, by rfl⟩ : syracuseStep 1845171 = 2767757) B2767757
theorem B1845187 : Blo 1843623 1845187 := bstep (se 1 (by rfl) ⟨1383890, by rfl⟩ : syracuseStep 1845187 = 2767781) B2767781
theorem B1845203 : Blo 1843623 1845203 := bstep (se 1 (by rfl) ⟨1383902, by rfl⟩ : syracuseStep 1845203 = 2767805) B2767805
theorem B3991523 : Blo 1843623 3991523 := bstep (se 1 (by rfl) ⟨2993642, by rfl⟩ : syracuseStep 3991523 = 5987285) B5987285
theorem B1845219 : Blo 1843623 1845219 := bstep (se 1 (by rfl) ⟨1383914, by rfl⟩ : syracuseStep 1845219 = 2767829) B2767829
theorem B1845235 : Blo 1843623 1845235 := bstep (se 1 (by rfl) ⟨1383926, by rfl⟩ : syracuseStep 1845235 = 2767853) B2767853
theorem B1845251 : Blo 1843623 1845251 := bstep (se 1 (by rfl) ⟨1383938, by rfl⟩ : syracuseStep 1845251 = 2767877) B2767877
theorem B6227981 : Blo 1843623 6227981 := bstep (se 3 (by rfl) ⟨1167746, by rfl⟩ : syracuseStep 6227981 = 2335493) B2335493
theorem B1845267 : Blo 1843623 1845267 := bstep (se 1 (by rfl) ⟨1383950, by rfl⟩ : syracuseStep 1845267 = 2767901) B2767901
theorem B1845283 : Blo 1843623 1845283 := bstep (se 1 (by rfl) ⟨1383962, by rfl⟩ : syracuseStep 1845283 = 2767925) B2767925
theorem B3500081 : Blo 1843623 3500081 := bstep (se 2 (by rfl) ⟨1312530, by rfl⟩ : syracuseStep 3500081 = 2625061) B2625061
theorem B2074675 : Blo 1843623 2074675 := bstep (se 1 (by rfl) ⟨1556006, by rfl⟩ : syracuseStep 2074675 = 3112013) B3112013
theorem B1845299 : Blo 1843623 1845299 := bstep (se 1 (by rfl) ⟨1383974, by rfl⟩ : syracuseStep 1845299 = 2767949) B2767949
theorem B1845315 : Blo 1843623 1845315 := bstep (se 1 (by rfl) ⟨1383986, by rfl⟩ : syracuseStep 1845315 = 2767973) B2767973
theorem B6228035 : Blo 1843623 6228035 := bstep (se 1 (by rfl) ⟨4671026, by rfl⟩ : syracuseStep 6228035 = 9342053) B9342053
theorem B1845331 : Blo 1843623 1845331 := bstep (se 1 (by rfl) ⟨1383998, by rfl⟩ : syracuseStep 1845331 = 2767997) B2767997
theorem B1845347 : Blo 1843623 1845347 := bstep (se 1 (by rfl) ⟨1384010, by rfl⟩ : syracuseStep 1845347 = 2768021) B2768021
theorem B1845363 : Blo 1843623 1845363 := bstep (se 1 (by rfl) ⟨1384022, by rfl⟩ : syracuseStep 1845363 = 2768045) B2768045
theorem B1845379 : Blo 1843623 1845379 := bstep (se 1 (by rfl) ⟨1384034, by rfl⟩ : syracuseStep 1845379 = 2768069) B2768069
theorem B5253265 : Blo 1843623 5253265 := bstep (se 2 (by rfl) ⟨1969974, by rfl⟩ : syracuseStep 5253265 = 3939949) B3939949
theorem B1845395 : Blo 1843623 1845395 := bstep (se 1 (by rfl) ⟨1384046, by rfl⟩ : syracuseStep 1845395 = 2768093) B2768093
theorem B1845411 : Blo 1843623 1845411 := bstep (se 1 (by rfl) ⟨1384058, by rfl⟩ : syracuseStep 1845411 = 2768117) B2768117
theorem B3549361 : Blo 1843623 3549361 := bstep (se 2 (by rfl) ⟨1331010, by rfl⟩ : syracuseStep 3549361 = 2662021) B2662021
theorem B1845427 : Blo 1843623 1845427 := bstep (se 1 (by rfl) ⟨1384070, by rfl⟩ : syracuseStep 1845427 = 2768141) B2768141
theorem B4434097 : Blo 1843623 4434097 := bstep (se 2 (by rfl) ⟨1662786, by rfl⟩ : syracuseStep 4434097 = 3325573) B3325573
theorem B4671665 : Blo 1843623 4671665 := bstep (se 2 (by rfl) ⟨1751874, by rfl⟩ : syracuseStep 4671665 = 3503749) B3503749
theorem B2074819 : Blo 1843623 2074819 := bstep (se 1 (by rfl) ⟨1556114, by rfl⟩ : syracuseStep 2074819 = 3112229) B3112229
theorem B1845443 : Blo 1843623 1845443 := bstep (se 1 (by rfl) ⟨1384082, by rfl⟩ : syracuseStep 1845443 = 2768165) B2768165
theorem B1845459 : Blo 1843623 1845459 := bstep (se 1 (by rfl) ⟨1384094, by rfl⟩ : syracuseStep 1845459 = 2768189) B2768189
theorem B7989475 : Blo 1843623 7989475 := bstep (se 1 (by rfl) ⟨5992106, by rfl⟩ : syracuseStep 7989475 = 11984213) B11984213
theorem B1845475 : Blo 1843623 1845475 := bstep (se 1 (by rfl) ⟨1384106, by rfl⟩ : syracuseStep 1845475 = 2768213) B2768213
theorem B1845491 : Blo 1843623 1845491 := bstep (se 1 (by rfl) ⟨1384118, by rfl⟩ : syracuseStep 1845491 = 2768237) B2768237
theorem B1845507 : Blo 1843623 1845507 := bstep (se 1 (by rfl) ⟨1384130, by rfl⟩ : syracuseStep 1845507 = 2768261) B2768261
theorem B1845523 : Blo 1843623 1845523 := bstep (se 1 (by rfl) ⟨1384142, by rfl⟩ : syracuseStep 1845523 = 2768285) B2768285
theorem B4434211 : Blo 1843623 4434211 := bstep (se 1 (by rfl) ⟨3325658, by rfl⟩ : syracuseStep 4434211 = 6651317) B6651317
theorem B1845539 : Blo 1843623 1845539 := bstep (se 1 (by rfl) ⟨1384154, by rfl⟩ : syracuseStep 1845539 = 2768309) B2768309
theorem B1845555 : Blo 1843623 1845555 := bstep (se 1 (by rfl) ⟨1384166, by rfl⟩ : syracuseStep 1845555 = 2768333) B2768333
theorem B1845571 : Blo 1843623 1845571 := bstep (se 1 (by rfl) ⟨1384178, by rfl⟩ : syracuseStep 1845571 = 2768357) B2768357
theorem B9464141 : Blo 1843623 9464141 := bstep (se 3 (by rfl) ⟨1774526, by rfl⟩ : syracuseStep 9464141 = 3549053) B3549053
theorem B10504525 : Blo 1843623 10504525 := bstep (se 3 (by rfl) ⟨1969598, by rfl⟩ : syracuseStep 10504525 = 3939197) B3939197
theorem B6228305 : Blo 1843623 6228305 := bstep (se 2 (by rfl) ⟨2335614, by rfl⟩ : syracuseStep 6228305 = 4671229) B4671229
theorem B2074963 : Blo 1843623 2074963 := bstep (se 1 (by rfl) ⟨1556222, by rfl⟩ : syracuseStep 2074963 = 3112445) B3112445
theorem B1845587 : Blo 1843623 1845587 := bstep (se 1 (by rfl) ⟨1384190, by rfl⟩ : syracuseStep 1845587 = 2768381) B2768381
theorem B1845603 : Blo 1843623 1845603 := bstep (se 1 (by rfl) ⟨1384202, by rfl⟩ : syracuseStep 1845603 = 2768405) B2768405
theorem B1845619 : Blo 1843623 1845619 := bstep (se 1 (by rfl) ⟨1384214, by rfl⟩ : syracuseStep 1845619 = 2768429) B2768429
theorem B2075107 : Blo 1843623 2075107 := bstep (se 1 (by rfl) ⟨1556330, by rfl⟩ : syracuseStep 2075107 = 3112661) B3112661
theorem B22432241 : Blo 1843623 22432241 := bstep (se 2 (by rfl) ⟨8412090, by rfl⟩ : syracuseStep 22432241 = 16824181) B16824181
theorem B14010893 : Blo 1843623 14010893 := bstep (se 3 (by rfl) ⟨2627042, by rfl⟩ : syracuseStep 14010893 = 5254085) B5254085
theorem B2492947 : Blo 1843623 2492947 := bstep (se 1 (by rfl) ⟨1869710, by rfl⟩ : syracuseStep 2492947 = 3739421) B3739421
theorem B7006769 : Blo 1843623 7006769 := bstep (se 2 (by rfl) ⟨2627538, by rfl⟩ : syracuseStep 7006769 = 5255077) B5255077
theorem B2075251 : Blo 1843623 2075251 := bstep (se 1 (by rfl) ⟨1556438, by rfl⟩ : syracuseStep 2075251 = 3112877) B3112877
theorem B5909233 : Blo 1843623 5909233 := bstep (se 2 (by rfl) ⟨2215962, by rfl⟩ : syracuseStep 5909233 = 4431925) B4431925
theorem B2075395 : Blo 1843623 2075395 := bstep (se 1 (by rfl) ⟨1556546, by rfl⟩ : syracuseStep 2075395 = 3113093) B3113093
theorem B4983601 : Blo 1843623 4983601 := bstep (se 2 (by rfl) ⟨1868850, by rfl⟩ : syracuseStep 4983601 = 3737701) B3737701
theorem B6228845 : Blo 1843623 6228845 := bstep (se 3 (by rfl) ⟨1167908, by rfl⟩ : syracuseStep 6228845 = 2335817) B2335817
theorem B22432625 : Blo 1843623 22432625 := bstep (se 2 (by rfl) ⟨8412234, by rfl⟩ : syracuseStep 22432625 = 16824469) B16824469
theorem B2804627 : Blo 1843623 2804627 := bstep (se 1 (by rfl) ⟨2103470, by rfl⟩ : syracuseStep 2804627 = 4206941) B4206941
theorem B2075539 : Blo 1843623 2075539 := bstep (se 1 (by rfl) ⟨1556654, by rfl⟩ : syracuseStep 2075539 = 3113309) B3113309
theorem B5909411 : Blo 1843623 5909411 := bstep (se 1 (by rfl) ⟨4432058, by rfl⟩ : syracuseStep 5909411 = 8864117) B8864117
theorem B2493347 : Blo 1843623 2493347 := bstep (se 1 (by rfl) ⟨1870010, by rfl⟩ : syracuseStep 2493347 = 3740021) B3740021
theorem B6228899 : Blo 1843623 6228899 := bstep (se 1 (by rfl) ⟨4671674, by rfl⟩ : syracuseStep 6228899 = 9343349) B9343349
theorem B3500977 : Blo 1843623 3500977 := bstep (se 2 (by rfl) ⟨1312866, by rfl⟩ : syracuseStep 3500977 = 2625733) B2625733
theorem B3738641 : Blo 1843623 3738641 := bstep (se 2 (by rfl) ⟨1401990, by rfl⟩ : syracuseStep 3738641 = 2803981) B2803981
theorem B2075683 : Blo 1843623 2075683 := bstep (se 1 (by rfl) ⟨1556762, by rfl⟩ : syracuseStep 2075683 = 3113525) B3113525
theorem B1969219 : Blo 1843623 1969219 := bstep (se 1 (by rfl) ⟨1476914, by rfl⟩ : syracuseStep 1969219 = 2953829) B2953829
theorem B3501137 : Blo 1843623 3501137 := bstep (se 2 (by rfl) ⟨1312926, by rfl⟩ : syracuseStep 3501137 = 2625853) B2625853
theorem B4148369 : Blo 1843623 4148369 := bstep (se 2 (by rfl) ⟨1555638, by rfl⟩ : syracuseStep 4148369 = 3111277) B3111277
theorem B4148387 : Blo 1843623 4148387 := bstep (se 1 (by rfl) ⟨3111290, by rfl⟩ : syracuseStep 4148387 = 6222581) B6222581
theorem B2075827 : Blo 1843623 2075827 := bstep (se 1 (by rfl) ⟨1556870, by rfl⟩ : syracuseStep 2075827 = 3113741) B3113741
theorem B15756515 : Blo 1843623 15756515 := bstep (se 1 (by rfl) ⟨11817386, by rfl⟩ : syracuseStep 15756515 = 23634773) B23634773
theorem B4984067 : Blo 1843623 4984067 := bstep (se 1 (by rfl) ⟨3738050, by rfl⟩ : syracuseStep 4984067 = 7476101) B7476101
theorem B2075971 : Blo 1843623 2075971 := bstep (se 1 (by rfl) ⟨1556978, by rfl⟩ : syracuseStep 2075971 = 3113957) B3113957
theorem B9334115 : Blo 1843623 9334115 := bstep (se 1 (by rfl) ⟨7000586, by rfl⟩ : syracuseStep 9334115 = 14001173) B14001173
theorem B5254541 : Blo 1843623 5254541 := bstep (se 3 (by rfl) ⟨985226, by rfl⟩ : syracuseStep 5254541 = 1970453) B1970453
theorem B4148657 : Blo 1843623 4148657 := bstep (se 2 (by rfl) ⟨1555746, by rfl⟩ : syracuseStep 4148657 = 3111493) B3111493
theorem B4148675 : Blo 1843623 4148675 := bstep (se 1 (by rfl) ⟨3111506, by rfl⟩ : syracuseStep 4148675 = 6223013) B6223013
theorem B2076115 : Blo 1843623 2076115 := bstep (se 1 (by rfl) ⟨1557086, by rfl⟩ : syracuseStep 2076115 = 3114173) B3114173
theorem B3501539 : Blo 1843623 3501539 := bstep (se 1 (by rfl) ⟨2626154, by rfl⟩ : syracuseStep 3501539 = 5252309) B5252309
theorem B2493985 : Blo 1843623 2493985 := bstep (se 2 (by rfl) ⟨935244, by rfl⟩ : syracuseStep 2493985 = 1870489) B1870489
theorem B5254723 : Blo 1843623 5254723 := bstep (se 1 (by rfl) ⟨3941042, by rfl⟩ : syracuseStep 5254723 = 7882085) B7882085
theorem B2076259 : Blo 1843623 2076259 := bstep (se 1 (by rfl) ⟨1557194, by rfl⟩ : syracuseStep 2076259 = 3114389) B3114389
theorem B5254769 : Blo 1843623 5254769 := bstep (se 2 (by rfl) ⟨1970538, by rfl⟩ : syracuseStep 5254769 = 3941077) B3941077
theorem B4148945 : Blo 1843623 4148945 := bstep (se 2 (by rfl) ⟨1555854, by rfl⟩ : syracuseStep 4148945 = 3111709) B3111709
theorem B4148963 : Blo 1843623 4148963 := bstep (se 1 (by rfl) ⟨3111722, by rfl⟩ : syracuseStep 4148963 = 6223445) B6223445
theorem B2805491 : Blo 1843623 2805491 := bstep (se 1 (by rfl) ⟨2104118, by rfl⟩ : syracuseStep 2805491 = 4208237) B4208237
theorem B11824973 : Blo 1843623 11824973 := bstep (se 3 (by rfl) ⟨2217182, by rfl⟩ : syracuseStep 11824973 = 4434365) B4434365
theorem B4149233 : Blo 1843623 4149233 := bstep (se 2 (by rfl) ⟨1555962, by rfl⟩ : syracuseStep 4149233 = 3111925) B3111925
theorem B2625539 : Blo 1843623 2625539 := bstep (se 1 (by rfl) ⟨1969154, by rfl⟩ : syracuseStep 2625539 = 3938309) B3938309
theorem B4149251 : Blo 1843623 4149251 := bstep (se 1 (by rfl) ⟨3111938, by rfl⟩ : syracuseStep 4149251 = 6223877) B6223877
theorem B4730897 : Blo 1843623 4730897 := bstep (se 2 (by rfl) ⟨1774086, by rfl⟩ : syracuseStep 4730897 = 3548173) B3548173
theorem B9343025 : Blo 1843623 9343025 := bstep (se 2 (by rfl) ⟨3503634, by rfl⟩ : syracuseStep 9343025 = 7007269) B7007269
theorem B11817029 : Blo 1843623 11817029 := bstep (se 4 (by rfl) ⟨1107846, by rfl⟩ : syracuseStep 11817029 = 2215693) B2215693
theorem B3551345 : Blo 1843623 3551345 := bstep (se 2 (by rfl) ⟨1331754, by rfl⟩ : syracuseStep 3551345 = 2663509) B2663509
theorem B1970291 : Blo 1843623 1970291 := bstep (se 1 (by rfl) ⟨1477718, by rfl⟩ : syracuseStep 1970291 = 2955437) B2955437
theorem B9334925 : Blo 1843623 9334925 := bstep (se 3 (by rfl) ⟨1750298, by rfl⟩ : syracuseStep 9334925 = 3500597) B3500597
theorem B26587277 : Blo 1843623 26587277 := bstep (se 3 (by rfl) ⟨4985114, by rfl⟩ : syracuseStep 26587277 = 9970229) B9970229
theorem B10506509 : Blo 1843623 10506509 := bstep (se 3 (by rfl) ⟨1969970, by rfl⟩ : syracuseStep 10506509 = 3939941) B3939941
theorem B4149521 : Blo 1843623 4149521 := bstep (se 2 (by rfl) ⟨1556070, by rfl⟩ : syracuseStep 4149521 = 3112141) B3112141
theorem B4149539 : Blo 1843623 4149539 := bstep (se 1 (by rfl) ⟨3112154, by rfl⟩ : syracuseStep 4149539 = 6224309) B6224309
theorem B4731185 : Blo 1843623 4731185 := bstep (se 2 (by rfl) ⟨1774194, by rfl⟩ : syracuseStep 4731185 = 3548389) B3548389
theorem B3502435 : Blo 1843623 3502435 := bstep (se 1 (by rfl) ⟨2626826, by rfl⟩ : syracuseStep 3502435 = 5253653) B5253653
theorem B4731299 : Blo 1843623 4731299 := bstep (se 1 (by rfl) ⟨3548474, by rfl⟩ : syracuseStep 4731299 = 7096949) B7096949
theorem B7877027 : Blo 1843623 7877027 := bstep (se 1 (by rfl) ⟨5907770, by rfl⟩ : syracuseStep 7877027 = 11815541) B11815541
theorem B6222257 : Blo 1843623 6222257 := bstep (se 2 (by rfl) ⟨2333346, by rfl⟩ : syracuseStep 6222257 = 4666693) B4666693
theorem B2216371 : Blo 1843623 2216371 := bstep (se 1 (by rfl) ⟨1662278, by rfl⟩ : syracuseStep 2216371 = 3324557) B3324557
theorem B3502595 : Blo 1843623 3502595 := bstep (se 1 (by rfl) ⟨2626946, by rfl⟩ : syracuseStep 3502595 = 5253893) B5253893
theorem B4149809 : Blo 1843623 4149809 := bstep (se 2 (by rfl) ⟨1556178, by rfl⟩ : syracuseStep 4149809 = 3112357) B3112357
theorem B4149827 : Blo 1843623 4149827 := bstep (se 1 (by rfl) ⟨3112370, by rfl⟩ : syracuseStep 4149827 = 6224741) B6224741
theorem B2765441 : Blo 1843623 2765441 := bstep (se 2 (by rfl) ⟨1037040, by rfl⟩ : syracuseStep 2765441 = 2074081) B2074081
theorem B2626177 : Blo 1843623 2626177 := bstep (se 2 (by rfl) ⟨984816, by rfl⟩ : syracuseStep 2626177 = 1969633) B1969633
theorem B5911181 : Blo 1843623 5911181 := bstep (se 3 (by rfl) ⟨1108346, by rfl⟩ : syracuseStep 5911181 = 2216693) B2216693
theorem B2765459 : Blo 1843623 2765459 := bstep (se 1 (by rfl) ⟨2074094, by rfl⟩ : syracuseStep 2765459 = 4148189) B4148189
theorem B7000739 : Blo 1843623 7000739 := bstep (se 1 (by rfl) ⟨5250554, by rfl⟩ : syracuseStep 7000739 = 10501109) B10501109
theorem B2765489 : Blo 1843623 2765489 := bstep (se 2 (by rfl) ⟨1037058, by rfl⟩ : syracuseStep 2765489 = 2074117) B2074117
theorem B8417969 : Blo 1843623 8417969 := bstep (se 2 (by rfl) ⟨3156738, by rfl⟩ : syracuseStep 8417969 = 6313477) B6313477
theorem B2765507 : Blo 1843623 2765507 := bstep (se 1 (by rfl) ⟨2074130, by rfl⟩ : syracuseStep 2765507 = 4148261) B4148261
theorem B2953937 : Blo 1843623 2953937 := bstep (se 2 (by rfl) ⟨1107726, by rfl⟩ : syracuseStep 2953937 = 2215453) B2215453
theorem B2765537 : Blo 1843623 2765537 := bstep (se 2 (by rfl) ⟨1037076, by rfl⟩ : syracuseStep 2765537 = 2074153) B2074153
theorem B2765555 : Blo 1843623 2765555 := bstep (se 1 (by rfl) ⟨2074166, by rfl⟩ : syracuseStep 2765555 = 4148333) B4148333
theorem B2626291 : Blo 1843623 2626291 := bstep (se 1 (by rfl) ⟨1969718, by rfl⟩ : syracuseStep 2626291 = 3939437) B3939437
theorem B2765585 : Blo 1843623 2765585 := bstep (se 2 (by rfl) ⟨1037094, by rfl⟩ : syracuseStep 2765585 = 2074189) B2074189
theorem B2765603 : Blo 1843623 2765603 := bstep (se 1 (by rfl) ⟨2074202, by rfl⟩ : syracuseStep 2765603 = 4148405) B4148405
theorem B2765633 : Blo 1843623 2765633 := bstep (se 2 (by rfl) ⟨1037112, by rfl⟩ : syracuseStep 2765633 = 2074225) B2074225
theorem B14005061 : Blo 1843623 14005061 := bstep (se 4 (by rfl) ⟨1312974, by rfl⟩ : syracuseStep 14005061 = 2625949) B2625949
theorem B2954065 : Blo 1843623 2954065 := bstep (se 2 (by rfl) ⟨1107774, by rfl⟩ : syracuseStep 2954065 = 2215549) B2215549
theorem B4150097 : Blo 1843623 4150097 := bstep (se 2 (by rfl) ⟨1556286, by rfl⟩ : syracuseStep 4150097 = 3112573) B3112573
theorem B2765651 : Blo 1843623 2765651 := bstep (se 1 (by rfl) ⟨2074238, by rfl⟩ : syracuseStep 2765651 = 4148477) B4148477
theorem B4150115 : Blo 1843623 4150115 := bstep (se 1 (by rfl) ⟨3112586, by rfl⟩ : syracuseStep 4150115 = 6225173) B6225173
theorem B3199843 : Blo 1843623 3199843 := bstep (se 1 (by rfl) ⟨2399882, by rfl⟩ : syracuseStep 3199843 = 4799765) B4799765
theorem B2765681 : Blo 1843623 2765681 := bstep (se 2 (by rfl) ⟨1037130, by rfl⟩ : syracuseStep 2765681 = 2074261) B2074261
theorem B2765699 : Blo 1843623 2765699 := bstep (se 1 (by rfl) ⟨2074274, by rfl⟩ : syracuseStep 2765699 = 4148549) B4148549
theorem B2765729 : Blo 1843623 2765729 := bstep (se 2 (by rfl) ⟨1037148, by rfl⟩ : syracuseStep 2765729 = 2074297) B2074297
theorem B2765747 : Blo 1843623 2765747 := bstep (se 1 (by rfl) ⟨2074310, by rfl⟩ : syracuseStep 2765747 = 4148621) B4148621
theorem B6222797 : Blo 1843623 6222797 := bstep (se 3 (by rfl) ⟨1166774, by rfl⟩ : syracuseStep 6222797 = 2333549) B2333549
theorem B2765777 : Blo 1843623 2765777 := bstep (se 2 (by rfl) ⟨1037166, by rfl⟩ : syracuseStep 2765777 = 2074333) B2074333
theorem B2765795 : Blo 1843623 2765795 := bstep (se 1 (by rfl) ⟨2074346, by rfl⟩ : syracuseStep 2765795 = 4148693) B4148693
theorem B2765825 : Blo 1843623 2765825 := bstep (se 2 (by rfl) ⟨1037184, by rfl⟩ : syracuseStep 2765825 = 2074369) B2074369
theorem B6222851 : Blo 1843623 6222851 := bstep (se 1 (by rfl) ⟨4667138, by rfl⟩ : syracuseStep 6222851 = 9334277) B9334277
theorem B2765843 : Blo 1843623 2765843 := bstep (se 1 (by rfl) ⟨2074382, by rfl⟩ : syracuseStep 2765843 = 4148765) B4148765
theorem B7099427 : Blo 1843623 7099427 := bstep (se 1 (by rfl) ⟨5324570, by rfl⟩ : syracuseStep 7099427 = 10649141) B10649141
theorem B2765873 : Blo 1843623 2765873 := bstep (se 2 (by rfl) ⟨1037202, by rfl⟩ : syracuseStep 2765873 = 2074405) B2074405
theorem B2765891 : Blo 1843623 2765891 := bstep (se 1 (by rfl) ⟨2074418, by rfl⟩ : syracuseStep 2765891 = 4148837) B4148837
theorem B2765921 : Blo 1843623 2765921 := bstep (se 2 (by rfl) ⟨1037220, by rfl⟩ : syracuseStep 2765921 = 2074441) B2074441
theorem B5608547 : Blo 1843623 5608547 := bstep (se 1 (by rfl) ⟨4206410, by rfl⟩ : syracuseStep 5608547 = 8412821) B8412821
theorem B4150385 : Blo 1843623 4150385 := bstep (se 2 (by rfl) ⟨1556394, by rfl⟩ : syracuseStep 4150385 = 3112789) B3112789
theorem B2765939 : Blo 1843623 2765939 := bstep (se 1 (by rfl) ⟨2074454, by rfl⟩ : syracuseStep 2765939 = 4148909) B4148909
theorem B4150403 : Blo 1843623 4150403 := bstep (se 1 (by rfl) ⟨3112802, by rfl⟩ : syracuseStep 4150403 = 6225605) B6225605
theorem B2765969 : Blo 1843623 2765969 := bstep (se 2 (by rfl) ⟨1037238, by rfl⟩ : syracuseStep 2765969 = 2074477) B2074477
theorem B2765987 : Blo 1843623 2765987 := bstep (se 1 (by rfl) ⟨2074490, by rfl⟩ : syracuseStep 2765987 = 4148981) B4148981
theorem B10507441 : Blo 1843623 10507441 := bstep (se 2 (by rfl) ⟨3940290, by rfl⟩ : syracuseStep 10507441 = 7880581) B7880581
theorem B2766017 : Blo 1843623 2766017 := bstep (se 2 (by rfl) ⟨1037256, by rfl⟩ : syracuseStep 2766017 = 2074513) B2074513
theorem B2766035 : Blo 1843623 2766035 := bstep (se 1 (by rfl) ⟨2074526, by rfl⟩ : syracuseStep 2766035 = 4149053) B4149053
theorem B2766065 : Blo 1843623 2766065 := bstep (se 2 (by rfl) ⟨1037274, by rfl⟩ : syracuseStep 2766065 = 2074549) B2074549
theorem B2766083 : Blo 1843623 2766083 := bstep (se 1 (by rfl) ⟨2074562, by rfl⟩ : syracuseStep 2766083 = 4149125) B4149125
theorem B7296269 : Blo 1843623 7296269 := bstep (se 3 (by rfl) ⟨1368050, by rfl⟩ : syracuseStep 7296269 = 2736101) B2736101
theorem B6223121 : Blo 1843623 6223121 := bstep (se 2 (by rfl) ⟨2333670, by rfl⟩ : syracuseStep 6223121 = 4667341) B4667341
theorem B2766113 : Blo 1843623 2766113 := bstep (se 2 (by rfl) ⟨1037292, by rfl⟩ : syracuseStep 2766113 = 2074585) B2074585
theorem B4666673 : Blo 1843623 4666673 := bstep (se 2 (by rfl) ⟨1750002, by rfl⟩ : syracuseStep 4666673 = 3500005) B3500005
theorem B2766131 : Blo 1843623 2766131 := bstep (se 1 (by rfl) ⟨2074598, by rfl⟩ : syracuseStep 2766131 = 4149197) B4149197
theorem B3740995 : Blo 1843623 3740995 := bstep (se 1 (by rfl) ⟨2805746, by rfl⟩ : syracuseStep 3740995 = 5611493) B5611493
theorem B2766161 : Blo 1843623 2766161 := bstep (se 2 (by rfl) ⟨1037310, by rfl⟩ : syracuseStep 2766161 = 2074621) B2074621
theorem B2766179 : Blo 1843623 2766179 := bstep (se 1 (by rfl) ⟨2074634, by rfl⟩ : syracuseStep 2766179 = 4149269) B4149269
theorem B39892337 : Blo 1843623 39892337 := bstep (se 2 (by rfl) ⟨14959626, by rfl⟩ : syracuseStep 39892337 = 29919253) B29919253
theorem B14013809 : Blo 1843623 14013809 := bstep (se 2 (by rfl) ⟨5255178, by rfl⟩ : syracuseStep 14013809 = 10510357) B10510357
theorem B2766209 : Blo 1843623 2766209 := bstep (se 2 (by rfl) ⟨1037328, by rfl⟩ : syracuseStep 2766209 = 2074657) B2074657
theorem B3741059 : Blo 1843623 3741059 := bstep (se 1 (by rfl) ⟨2805794, by rfl⟩ : syracuseStep 3741059 = 5611589) B5611589
theorem B4150673 : Blo 1843623 4150673 := bstep (se 2 (by rfl) ⟨1556502, by rfl⟩ : syracuseStep 4150673 = 3113005) B3113005
theorem B2766227 : Blo 1843623 2766227 := bstep (se 1 (by rfl) ⟨2074670, by rfl⟩ : syracuseStep 2766227 = 4149341) B4149341
theorem B4150691 : Blo 1843623 4150691 := bstep (se 1 (by rfl) ⟨3113018, by rfl⟩ : syracuseStep 4150691 = 6226037) B6226037
theorem B2766257 : Blo 1843623 2766257 := bstep (se 2 (by rfl) ⟨1037346, by rfl⟩ : syracuseStep 2766257 = 2074693) B2074693
theorem B2766275 : Blo 1843623 2766275 := bstep (se 1 (by rfl) ⟨2074706, by rfl⟩ : syracuseStep 2766275 = 4149413) B4149413
theorem B2766305 : Blo 1843623 2766305 := bstep (se 2 (by rfl) ⟨1037364, by rfl⟩ : syracuseStep 2766305 = 2074729) B2074729
theorem B2766323 : Blo 1843623 2766323 := bstep (se 1 (by rfl) ⟨2074742, by rfl⟩ : syracuseStep 2766323 = 4149485) B4149485
theorem B2766353 : Blo 1843623 2766353 := bstep (se 2 (by rfl) ⟨1037382, by rfl⟩ : syracuseStep 2766353 = 2074765) B2074765
theorem B2766371 : Blo 1843623 2766371 := bstep (se 1 (by rfl) ⟨2074778, by rfl⟩ : syracuseStep 2766371 = 4149557) B4149557
theorem B3503665 : Blo 1843623 3503665 := bstep (se 2 (by rfl) ⟨1313874, by rfl⟩ : syracuseStep 3503665 = 2627749) B2627749
theorem B2766401 : Blo 1843623 2766401 := bstep (se 2 (by rfl) ⟨1037400, by rfl⟩ : syracuseStep 2766401 = 2074801) B2074801
theorem B2766419 : Blo 1843623 2766419 := bstep (se 1 (by rfl) ⟨2074814, by rfl⟩ : syracuseStep 2766419 = 4149629) B4149629
theorem B3937891 : Blo 1843623 3937891 := bstep (se 1 (by rfl) ⟨2953418, by rfl⟩ : syracuseStep 3937891 = 5906837) B5906837
theorem B2766449 : Blo 1843623 2766449 := bstep (se 2 (by rfl) ⟨1037418, by rfl⟩ : syracuseStep 2766449 = 2074837) B2074837
theorem B2766467 : Blo 1843623 2766467 := bstep (se 1 (by rfl) ⟨2074850, by rfl⟩ : syracuseStep 2766467 = 4149701) B4149701
theorem B7001741 : Blo 1843623 7001741 := bstep (se 3 (by rfl) ⟨1312826, by rfl⟩ : syracuseStep 7001741 = 2625653) B2625653
theorem B2766497 : Blo 1843623 2766497 := bstep (se 2 (by rfl) ⟨1037436, by rfl⟩ : syracuseStep 2766497 = 2074873) B2074873
theorem B4150961 : Blo 1843623 4150961 := bstep (se 2 (by rfl) ⟨1556610, by rfl⟩ : syracuseStep 4150961 = 3113221) B3113221
theorem B2766515 : Blo 1843623 2766515 := bstep (se 1 (by rfl) ⟨2074886, by rfl⟩ : syracuseStep 2766515 = 4149773) B4149773
theorem B4150979 : Blo 1843623 4150979 := bstep (se 1 (by rfl) ⟨3113234, by rfl⟩ : syracuseStep 4150979 = 6226469) B6226469
theorem B2766545 : Blo 1843623 2766545 := bstep (se 2 (by rfl) ⟨1037454, by rfl⟩ : syracuseStep 2766545 = 2074909) B2074909
theorem B2766563 : Blo 1843623 2766563 := bstep (se 1 (by rfl) ⟨2074922, by rfl⟩ : syracuseStep 2766563 = 4149845) B4149845
theorem B2766593 : Blo 1843623 2766593 := bstep (se 2 (by rfl) ⟨1037472, by rfl⟩ : syracuseStep 2766593 = 2074945) B2074945
theorem B2766611 : Blo 1843623 2766611 := bstep (se 1 (by rfl) ⟨2074958, by rfl⟩ : syracuseStep 2766611 = 4149917) B4149917
theorem B6223661 : Blo 1843623 6223661 := bstep (se 3 (by rfl) ⟨1166936, by rfl⟩ : syracuseStep 6223661 = 2333873) B2333873
theorem B2766641 : Blo 1843623 2766641 := bstep (se 2 (by rfl) ⟨1037490, by rfl⟩ : syracuseStep 2766641 = 2074981) B2074981
theorem B2103091 : Blo 1843623 2103091 := bstep (se 1 (by rfl) ⟨1577318, by rfl⟩ : syracuseStep 2103091 = 3154637) B3154637
theorem B2955059 : Blo 1843623 2955059 := bstep (se 1 (by rfl) ⟨2216294, by rfl⟩ : syracuseStep 2955059 = 4432589) B4432589
theorem B2766659 : Blo 1843623 2766659 := bstep (se 1 (by rfl) ⟨2074994, by rfl⟩ : syracuseStep 2766659 = 4149989) B4149989
theorem B2766689 : Blo 1843623 2766689 := bstep (se 2 (by rfl) ⟨1037508, by rfl⟩ : syracuseStep 2766689 = 2075017) B2075017
theorem B6223715 : Blo 1843623 6223715 := bstep (se 1 (by rfl) ⟨4667786, by rfl⟩ : syracuseStep 6223715 = 9335573) B9335573
theorem B2766707 : Blo 1843623 2766707 := bstep (se 1 (by rfl) ⟨2075030, by rfl⟩ : syracuseStep 2766707 = 4150061) B4150061
theorem B2766737 : Blo 1843623 2766737 := bstep (se 2 (by rfl) ⟨1037526, by rfl⟩ : syracuseStep 2766737 = 2075053) B2075053
theorem B2766755 : Blo 1843623 2766755 := bstep (se 1 (by rfl) ⟨2075066, by rfl⟩ : syracuseStep 2766755 = 4150133) B4150133
theorem B2766785 : Blo 1843623 2766785 := bstep (se 2 (by rfl) ⟨1037544, by rfl⟩ : syracuseStep 2766785 = 2075089) B2075089
theorem B4151249 : Blo 1843623 4151249 := bstep (se 2 (by rfl) ⟨1556718, by rfl⟩ : syracuseStep 4151249 = 3113437) B3113437
theorem B2766803 : Blo 1843623 2766803 := bstep (se 1 (by rfl) ⟨2075102, by rfl⟩ : syracuseStep 2766803 = 4150205) B4150205
theorem B4151267 : Blo 1843623 4151267 := bstep (se 1 (by rfl) ⟨3113450, by rfl⟩ : syracuseStep 4151267 = 6226901) B6226901
theorem B2766833 : Blo 1843623 2766833 := bstep (se 2 (by rfl) ⟨1037562, by rfl⟩ : syracuseStep 2766833 = 2075125) B2075125
theorem B2766851 : Blo 1843623 2766851 := bstep (se 1 (by rfl) ⟨2075138, by rfl⟩ : syracuseStep 2766851 = 4150277) B4150277
theorem B2766881 : Blo 1843623 2766881 := bstep (se 2 (by rfl) ⟨1037580, by rfl⟩ : syracuseStep 2766881 = 2075161) B2075161
theorem B2766899 : Blo 1843623 2766899 := bstep (se 1 (by rfl) ⟨2075174, by rfl⟩ : syracuseStep 2766899 = 4150349) B4150349
theorem B2627635 : Blo 1843623 2627635 := bstep (se 1 (by rfl) ⟨1970726, by rfl⟩ : syracuseStep 2627635 = 3941453) B3941453
theorem B6649933 : Blo 1843623 6649933 := bstep (se 3 (by rfl) ⟨1246862, by rfl⟩ : syracuseStep 6649933 = 2493725) B2493725
theorem B2766929 : Blo 1843623 2766929 := bstep (se 2 (by rfl) ⟨1037598, by rfl⟩ : syracuseStep 2766929 = 2075197) B2075197
theorem B2766947 : Blo 1843623 2766947 := bstep (se 1 (by rfl) ⟨2075210, by rfl⟩ : syracuseStep 2766947 = 4150421) B4150421
theorem B6223985 : Blo 1843623 6223985 := bstep (se 2 (by rfl) ⟨2333994, by rfl⟩ : syracuseStep 6223985 = 4667989) B4667989
theorem B2766977 : Blo 1843623 2766977 := bstep (se 2 (by rfl) ⟨1037616, by rfl⟩ : syracuseStep 2766977 = 2075233) B2075233
theorem B2766995 : Blo 1843623 2766995 := bstep (se 1 (by rfl) ⟨2075246, by rfl⟩ : syracuseStep 2766995 = 4150493) B4150493
theorem B5609645 : Blo 1843623 5609645 := bstep (se 3 (by rfl) ⟨1051808, by rfl⟩ : syracuseStep 5609645 = 2103617) B2103617
theorem B2767025 : Blo 1843623 2767025 := bstep (se 2 (by rfl) ⟨1037634, by rfl⟩ : syracuseStep 2767025 = 2075269) B2075269
theorem B2767043 : Blo 1843623 2767043 := bstep (se 1 (by rfl) ⟨2075282, by rfl⟩ : syracuseStep 2767043 = 4150565) B4150565
theorem B2767073 : Blo 1843623 2767073 := bstep (se 2 (by rfl) ⟨1037652, by rfl⟩ : syracuseStep 2767073 = 2075305) B2075305
theorem B8411363 : Blo 1843623 8411363 := bstep (se 1 (by rfl) ⟨6308522, by rfl⟩ : syracuseStep 8411363 = 12617045) B12617045
theorem B4151537 : Blo 1843623 4151537 := bstep (se 2 (by rfl) ⟨1556826, by rfl⟩ : syracuseStep 4151537 = 3113653) B3113653
theorem B2767091 : Blo 1843623 2767091 := bstep (se 1 (by rfl) ⟨2075318, by rfl⟩ : syracuseStep 2767091 = 4150637) B4150637
theorem B3111169 : Blo 1843623 3111169 := bstep (se 2 (by rfl) ⟨1166688, by rfl⟩ : syracuseStep 3111169 = 2333377) B2333377
theorem B4151555 : Blo 1843623 4151555 := bstep (se 1 (by rfl) ⟨3113666, by rfl⟩ : syracuseStep 4151555 = 6227333) B6227333
theorem B4667665 : Blo 1843623 4667665 := bstep (se 2 (by rfl) ⟨1750374, by rfl⟩ : syracuseStep 4667665 = 3500749) B3500749
theorem B2767121 : Blo 1843623 2767121 := bstep (se 2 (by rfl) ⟨1037670, by rfl⟩ : syracuseStep 2767121 = 2075341) B2075341
theorem B3111203 : Blo 1843623 3111203 := bstep (se 1 (by rfl) ⟨2333402, by rfl⟩ : syracuseStep 3111203 = 4666805) B4666805
theorem B2767139 : Blo 1843623 2767139 := bstep (se 1 (by rfl) ⟨2075354, by rfl⟩ : syracuseStep 2767139 = 4150709) B4150709
theorem B2767169 : Blo 1843623 2767169 := bstep (se 2 (by rfl) ⟨1037688, by rfl⟩ : syracuseStep 2767169 = 2075377) B2075377
theorem B2767187 : Blo 1843623 2767187 := bstep (se 1 (by rfl) ⟨2075390, by rfl⟩ : syracuseStep 2767187 = 4150781) B4150781
theorem B2767217 : Blo 1843623 2767217 := bstep (se 2 (by rfl) ⟨1037706, by rfl⟩ : syracuseStep 2767217 = 2075413) B2075413
theorem B2767235 : Blo 1843623 2767235 := bstep (se 1 (by rfl) ⟨2075426, by rfl⟩ : syracuseStep 2767235 = 4150853) B4150853
theorem B2767265 : Blo 1843623 2767265 := bstep (se 2 (by rfl) ⟨1037724, by rfl⟩ : syracuseStep 2767265 = 2075449) B2075449
theorem B3840419 : Blo 1843623 3840419 := bstep (se 1 (by rfl) ⟨2880314, by rfl⟩ : syracuseStep 3840419 = 5760629) B5760629
theorem B3111331 : Blo 1843623 3111331 := bstep (se 1 (by rfl) ⟨2333498, by rfl⟩ : syracuseStep 3111331 = 4666997) B4666997
theorem B2767283 : Blo 1843623 2767283 := bstep (se 1 (by rfl) ⟨2075462, by rfl⟩ : syracuseStep 2767283 = 4150925) B4150925
theorem B302913989 : Blo 1843623 302913989 := bstep (se 4 (by rfl) ⟨28398186, by rfl⟩ : syracuseStep 302913989 = 56796373) B56796373
theorem B2767313 : Blo 1843623 2767313 := bstep (se 2 (by rfl) ⟨1037742, by rfl⟩ : syracuseStep 2767313 = 2075485) B2075485
theorem B2767331 : Blo 1843623 2767331 := bstep (se 1 (by rfl) ⟨2075498, by rfl⟩ : syracuseStep 2767331 = 4150997) B4150997
theorem B2767361 : Blo 1843623 2767361 := bstep (se 2 (by rfl) ⟨1037760, by rfl⟩ : syracuseStep 2767361 = 2075521) B2075521
theorem B4151825 : Blo 1843623 4151825 := bstep (se 2 (by rfl) ⟨1556934, by rfl⟩ : syracuseStep 4151825 = 3113869) B3113869
theorem B2767379 : Blo 1843623 2767379 := bstep (se 1 (by rfl) ⟨2075534, by rfl⟩ : syracuseStep 2767379 = 4151069) B4151069
theorem B4667939 : Blo 1843623 4667939 := bstep (se 1 (by rfl) ⟨3500954, by rfl⟩ : syracuseStep 4667939 = 7001909) B7001909
theorem B4151843 : Blo 1843623 4151843 := bstep (se 1 (by rfl) ⟨3113882, by rfl⟩ : syracuseStep 4151843 = 6227765) B6227765
theorem B3111473 : Blo 1843623 3111473 := bstep (se 2 (by rfl) ⟨1166802, by rfl⟩ : syracuseStep 3111473 = 2333605) B2333605
theorem B2767409 : Blo 1843623 2767409 := bstep (se 2 (by rfl) ⟨1037778, by rfl⟩ : syracuseStep 2767409 = 2075557) B2075557
theorem B63871541 : Blo 1843623 63871541 := bstep (se 5 (by rfl) ⟨2993978, by rfl⟩ : syracuseStep 63871541 = 5987957) B5987957
theorem B2767427 : Blo 1843623 2767427 := bstep (se 1 (by rfl) ⟨2075570, by rfl⟩ : syracuseStep 2767427 = 4151141) B4151141
theorem B10500677 : Blo 1843623 10500677 := bstep (se 4 (by rfl) ⟨984438, by rfl⟩ : syracuseStep 10500677 = 1968877) B1968877
theorem B2767457 : Blo 1843623 2767457 := bstep (se 2 (by rfl) ⟨1037796, by rfl⟩ : syracuseStep 2767457 = 2075593) B2075593
theorem B10508899 : Blo 1843623 10508899 := bstep (se 1 (by rfl) ⟨7881674, by rfl⟩ : syracuseStep 10508899 = 15763349) B15763349
theorem B2767475 : Blo 1843623 2767475 := bstep (se 1 (by rfl) ⟨2075606, by rfl⟩ : syracuseStep 2767475 = 4151213) B4151213
theorem B6224525 : Blo 1843623 6224525 := bstep (se 3 (by rfl) ⟨1167098, by rfl⟩ : syracuseStep 6224525 = 2334197) B2334197
theorem B2767505 : Blo 1843623 2767505 := bstep (se 2 (by rfl) ⟨1037814, by rfl⟩ : syracuseStep 2767505 = 2075629) B2075629
theorem B2767523 : Blo 1843623 2767523 := bstep (se 1 (by rfl) ⟨2075642, by rfl⟩ : syracuseStep 2767523 = 4151285) B4151285
theorem B3111601 : Blo 1843623 3111601 := bstep (se 2 (by rfl) ⟨1166850, by rfl⟩ : syracuseStep 3111601 = 2333701) B2333701
theorem B4430513 : Blo 1843623 4430513 := bstep (se 2 (by rfl) ⟨1661442, by rfl⟩ : syracuseStep 4430513 = 3322885) B3322885
theorem B2767553 : Blo 1843623 2767553 := bstep (se 2 (by rfl) ⟨1037832, by rfl⟩ : syracuseStep 2767553 = 2075665) B2075665
theorem B6224579 : Blo 1843623 6224579 := bstep (se 1 (by rfl) ⟨4668434, by rfl⟩ : syracuseStep 6224579 = 9336869) B9336869
theorem B3111635 : Blo 1843623 3111635 := bstep (se 1 (by rfl) ⟨2333726, by rfl⟩ : syracuseStep 3111635 = 4667453) B4667453
theorem B2767571 : Blo 1843623 2767571 := bstep (se 1 (by rfl) ⟨2075678, by rfl⟩ : syracuseStep 2767571 = 4151357) B4151357
theorem B4668131 : Blo 1843623 4668131 := bstep (se 1 (by rfl) ⟨3501098, by rfl⟩ : syracuseStep 4668131 = 7002197) B7002197
theorem B2767601 : Blo 1843623 2767601 := bstep (se 2 (by rfl) ⟨1037850, by rfl⟩ : syracuseStep 2767601 = 2075701) B2075701
theorem B2333443 : Blo 1843623 2333443 := bstep (se 1 (by rfl) ⟨1750082, by rfl⟩ : syracuseStep 2333443 = 3500165) B3500165
theorem B2767619 : Blo 1843623 2767619 := bstep (se 1 (by rfl) ⟨2075714, by rfl⟩ : syracuseStep 2767619 = 4151429) B4151429
theorem B2767649 : Blo 1843623 2767649 := bstep (se 2 (by rfl) ⟨1037868, by rfl⟩ : syracuseStep 2767649 = 2075737) B2075737
theorem B3939121 : Blo 1843623 3939121 := bstep (se 2 (by rfl) ⟨1477170, by rfl⟩ : syracuseStep 3939121 = 2954341) B2954341
theorem B4152113 : Blo 1843623 4152113 := bstep (se 2 (by rfl) ⟨1557042, by rfl⟩ : syracuseStep 4152113 = 3114085) B3114085
theorem B2767667 : Blo 1843623 2767667 := bstep (se 1 (by rfl) ⟨2075750, by rfl⟩ : syracuseStep 2767667 = 4151501) B4151501
theorem B4152131 : Blo 1843623 4152131 := bstep (se 1 (by rfl) ⟨3114098, by rfl⟩ : syracuseStep 4152131 = 6228197) B6228197
theorem B2767697 : Blo 1843623 2767697 := bstep (se 2 (by rfl) ⟨1037886, by rfl⟩ : syracuseStep 2767697 = 2075773) B2075773
theorem B3111763 : Blo 1843623 3111763 := bstep (se 1 (by rfl) ⟨2333822, by rfl⟩ : syracuseStep 3111763 = 4667645) B4667645
theorem B2333539 : Blo 1843623 2333539 := bstep (se 1 (by rfl) ⟨1750154, by rfl⟩ : syracuseStep 2333539 = 3500309) B3500309
theorem B2767715 : Blo 1843623 2767715 := bstep (se 1 (by rfl) ⟨2075786, by rfl⟩ : syracuseStep 2767715 = 4151573) B4151573
theorem B4799345 : Blo 1843623 4799345 := bstep (se 2 (by rfl) ⟨1799754, by rfl⟩ : syracuseStep 4799345 = 3599509) B3599509
theorem B2767745 : Blo 1843623 2767745 := bstep (se 2 (by rfl) ⟨1037904, by rfl⟩ : syracuseStep 2767745 = 2075809) B2075809
theorem B2767763 : Blo 1843623 2767763 := bstep (se 1 (by rfl) ⟨2075822, by rfl⟩ : syracuseStep 2767763 = 4151645) B4151645
theorem B2767793 : Blo 1843623 2767793 := bstep (se 2 (by rfl) ⟨1037922, by rfl⟩ : syracuseStep 2767793 = 2075845) B2075845
theorem B2767811 : Blo 1843623 2767811 := bstep (se 1 (by rfl) ⟨2075858, by rfl⟩ : syracuseStep 2767811 = 4151717) B4151717
theorem B6224849 : Blo 1843623 6224849 := bstep (se 2 (by rfl) ⟨2334318, by rfl⟩ : syracuseStep 6224849 = 4668637) B4668637
theorem B3111905 : Blo 1843623 3111905 := bstep (se 2 (by rfl) ⟨1166964, by rfl⟩ : syracuseStep 3111905 = 2333929) B2333929
theorem B2767841 : Blo 1843623 2767841 := bstep (se 2 (by rfl) ⟨1037940, by rfl⟩ : syracuseStep 2767841 = 2075881) B2075881
theorem B9337841 : Blo 1843623 9337841 := bstep (se 2 (by rfl) ⟨3501690, by rfl⟩ : syracuseStep 9337841 = 7003381) B7003381
theorem B2767859 : Blo 1843623 2767859 := bstep (se 1 (by rfl) ⟨2075894, by rfl⟩ : syracuseStep 2767859 = 4151789) B4151789
theorem B7879693 : Blo 1843623 7879693 := bstep (se 3 (by rfl) ⟨1477442, by rfl⟩ : syracuseStep 7879693 = 2954885) B2954885
theorem B2767889 : Blo 1843623 2767889 := bstep (se 2 (by rfl) ⟨1037958, by rfl⟩ : syracuseStep 2767889 = 2075917) B2075917
theorem B2767907 : Blo 1843623 2767907 := bstep (se 1 (by rfl) ⟨2075930, by rfl⟩ : syracuseStep 2767907 = 4151861) B4151861
theorem B2767937 : Blo 1843623 2767937 := bstep (se 2 (by rfl) ⟨1037976, by rfl⟩ : syracuseStep 2767937 = 2075953) B2075953
theorem B4152401 : Blo 1843623 4152401 := bstep (se 2 (by rfl) ⟨1557150, by rfl⟩ : syracuseStep 4152401 = 3114301) B3114301
theorem B2767955 : Blo 1843623 2767955 := bstep (se 1 (by rfl) ⟨2075966, by rfl⟩ : syracuseStep 2767955 = 4151933) B4151933
theorem B3112033 : Blo 1843623 3112033 := bstep (se 2 (by rfl) ⟨1167012, by rfl⟩ : syracuseStep 3112033 = 2334025) B2334025
theorem B4152419 : Blo 1843623 4152419 := bstep (se 1 (by rfl) ⟨3114314, by rfl⟩ : syracuseStep 4152419 = 6228629) B6228629
theorem B10509425 : Blo 1843623 10509425 := bstep (se 2 (by rfl) ⟨3941034, by rfl⟩ : syracuseStep 10509425 = 7882069) B7882069
theorem B2767985 : Blo 1843623 2767985 := bstep (se 2 (by rfl) ⟨1037994, by rfl⟩ : syracuseStep 2767985 = 2075989) B2075989
theorem B3112067 : Blo 1843623 3112067 := bstep (se 1 (by rfl) ⟨2334050, by rfl⟩ : syracuseStep 3112067 = 4668101) B4668101
theorem B2768003 : Blo 1843623 2768003 := bstep (se 1 (by rfl) ⟨2076002, by rfl⟩ : syracuseStep 2768003 = 4152005) B4152005
theorem B2768033 : Blo 1843623 2768033 := bstep (se 2 (by rfl) ⟨1038012, by rfl⟩ : syracuseStep 2768033 = 2076025) B2076025
theorem B2768051 : Blo 1843623 2768051 := bstep (se 1 (by rfl) ⟨2076038, by rfl⟩ : syracuseStep 2768051 = 4152077) B4152077
theorem B4988099 : Blo 1843623 4988099 := bstep (se 1 (by rfl) ⟨3741074, by rfl⟩ : syracuseStep 4988099 = 7482149) B7482149
theorem B2768081 : Blo 1843623 2768081 := bstep (se 2 (by rfl) ⟨1038030, by rfl⟩ : syracuseStep 2768081 = 2076061) B2076061
theorem B2768099 : Blo 1843623 2768099 := bstep (se 1 (by rfl) ⟨2076074, by rfl⟩ : syracuseStep 2768099 = 4152149) B4152149
theorem B2768129 : Blo 1843623 2768129 := bstep (se 2 (by rfl) ⟨1038048, by rfl⟩ : syracuseStep 2768129 = 2076097) B2076097
theorem B3112195 : Blo 1843623 3112195 := bstep (se 1 (by rfl) ⟨2334146, by rfl⟩ : syracuseStep 3112195 = 4668293) B4668293
theorem B2768147 : Blo 1843623 2768147 := bstep (se 1 (by rfl) ⟨2076110, by rfl⟩ : syracuseStep 2768147 = 4152221) B4152221
theorem B5250349 : Blo 1843623 5250349 := bstep (se 3 (by rfl) ⟨984440, by rfl⟩ : syracuseStep 5250349 = 1968881) B1968881
theorem B2768177 : Blo 1843623 2768177 := bstep (se 2 (by rfl) ⟨1038066, by rfl⟩ : syracuseStep 2768177 = 2076133) B2076133
theorem B2768195 : Blo 1843623 2768195 := bstep (se 1 (by rfl) ⟨2076146, by rfl⟩ : syracuseStep 2768195 = 4152293) B4152293
theorem B2334035 : Blo 1843623 2334035 := bstep (se 1 (by rfl) ⟨1750526, by rfl⟩ : syracuseStep 2334035 = 3501053) B3501053
theorem B2768225 : Blo 1843623 2768225 := bstep (se 2 (by rfl) ⟨1038084, by rfl⟩ : syracuseStep 2768225 = 2076169) B2076169
theorem B2768243 : Blo 1843623 2768243 := bstep (se 1 (by rfl) ⟨2076182, by rfl⟩ : syracuseStep 2768243 = 4152365) B4152365
theorem B3112337 : Blo 1843623 3112337 := bstep (se 2 (by rfl) ⟨1167126, by rfl⟩ : syracuseStep 3112337 = 2334253) B2334253
theorem B2768273 : Blo 1843623 2768273 := bstep (se 2 (by rfl) ⟨1038102, by rfl⟩ : syracuseStep 2768273 = 2076205) B2076205
theorem B2768291 : Blo 1843623 2768291 := bstep (se 1 (by rfl) ⟨2076218, by rfl⟩ : syracuseStep 2768291 = 4152437) B4152437
theorem B2768321 : Blo 1843623 2768321 := bstep (se 2 (by rfl) ⟨1038120, by rfl⟩ : syracuseStep 2768321 = 2076241) B2076241
theorem B3939779 : Blo 1843623 3939779 := bstep (se 1 (by rfl) ⟨2954834, by rfl⟩ : syracuseStep 3939779 = 5909669) B5909669
theorem B2768339 : Blo 1843623 2768339 := bstep (se 1 (by rfl) ⟨2076254, by rfl⟩ : syracuseStep 2768339 = 4152509) B4152509
theorem B6225389 : Blo 1843623 6225389 := bstep (se 3 (by rfl) ⟨1167260, by rfl⟩ : syracuseStep 6225389 = 2334521) B2334521
theorem B2768369 : Blo 1843623 2768369 := bstep (se 2 (by rfl) ⟨1038138, by rfl⟩ : syracuseStep 2768369 = 2076277) B2076277
theorem B2768387 : Blo 1843623 2768387 := bstep (se 1 (by rfl) ⟨2076290, by rfl⟩ : syracuseStep 2768387 = 4152581) B4152581
theorem B5250577 : Blo 1843623 5250577 := bstep (se 2 (by rfl) ⟨1968966, by rfl⟩ : syracuseStep 5250577 = 3937933) B3937933
theorem B3112465 : Blo 1843623 3112465 := bstep (se 2 (by rfl) ⟨1167174, by rfl⟩ : syracuseStep 3112465 = 2334349) B2334349
theorem B6225443 : Blo 1843623 6225443 := bstep (se 1 (by rfl) ⟨4669082, by rfl⟩ : syracuseStep 6225443 = 9338165) B9338165
theorem B2768417 : Blo 1843623 2768417 := bstep (se 2 (by rfl) ⟨1038156, by rfl⟩ : syracuseStep 2768417 = 2076313) B2076313
theorem B3112499 : Blo 1843623 3112499 := bstep (se 1 (by rfl) ⟨2334374, by rfl⟩ : syracuseStep 3112499 = 4668749) B4668749
theorem B2768435 : Blo 1843623 2768435 := bstep (se 1 (by rfl) ⟨2076326, by rfl⟩ : syracuseStep 2768435 = 4152653) B4152653
theorem B12623501 : Blo 1843623 12623501 := bstep (se 3 (by rfl) ⟨2366906, by rfl⟩ : syracuseStep 12623501 = 4733813) B4733813
theorem B4669073 : Blo 1843623 4669073 := bstep (se 2 (by rfl) ⟨1750902, by rfl⟩ : syracuseStep 4669073 = 3501805) B3501805
theorem B2662049 : Blo 1843623 2662049 := bstep (se 2 (by rfl) ⟨998268, by rfl⟩ : syracuseStep 2662049 = 1996537) B1996537
theorem B5250737 : Blo 1843623 5250737 := bstep (se 2 (by rfl) ⟨1969026, by rfl⟩ : syracuseStep 5250737 = 3938053) B3938053
theorem B3112627 : Blo 1843623 3112627 := bstep (se 1 (by rfl) ⟨2334470, by rfl⟩ : syracuseStep 3112627 = 4668941) B4668941
theorem B4669123 : Blo 1843623 4669123 := bstep (se 1 (by rfl) ⟨3501842, by rfl⟩ : syracuseStep 4669123 = 7003685) B7003685
theorem B11976389 : Blo 1843623 11976389 := bstep (se 4 (by rfl) ⟨1122786, by rfl⟩ : syracuseStep 11976389 = 2245573) B2245573
theorem B33660613 : Blo 1843623 33660613 := bstep (se 4 (by rfl) ⟨3155682, by rfl⟩ : syracuseStep 33660613 = 6311365) B6311365
theorem B7003853 : Blo 1843623 7003853 := bstep (se 3 (by rfl) ⟨1313222, by rfl⟩ : syracuseStep 7003853 = 2626445) B2626445
theorem B8863501 : Blo 1843623 8863501 := bstep (se 3 (by rfl) ⟨1661906, by rfl⟩ : syracuseStep 8863501 = 3323813) B3323813
theorem B5250851 : Blo 1843623 5250851 := bstep (se 1 (by rfl) ⟨3938138, by rfl⟩ : syracuseStep 5250851 = 7876277) B7876277
theorem B6225713 : Blo 1843623 6225713 := bstep (se 2 (by rfl) ⟨2334642, by rfl⟩ : syracuseStep 6225713 = 4669285) B4669285
theorem B3112769 : Blo 1843623 3112769 := bstep (se 2 (by rfl) ⟨1167288, by rfl⟩ : syracuseStep 3112769 = 2334577) B2334577
theorem B4669265 : Blo 1843623 4669265 := bstep (se 2 (by rfl) ⟨1750974, by rfl⟩ : syracuseStep 4669265 = 3501949) B3501949
theorem B19947377 : Blo 1843623 19947377 := bstep (se 2 (by rfl) ⟨7480266, by rfl⟩ : syracuseStep 19947377 = 14960533) B14960533
theorem B11820977 : Blo 1843623 11820977 := bstep (se 2 (by rfl) ⟨4432866, by rfl⟩ : syracuseStep 11820977 = 8865733) B8865733
theorem B3112897 : Blo 1843623 3112897 := bstep (se 2 (by rfl) ⟨1167336, by rfl⟩ : syracuseStep 3112897 = 2334673) B2334673
theorem B3112931 : Blo 1843623 3112931 := bstep (se 1 (by rfl) ⟨2334698, by rfl⟩ : syracuseStep 3112931 = 4669397) B4669397
theorem B3112985 : Blo 1843623 3112985 := bstep (se 2 (by rfl) ⟨1167369, by rfl⟩ : syracuseStep 3112985 = 2334739) B2334739
theorem B12615725 : Blo 1843623 12615725 := bstep (se 3 (by rfl) ⟨2365448, by rfl⟩ : syracuseStep 12615725 = 4730897) B4730897
theorem B2367563 : Blo 1843623 2367563 := bstep (se 1 (by rfl) ⟨1775672, by rfl⟩ : syracuseStep 2367563 = 3551345) B3551345
theorem B3113113 : Blo 1843623 3113113 := bstep (se 2 (by rfl) ⟨1167417, by rfl⟩ : syracuseStep 3113113 = 2334835) B2334835
theorem B7004339 : Blo 1843623 7004339 := bstep (se 1 (by rfl) ⟨5253254, by rfl⟩ : syracuseStep 7004339 = 10506509) B10506509
theorem B39878837 : Blo 1843623 39878837 := bstep (se 5 (by rfl) ⟨1869320, by rfl⟩ : syracuseStep 39878837 = 3738641) B3738641
theorem B7004353 : Blo 1843623 7004353 := bstep (se 2 (by rfl) ⟨2626632, by rfl⟩ : syracuseStep 7004353 = 5253265) B5253265
theorem B3154123 : Blo 1843623 3154123 := bstep (se 1 (by rfl) ⟨2365592, by rfl⟩ : syracuseStep 3154123 = 4731185) B4731185
theorem B3154199 : Blo 1843623 3154199 := bstep (se 1 (by rfl) ⟨2365649, by rfl⟩ : syracuseStep 3154199 = 4731299) B4731299
theorem B6226199 : Blo 1843623 6226199 := bstep (se 1 (by rfl) ⟨4669649, by rfl⟩ : syracuseStep 6226199 = 9339299) B9339299
theorem B4669771 : Blo 1843623 4669771 := bstep (se 1 (by rfl) ⟨3502328, by rfl⟩ : syracuseStep 4669771 = 7004657) B7004657
theorem B2335063 : Blo 1843623 2335063 := bstep (se 1 (by rfl) ⟨1751297, by rfl⟩ : syracuseStep 2335063 = 3502595) B3502595
theorem B1843627 : Blo 1843623 1843627 := bstep (se 1 (by rfl) ⟨1382720, by rfl⟩ : syracuseStep 1843627 = 2765441) B2765441
theorem B3940787 : Blo 1843623 3940787 := bstep (se 1 (by rfl) ⟨2955590, by rfl⟩ : syracuseStep 3940787 = 5911181) B5911181
theorem B1843639 : Blo 1843623 1843639 := bstep (se 1 (by rfl) ⟨1382729, by rfl⟩ : syracuseStep 1843639 = 2765459) B2765459
theorem B1843659 : Blo 1843623 1843659 := bstep (se 1 (by rfl) ⟨1382744, by rfl⟩ : syracuseStep 1843659 = 2765489) B2765489
theorem B5611979 : Blo 1843623 5611979 := bstep (se 1 (by rfl) ⟨4208984, by rfl⟩ : syracuseStep 5611979 = 8417969) B8417969
theorem B4735435 : Blo 1843623 4735435 := bstep (se 1 (by rfl) ⟨3551576, by rfl⟩ : syracuseStep 4735435 = 7103153) B7103153
theorem B1843671 : Blo 1843623 1843671 := bstep (se 1 (by rfl) ⟨1382753, by rfl⟩ : syracuseStep 1843671 = 2765507) B2765507
theorem B4669913 : Blo 1843623 4669913 := bstep (se 2 (by rfl) ⟨1751217, by rfl⟩ : syracuseStep 4669913 = 3502435) B3502435
theorem B1843691 : Blo 1843623 1843691 := bstep (se 1 (by rfl) ⟨1382768, by rfl⟩ : syracuseStep 1843691 = 2765537) B2765537
theorem B1843703 : Blo 1843623 1843703 := bstep (se 1 (by rfl) ⟨1382777, by rfl⟩ : syracuseStep 1843703 = 2765555) B2765555
theorem B1843723 : Blo 1843623 1843723 := bstep (se 1 (by rfl) ⟨1382792, by rfl⟩ : syracuseStep 1843723 = 2765585) B2765585
theorem B1843735 : Blo 1843623 1843735 := bstep (se 1 (by rfl) ⟨1382801, by rfl⟩ : syracuseStep 1843735 = 2765603) B2765603
theorem B1843755 : Blo 1843623 1843755 := bstep (se 1 (by rfl) ⟨1382816, by rfl⟩ : syracuseStep 1843755 = 2765633) B2765633
theorem B1843767 : Blo 1843623 1843767 := bstep (se 1 (by rfl) ⟨1382825, by rfl⟩ : syracuseStep 1843767 = 2765651) B2765651
theorem B1843787 : Blo 1843623 1843787 := bstep (se 1 (by rfl) ⟨1382840, by rfl⟩ : syracuseStep 1843787 = 2765681) B2765681
theorem B1843799 : Blo 1843623 1843799 := bstep (se 1 (by rfl) ⟨1382849, by rfl⟩ : syracuseStep 1843799 = 2765699) B2765699
theorem B1843819 : Blo 1843623 1843819 := bstep (se 1 (by rfl) ⟨1382864, by rfl⟩ : syracuseStep 1843819 = 2765729) B2765729
theorem B1843831 : Blo 1843623 1843831 := bstep (se 1 (by rfl) ⟨1382873, by rfl⟩ : syracuseStep 1843831 = 2765747) B2765747
theorem B14959235 : Blo 1843623 14959235 := bstep (se 1 (by rfl) ⟨11219426, by rfl⟩ : syracuseStep 14959235 = 22438853) B22438853
theorem B1843851 : Blo 1843623 1843851 := bstep (se 1 (by rfl) ⟨1382888, by rfl⟩ : syracuseStep 1843851 = 2765777) B2765777
theorem B1843863 : Blo 1843623 1843863 := bstep (se 1 (by rfl) ⟨1382897, by rfl⟩ : syracuseStep 1843863 = 2765795) B2765795
theorem B1843883 : Blo 1843623 1843883 := bstep (se 1 (by rfl) ⟨1382912, by rfl⟩ : syracuseStep 1843883 = 2765825) B2765825
theorem B1843895 : Blo 1843623 1843895 := bstep (se 1 (by rfl) ⟨1382921, by rfl⟩ : syracuseStep 1843895 = 2765843) B2765843
theorem B1843915 : Blo 1843623 1843915 := bstep (se 1 (by rfl) ⟨1382936, by rfl⟩ : syracuseStep 1843915 = 2765873) B2765873
theorem B19456717 : Blo 1843623 19456717 := bstep (se 3 (by rfl) ⟨3648134, by rfl⟩ : syracuseStep 19456717 = 7296269) B7296269
theorem B1843927 : Blo 1843623 1843927 := bstep (se 1 (by rfl) ⟨1382945, by rfl⟩ : syracuseStep 1843927 = 2765891) B2765891
theorem B3113687 : Blo 1843623 3113687 := bstep (se 1 (by rfl) ⟨2335265, by rfl⟩ : syracuseStep 3113687 = 4670531) B4670531
theorem B1843947 : Blo 1843623 1843947 := bstep (se 1 (by rfl) ⟨1382960, by rfl⟩ : syracuseStep 1843947 = 2765921) B2765921
theorem B1843959 : Blo 1843623 1843959 := bstep (se 1 (by rfl) ⟨1382969, by rfl⟩ : syracuseStep 1843959 = 2765939) B2765939
theorem B1843979 : Blo 1843623 1843979 := bstep (se 1 (by rfl) ⟨1382984, by rfl⟩ : syracuseStep 1843979 = 2765969) B2765969
theorem B1843991 : Blo 1843623 1843991 := bstep (se 1 (by rfl) ⟨1382993, by rfl⟩ : syracuseStep 1843991 = 2765987) B2765987
theorem B1844011 : Blo 1843623 1844011 := bstep (se 1 (by rfl) ⟨1383008, by rfl⟩ : syracuseStep 1844011 = 2766017) B2766017
theorem B6226739 : Blo 1843623 6226739 := bstep (se 1 (by rfl) ⟨4670054, by rfl⟩ : syracuseStep 6226739 = 9340109) B9340109
theorem B1844023 : Blo 1843623 1844023 := bstep (se 1 (by rfl) ⟨1383017, by rfl⟩ : syracuseStep 1844023 = 2766035) B2766035
theorem B1844043 : Blo 1843623 1844043 := bstep (se 1 (by rfl) ⟨1383032, by rfl⟩ : syracuseStep 1844043 = 2766065) B2766065
theorem B1844055 : Blo 1843623 1844055 := bstep (se 1 (by rfl) ⟨1383041, by rfl⟩ : syracuseStep 1844055 = 2766083) B2766083
theorem B3113815 : Blo 1843623 3113815 := bstep (se 1 (by rfl) ⟨2335361, by rfl⟩ : syracuseStep 3113815 = 4670723) B4670723
theorem B1844075 : Blo 1843623 1844075 := bstep (se 1 (by rfl) ⟨1383056, by rfl⟩ : syracuseStep 1844075 = 2766113) B2766113
theorem B1844087 : Blo 1843623 1844087 := bstep (se 1 (by rfl) ⟨1383065, by rfl⟩ : syracuseStep 1844087 = 2766131) B2766131
theorem B1844107 : Blo 1843623 1844107 := bstep (se 1 (by rfl) ⟨1383080, by rfl⟩ : syracuseStep 1844107 = 2766161) B2766161
theorem B1844119 : Blo 1843623 1844119 := bstep (se 1 (by rfl) ⟨1383089, by rfl⟩ : syracuseStep 1844119 = 2766179) B2766179
theorem B1844139 : Blo 1843623 1844139 := bstep (se 1 (by rfl) ⟨1383104, by rfl⟩ : syracuseStep 1844139 = 2766209) B2766209
theorem B1844151 : Blo 1843623 1844151 := bstep (se 1 (by rfl) ⟨1383113, by rfl⟩ : syracuseStep 1844151 = 2766227) B2766227
theorem B1844171 : Blo 1843623 1844171 := bstep (se 1 (by rfl) ⟨1383128, by rfl⟩ : syracuseStep 1844171 = 2766257) B2766257
theorem B1844183 : Blo 1843623 1844183 := bstep (se 1 (by rfl) ⟨1383137, by rfl⟩ : syracuseStep 1844183 = 2766275) B2766275
theorem B1844203 : Blo 1843623 1844203 := bstep (se 1 (by rfl) ⟨1383152, by rfl⟩ : syracuseStep 1844203 = 2766305) B2766305
theorem B1844215 : Blo 1843623 1844215 := bstep (se 1 (by rfl) ⟨1383161, by rfl⟩ : syracuseStep 1844215 = 2766323) B2766323
theorem B1844235 : Blo 1843623 1844235 := bstep (se 1 (by rfl) ⟨1383176, by rfl⟩ : syracuseStep 1844235 = 2766353) B2766353
theorem B1844247 : Blo 1843623 1844247 := bstep (se 1 (by rfl) ⟨1383185, by rfl⟩ : syracuseStep 1844247 = 2766371) B2766371
theorem B1868843 : Blo 1843623 1868843 := bstep (se 1 (by rfl) ⟨1401632, by rfl⟩ : syracuseStep 1868843 = 2803265) B2803265
theorem B1844267 : Blo 1843623 1844267 := bstep (se 1 (by rfl) ⟨1383200, by rfl⟩ : syracuseStep 1844267 = 2766401) B2766401
theorem B1844279 : Blo 1843623 1844279 := bstep (se 1 (by rfl) ⟨1383209, by rfl⟩ : syracuseStep 1844279 = 2766419) B2766419
theorem B6644801 : Blo 1843623 6644801 := bstep (se 2 (by rfl) ⟨2491800, by rfl⟩ : syracuseStep 6644801 = 4983601) B4983601
theorem B5252161 : Blo 1843623 5252161 := bstep (se 2 (by rfl) ⟨1969560, by rfl⟩ : syracuseStep 5252161 = 3939121) B3939121
theorem B6227009 : Blo 1843623 6227009 := bstep (se 2 (by rfl) ⟨2335128, by rfl⟩ : syracuseStep 6227009 = 4670257) B4670257
theorem B1844299 : Blo 1843623 1844299 := bstep (se 1 (by rfl) ⟨1383224, by rfl⟩ : syracuseStep 1844299 = 2766449) B2766449
theorem B1844311 : Blo 1843623 1844311 := bstep (se 1 (by rfl) ⟨1383233, by rfl⟩ : syracuseStep 1844311 = 2766467) B2766467
theorem B21005405 : Blo 1843623 21005405 := bstep (se 3 (by rfl) ⟨3938513, by rfl⟩ : syracuseStep 21005405 = 7877027) B7877027
theorem B1844331 : Blo 1843623 1844331 := bstep (se 1 (by rfl) ⟨1383248, by rfl⟩ : syracuseStep 1844331 = 2766497) B2766497
theorem B1844343 : Blo 1843623 1844343 := bstep (se 1 (by rfl) ⟨1383257, by rfl⟩ : syracuseStep 1844343 = 2766515) B2766515
theorem B1844363 : Blo 1843623 1844363 := bstep (se 1 (by rfl) ⟨1383272, by rfl⟩ : syracuseStep 1844363 = 2766545) B2766545
theorem B1844375 : Blo 1843623 1844375 := bstep (se 1 (by rfl) ⟨1383281, by rfl⟩ : syracuseStep 1844375 = 2766563) B2766563
theorem B1844395 : Blo 1843623 1844395 := bstep (se 1 (by rfl) ⟨1383296, by rfl⟩ : syracuseStep 1844395 = 2766593) B2766593
theorem B1844407 : Blo 1843623 1844407 := bstep (se 1 (by rfl) ⟨1383305, by rfl⟩ : syracuseStep 1844407 = 2766611) B2766611
theorem B1844427 : Blo 1843623 1844427 := bstep (se 1 (by rfl) ⟨1383320, by rfl⟩ : syracuseStep 1844427 = 2766641) B2766641
theorem B1844439 : Blo 1843623 1844439 := bstep (se 1 (by rfl) ⟨1383329, by rfl⟩ : syracuseStep 1844439 = 2766659) B2766659
theorem B1844459 : Blo 1843623 1844459 := bstep (se 1 (by rfl) ⟨1383344, by rfl⟩ : syracuseStep 1844459 = 2766689) B2766689
theorem B1844471 : Blo 1843623 1844471 := bstep (se 1 (by rfl) ⟨1383353, by rfl⟩ : syracuseStep 1844471 = 2766707) B2766707
theorem B1844491 : Blo 1843623 1844491 := bstep (se 1 (by rfl) ⟨1383368, by rfl⟩ : syracuseStep 1844491 = 2766737) B2766737
theorem B1844503 : Blo 1843623 1844503 := bstep (se 1 (by rfl) ⟨1383377, by rfl⟩ : syracuseStep 1844503 = 2766755) B2766755
theorem B4670743 : Blo 1843623 4670743 := bstep (se 1 (by rfl) ⟨3503057, by rfl⟩ : syracuseStep 4670743 = 7006115) B7006115
theorem B1844523 : Blo 1843623 1844523 := bstep (se 1 (by rfl) ⟨1383392, by rfl⟩ : syracuseStep 1844523 = 2766785) B2766785
theorem B1844535 : Blo 1843623 1844535 := bstep (se 1 (by rfl) ⟨1383401, by rfl⟩ : syracuseStep 1844535 = 2766803) B2766803
theorem B1844555 : Blo 1843623 1844555 := bstep (se 1 (by rfl) ⟨1383416, by rfl⟩ : syracuseStep 1844555 = 2766833) B2766833
theorem B1844567 : Blo 1843623 1844567 := bstep (se 1 (by rfl) ⟨1383425, by rfl⟩ : syracuseStep 1844567 = 2766851) B2766851
theorem B1844587 : Blo 1843623 1844587 := bstep (se 1 (by rfl) ⟨1383440, by rfl⟩ : syracuseStep 1844587 = 2766881) B2766881
theorem B1844599 : Blo 1843623 1844599 := bstep (se 1 (by rfl) ⟨1383449, by rfl⟩ : syracuseStep 1844599 = 2766899) B2766899
theorem B1844619 : Blo 1843623 1844619 := bstep (se 1 (by rfl) ⟨1383464, by rfl⟩ : syracuseStep 1844619 = 2766929) B2766929
theorem B1844631 : Blo 1843623 1844631 := bstep (se 1 (by rfl) ⟨1383473, by rfl⟩ : syracuseStep 1844631 = 2766947) B2766947
theorem B1844651 : Blo 1843623 1844651 := bstep (se 1 (by rfl) ⟨1383488, by rfl⟩ : syracuseStep 1844651 = 2766977) B2766977
theorem B1844663 : Blo 1843623 1844663 := bstep (se 1 (by rfl) ⟨1383497, by rfl⟩ : syracuseStep 1844663 = 2766995) B2766995
theorem B1844683 : Blo 1843623 1844683 := bstep (se 1 (by rfl) ⟨1383512, by rfl⟩ : syracuseStep 1844683 = 2767025) B2767025
theorem B3114443 : Blo 1843623 3114443 := bstep (se 1 (by rfl) ⟨2335832, by rfl⟩ : syracuseStep 3114443 = 4671665) B4671665
theorem B1844695 : Blo 1843623 1844695 := bstep (se 1 (by rfl) ⟨1383521, by rfl⟩ : syracuseStep 1844695 = 2767043) B2767043
theorem B1844715 : Blo 1843623 1844715 := bstep (se 1 (by rfl) ⟨1383536, by rfl⟩ : syracuseStep 1844715 = 2767073) B2767073
theorem B1844727 : Blo 1843623 1844727 := bstep (se 1 (by rfl) ⟨1383545, by rfl⟩ : syracuseStep 1844727 = 2767091) B2767091
theorem B1844747 : Blo 1843623 1844747 := bstep (se 1 (by rfl) ⟨1383560, by rfl⟩ : syracuseStep 1844747 = 2767121) B2767121
theorem B9340433 : Blo 1843623 9340433 := bstep (se 2 (by rfl) ⟨3502662, by rfl⟩ : syracuseStep 9340433 = 7005325) B7005325
theorem B2074135 : Blo 1843623 2074135 := bstep (se 1 (by rfl) ⟨1555601, by rfl⟩ : syracuseStep 2074135 = 3111203) B3111203
theorem B1844759 : Blo 1843623 1844759 := bstep (se 1 (by rfl) ⟨1383569, by rfl⟩ : syracuseStep 1844759 = 2767139) B2767139
theorem B1844779 : Blo 1843623 1844779 := bstep (se 1 (by rfl) ⟨1383584, by rfl⟩ : syracuseStep 1844779 = 2767169) B2767169
theorem B6309427 : Blo 1843623 6309427 := bstep (se 1 (by rfl) ⟨4732070, by rfl⟩ : syracuseStep 6309427 = 9464141) B9464141
theorem B1844791 : Blo 1843623 1844791 := bstep (se 1 (by rfl) ⟨1383593, by rfl⟩ : syracuseStep 1844791 = 2767187) B2767187
theorem B14009921 : Blo 1843623 14009921 := bstep (se 2 (by rfl) ⟨5253720, by rfl⟩ : syracuseStep 14009921 = 10507441) B10507441
theorem B1844811 : Blo 1843623 1844811 := bstep (se 1 (by rfl) ⟨1383608, by rfl⟩ : syracuseStep 1844811 = 2767217) B2767217
theorem B1844823 : Blo 1843623 1844823 := bstep (se 1 (by rfl) ⟨1383617, by rfl⟩ : syracuseStep 1844823 = 2767235) B2767235
theorem B6227549 : Blo 1843623 6227549 := bstep (se 3 (by rfl) ⟨1167665, by rfl⟩ : syracuseStep 6227549 = 2335331) B2335331
theorem B11216485 : Blo 1843623 11216485 := bstep (se 4 (by rfl) ⟨1051545, by rfl⟩ : syracuseStep 11216485 = 2103091) B2103091
theorem B1844843 : Blo 1843623 1844843 := bstep (se 1 (by rfl) ⟨1383632, by rfl⟩ : syracuseStep 1844843 = 2767265) B2767265
theorem B1844855 : Blo 1843623 1844855 := bstep (se 1 (by rfl) ⟨1383641, by rfl⟩ : syracuseStep 1844855 = 2767283) B2767283
theorem B201942659 : Blo 1843623 201942659 := bstep (se 1 (by rfl) ⟨151456994, by rfl⟩ : syracuseStep 201942659 = 302913989) B302913989
theorem B1844875 : Blo 1843623 1844875 := bstep (se 1 (by rfl) ⟨1383656, by rfl⟩ : syracuseStep 1844875 = 2767313) B2767313
theorem B1844887 : Blo 1843623 1844887 := bstep (se 1 (by rfl) ⟨1383665, by rfl⟩ : syracuseStep 1844887 = 2767331) B2767331
theorem B1844907 : Blo 1843623 1844907 := bstep (se 1 (by rfl) ⟨1383680, by rfl⟩ : syracuseStep 1844907 = 2767361) B2767361
theorem B9340595 : Blo 1843623 9340595 := bstep (se 1 (by rfl) ⟨7005446, by rfl⟩ : syracuseStep 9340595 = 14010893) B14010893
theorem B1844919 : Blo 1843623 1844919 := bstep (se 1 (by rfl) ⟨1383689, by rfl⟩ : syracuseStep 1844919 = 2767379) B2767379
theorem B2074315 : Blo 1843623 2074315 := bstep (se 1 (by rfl) ⟨1555736, by rfl⟩ : syracuseStep 2074315 = 3111473) B3111473
theorem B1844939 : Blo 1843623 1844939 := bstep (se 1 (by rfl) ⟨1383704, by rfl⟩ : syracuseStep 1844939 = 2767409) B2767409
theorem B4671179 : Blo 1843623 4671179 := bstep (se 1 (by rfl) ⟨3503384, by rfl⟩ : syracuseStep 4671179 = 7006769) B7006769
theorem B1844951 : Blo 1843623 1844951 := bstep (se 1 (by rfl) ⟨1383713, by rfl⟩ : syracuseStep 1844951 = 2767427) B2767427
theorem B1844971 : Blo 1843623 1844971 := bstep (se 1 (by rfl) ⟨1383728, by rfl⟩ : syracuseStep 1844971 = 2767457) B2767457
theorem B1844983 : Blo 1843623 1844983 := bstep (se 1 (by rfl) ⟨1383737, by rfl⟩ : syracuseStep 1844983 = 2767475) B2767475
theorem B1845003 : Blo 1843623 1845003 := bstep (se 1 (by rfl) ⟨1383752, by rfl⟩ : syracuseStep 1845003 = 2767505) B2767505
theorem B1845015 : Blo 1843623 1845015 := bstep (se 1 (by rfl) ⟨1383761, by rfl⟩ : syracuseStep 1845015 = 2767523) B2767523
theorem B1845035 : Blo 1843623 1845035 := bstep (se 1 (by rfl) ⟨1383776, by rfl⟩ : syracuseStep 1845035 = 2767553) B2767553
theorem B2074423 : Blo 1843623 2074423 := bstep (se 1 (by rfl) ⟨1555817, by rfl⟩ : syracuseStep 2074423 = 3111635) B3111635
theorem B1845047 : Blo 1843623 1845047 := bstep (se 1 (by rfl) ⟨1383785, by rfl⟩ : syracuseStep 1845047 = 2767571) B2767571
theorem B1845067 : Blo 1843623 1845067 := bstep (se 1 (by rfl) ⟨1383800, by rfl⟩ : syracuseStep 1845067 = 2767601) B2767601
theorem B1845079 : Blo 1843623 1845079 := bstep (se 1 (by rfl) ⟨1383809, by rfl⟩ : syracuseStep 1845079 = 2767619) B2767619
theorem B17065829 : Blo 1843623 17065829 := bstep (se 4 (by rfl) ⟨1599921, by rfl⟩ : syracuseStep 17065829 = 3199843) B3199843
theorem B1845099 : Blo 1843623 1845099 := bstep (se 1 (by rfl) ⟨1383824, by rfl⟩ : syracuseStep 1845099 = 2767649) B2767649
theorem B1845111 : Blo 1843623 1845111 := bstep (se 1 (by rfl) ⟨1383833, by rfl⟩ : syracuseStep 1845111 = 2767667) B2767667
theorem B1845131 : Blo 1843623 1845131 := bstep (se 1 (by rfl) ⟨1383848, by rfl⟩ : syracuseStep 1845131 = 2767697) B2767697
theorem B1845143 : Blo 1843623 1845143 := bstep (se 1 (by rfl) ⟨1383857, by rfl⟩ : syracuseStep 1845143 = 2767715) B2767715
theorem B1845163 : Blo 1843623 1845163 := bstep (se 1 (by rfl) ⟨1383872, by rfl⟩ : syracuseStep 1845163 = 2767745) B2767745
theorem B1869751 : Blo 1843623 1869751 := bstep (se 1 (by rfl) ⟨1402313, by rfl⟩ : syracuseStep 1869751 = 2804627) B2804627
theorem B1845175 : Blo 1843623 1845175 := bstep (se 1 (by rfl) ⟨1383881, by rfl⟩ : syracuseStep 1845175 = 2767763) B2767763
theorem B1845195 : Blo 1843623 1845195 := bstep (se 1 (by rfl) ⟨1383896, by rfl⟩ : syracuseStep 1845195 = 2767793) B2767793
theorem B1845207 : Blo 1843623 1845207 := bstep (se 1 (by rfl) ⟨1383905, by rfl⟩ : syracuseStep 1845207 = 2767811) B2767811
theorem B2074603 : Blo 1843623 2074603 := bstep (se 1 (by rfl) ⟨1555952, by rfl⟩ : syracuseStep 2074603 = 3111905) B3111905
theorem B1845227 : Blo 1843623 1845227 := bstep (se 1 (by rfl) ⟨1383920, by rfl⟩ : syracuseStep 1845227 = 2767841) B2767841
theorem B1845239 : Blo 1843623 1845239 := bstep (se 1 (by rfl) ⟨1383929, by rfl⟩ : syracuseStep 1845239 = 2767859) B2767859
theorem B1845259 : Blo 1843623 1845259 := bstep (se 1 (by rfl) ⟨1383944, by rfl⟩ : syracuseStep 1845259 = 2767889) B2767889
theorem B1845271 : Blo 1843623 1845271 := bstep (se 1 (by rfl) ⟨1383953, by rfl⟩ : syracuseStep 1845271 = 2767907) B2767907
theorem B1845291 : Blo 1843623 1845291 := bstep (se 1 (by rfl) ⟨1383968, by rfl⟩ : syracuseStep 1845291 = 2767937) B2767937
theorem B1845303 : Blo 1843623 1845303 := bstep (se 1 (by rfl) ⟨1383977, by rfl⟩ : syracuseStep 1845303 = 2767955) B2767955
theorem B4671553 : Blo 1843623 4671553 := bstep (se 2 (by rfl) ⟨1751832, by rfl⟩ : syracuseStep 4671553 = 3503665) B3503665
theorem B7006283 : Blo 1843623 7006283 := bstep (se 1 (by rfl) ⟨5254712, by rfl⟩ : syracuseStep 7006283 = 10509425) B10509425
theorem B1845323 : Blo 1843623 1845323 := bstep (se 1 (by rfl) ⟨1383992, by rfl⟩ : syracuseStep 1845323 = 2767985) B2767985
theorem B2074711 : Blo 1843623 2074711 := bstep (se 1 (by rfl) ⟨1556033, by rfl⟩ : syracuseStep 2074711 = 3112067) B3112067
theorem B1845335 : Blo 1843623 1845335 := bstep (se 1 (by rfl) ⟨1384001, by rfl⟩ : syracuseStep 1845335 = 2768003) B2768003
theorem B7006297 : Blo 1843623 7006297 := bstep (se 2 (by rfl) ⟨2627361, by rfl⟩ : syracuseStep 7006297 = 5254723) B5254723
theorem B1845355 : Blo 1843623 1845355 := bstep (se 1 (by rfl) ⟨1384016, by rfl⟩ : syracuseStep 1845355 = 2768033) B2768033
theorem B1845367 : Blo 1843623 1845367 := bstep (se 1 (by rfl) ⟨1384025, by rfl⟩ : syracuseStep 1845367 = 2768051) B2768051
theorem B1845387 : Blo 1843623 1845387 := bstep (se 1 (by rfl) ⟨1384040, by rfl⟩ : syracuseStep 1845387 = 2768081) B2768081
theorem B10504343 : Blo 1843623 10504343 := bstep (se 1 (by rfl) ⟨7878257, by rfl⟩ : syracuseStep 10504343 = 15756515) B15756515
theorem B1845399 : Blo 1843623 1845399 := bstep (se 1 (by rfl) ⟨1384049, by rfl⟩ : syracuseStep 1845399 = 2768099) B2768099
theorem B1845419 : Blo 1843623 1845419 := bstep (se 1 (by rfl) ⟨1384064, by rfl⟩ : syracuseStep 1845419 = 2768129) B2768129
theorem B1845431 : Blo 1843623 1845431 := bstep (se 1 (by rfl) ⟨1384073, by rfl⟩ : syracuseStep 1845431 = 2768147) B2768147
theorem B1845451 : Blo 1843623 1845451 := bstep (se 1 (by rfl) ⟨1384088, by rfl⟩ : syracuseStep 1845451 = 2768177) B2768177
theorem B1845463 : Blo 1843623 1845463 := bstep (se 1 (by rfl) ⟨1384097, by rfl⟩ : syracuseStep 1845463 = 2768195) B2768195
theorem B1845483 : Blo 1843623 1845483 := bstep (se 1 (by rfl) ⟨1384112, by rfl⟩ : syracuseStep 1845483 = 2768225) B2768225
theorem B1845495 : Blo 1843623 1845495 := bstep (se 1 (by rfl) ⟨1384121, by rfl⟩ : syracuseStep 1845495 = 2768243) B2768243
theorem B2074891 : Blo 1843623 2074891 := bstep (se 1 (by rfl) ⟨1556168, by rfl⟩ : syracuseStep 2074891 = 3112337) B3112337
theorem B1845515 : Blo 1843623 1845515 := bstep (se 1 (by rfl) ⟨1384136, by rfl⟩ : syracuseStep 1845515 = 2768273) B2768273
theorem B1845527 : Blo 1843623 1845527 := bstep (se 1 (by rfl) ⟨1384145, by rfl⟩ : syracuseStep 1845527 = 2768291) B2768291
theorem B1845547 : Blo 1843623 1845547 := bstep (se 1 (by rfl) ⟨1384160, by rfl⟩ : syracuseStep 1845547 = 2768321) B2768321
theorem B12798253 : Blo 1843623 12798253 := bstep (se 3 (by rfl) ⟨2399672, by rfl⟩ : syracuseStep 12798253 = 4799345) B4799345
theorem B1845559 : Blo 1843623 1845559 := bstep (se 1 (by rfl) ⟨1384169, by rfl⟩ : syracuseStep 1845559 = 2768339) B2768339
theorem B1845579 : Blo 1843623 1845579 := bstep (se 1 (by rfl) ⟨1384184, by rfl⟩ : syracuseStep 1845579 = 2768369) B2768369
theorem B1845591 : Blo 1843623 1845591 := bstep (se 1 (by rfl) ⟨1384193, by rfl⟩ : syracuseStep 1845591 = 2768387) B2768387
theorem B1845611 : Blo 1843623 1845611 := bstep (se 1 (by rfl) ⟨1384208, by rfl⟩ : syracuseStep 1845611 = 2768417) B2768417
theorem B63883637 : Blo 1843623 63883637 := bstep (se 5 (by rfl) ⟨2994545, by rfl⟩ : syracuseStep 63883637 = 5989091) B5989091
theorem B2074999 : Blo 1843623 2074999 := bstep (se 1 (by rfl) ⟨1556249, by rfl⟩ : syracuseStep 2074999 = 3112499) B3112499
theorem B1845623 : Blo 1843623 1845623 := bstep (se 1 (by rfl) ⟨1384217, by rfl⟩ : syracuseStep 1845623 = 2768435) B2768435
theorem B8415667 : Blo 1843623 8415667 := bstep (se 1 (by rfl) ⟨6311750, by rfl⟩ : syracuseStep 8415667 = 12623501) B12623501
theorem B3500491 : Blo 1843623 3500491 := bstep (se 1 (by rfl) ⟨2625368, by rfl⟩ : syracuseStep 3500491 = 5250737) B5250737
theorem B1870327 : Blo 1843623 1870327 := bstep (se 1 (by rfl) ⟨1402745, by rfl⟩ : syracuseStep 1870327 = 2805491) B2805491
theorem B3500567 : Blo 1843623 3500567 := bstep (se 1 (by rfl) ⟨2625425, by rfl⟩ : syracuseStep 3500567 = 5250851) B5250851
theorem B2075179 : Blo 1843623 2075179 := bstep (se 1 (by rfl) ⟨1556384, by rfl⟩ : syracuseStep 2075179 = 3112769) B3112769
theorem B7883315 : Blo 1843623 7883315 := bstep (se 1 (by rfl) ⟨5912486, by rfl⟩ : syracuseStep 7883315 = 11824973) B11824973
theorem B13298251 : Blo 1843623 13298251 := bstep (se 1 (by rfl) ⟨9973688, by rfl⟩ : syracuseStep 13298251 = 19947377) B19947377
theorem B10644061 : Blo 1843623 10644061 := bstep (se 3 (by rfl) ⟨1995761, by rfl⟩ : syracuseStep 10644061 = 3991523) B3991523
theorem B2075287 : Blo 1843623 2075287 := bstep (se 1 (by rfl) ⟨1556465, by rfl⟩ : syracuseStep 2075287 = 3112931) B3112931
theorem B7875251 : Blo 1843623 7875251 := bstep (se 1 (by rfl) ⟨5906438, by rfl⟩ : syracuseStep 7875251 = 11812877) B11812877
theorem B5253835 : Blo 1843623 5253835 := bstep (se 1 (by rfl) ⟨3940376, by rfl⟩ : syracuseStep 5253835 = 7880753) B7880753
theorem B6228683 : Blo 1843623 6228683 := bstep (se 1 (by rfl) ⟨4671512, by rfl⟩ : syracuseStep 6228683 = 9343025) B9343025
theorem B8866577 : Blo 1843623 8866577 := bstep (se 2 (by rfl) ⟨3324966, by rfl⟩ : syracuseStep 8866577 = 6649933) B6649933
theorem B2075467 : Blo 1843623 2075467 := bstep (se 1 (by rfl) ⟨1556600, by rfl⟩ : syracuseStep 2075467 = 3113201) B3113201
theorem B2075575 : Blo 1843623 2075575 := bstep (se 1 (by rfl) ⟨1556681, by rfl⟩ : syracuseStep 2075575 = 3113363) B3113363
theorem B4148171 : Blo 1843623 4148171 := bstep (se 1 (by rfl) ⟨3111128, by rfl⟩ : syracuseStep 4148171 = 6222257) B6222257
theorem B10652633 : Blo 1843623 10652633 := bstep (se 2 (by rfl) ⟨3994737, by rfl⟩ : syracuseStep 10652633 = 7989475) B7989475
theorem B6228953 : Blo 1843623 6228953 := bstep (se 2 (by rfl) ⟨2335857, by rfl⟩ : syracuseStep 6228953 = 4671715) B4671715
theorem B5254109 : Blo 1843623 5254109 := bstep (se 3 (by rfl) ⟨985145, by rfl⟩ : syracuseStep 5254109 = 1970291) B1970291
theorem B4148225 : Blo 1843623 4148225 := bstep (se 2 (by rfl) ⟨1555584, by rfl⟩ : syracuseStep 4148225 = 3111169) B3111169
theorem B7007255 : Blo 1843623 7007255 := bstep (se 1 (by rfl) ⟨5255441, by rfl⟩ : syracuseStep 7007255 = 10510883) B10510883
theorem B2075755 : Blo 1843623 2075755 := bstep (se 1 (by rfl) ⟨1556816, by rfl⟩ : syracuseStep 2075755 = 3113633) B3113633
theorem B1969291 : Blo 1843623 1969291 := bstep (se 1 (by rfl) ⟨1476968, by rfl⟩ : syracuseStep 1969291 = 2953937) B2953937
theorem B3501235 : Blo 1843623 3501235 := bstep (se 1 (by rfl) ⟨2625926, by rfl⟩ : syracuseStep 3501235 = 5251853) B5251853
theorem B2075863 : Blo 1843623 2075863 := bstep (se 1 (by rfl) ⟨1556897, by rfl⟩ : syracuseStep 2075863 = 3113795) B3113795
theorem B4148441 : Blo 1843623 4148441 := bstep (se 2 (by rfl) ⟨1555665, by rfl⟩ : syracuseStep 4148441 = 3111331) B3111331
theorem B4148531 : Blo 1843623 4148531 := bstep (se 1 (by rfl) ⟨3111398, by rfl⟩ : syracuseStep 4148531 = 6222797) B6222797
theorem B4148567 : Blo 1843623 4148567 := bstep (se 1 (by rfl) ⟨3111425, by rfl⟩ : syracuseStep 4148567 = 6222851) B6222851
theorem B2076043 : Blo 1843623 2076043 := bstep (se 1 (by rfl) ⟨1557032, by rfl⟩ : syracuseStep 2076043 = 3114065) B3114065
theorem B3739031 : Blo 1843623 3739031 := bstep (se 1 (by rfl) ⟨2804273, by rfl⟩ : syracuseStep 3739031 = 5608547) B5608547
theorem B3501463 : Blo 1843623 3501463 := bstep (se 1 (by rfl) ⟨2626097, by rfl⟩ : syracuseStep 3501463 = 5252195) B5252195
theorem B3993047 : Blo 1843623 3993047 := bstep (se 1 (by rfl) ⟨2994785, by rfl⟩ : syracuseStep 3993047 = 5989571) B5989571
theorem B14011865 : Blo 1843623 14011865 := bstep (se 2 (by rfl) ⟨5254449, by rfl⟩ : syracuseStep 14011865 = 10508899) B10508899
theorem B2076151 : Blo 1843623 2076151 := bstep (se 1 (by rfl) ⟨1557113, by rfl⟩ : syracuseStep 2076151 = 3114227) B3114227
theorem B3501569 : Blo 1843623 3501569 := bstep (se 2 (by rfl) ⟨1313088, by rfl⟩ : syracuseStep 3501569 = 2626177) B2626177
theorem B4148747 : Blo 1843623 4148747 := bstep (se 1 (by rfl) ⟨3111560, by rfl⟩ : syracuseStep 4148747 = 6223121) B6223121
theorem B59846161 : Blo 1843623 59846161 := bstep (se 2 (by rfl) ⟨22442310, by rfl⟩ : syracuseStep 59846161 = 44884621) B44884621
theorem B4148801 : Blo 1843623 4148801 := bstep (se 2 (by rfl) ⟨1555800, by rfl⟩ : syracuseStep 4148801 = 3111601) B3111601
theorem B26594891 : Blo 1843623 26594891 := bstep (se 1 (by rfl) ⟨19946168, by rfl⟩ : syracuseStep 26594891 = 39892337) B39892337
theorem B9342539 : Blo 1843623 9342539 := bstep (se 1 (by rfl) ⟨7006904, by rfl⟩ : syracuseStep 9342539 = 14013809) B14013809
theorem B2494039 : Blo 1843623 2494039 := bstep (se 1 (by rfl) ⟨1870529, by rfl⟩ : syracuseStep 2494039 = 3741059) B3741059
theorem B3501721 : Blo 1843623 3501721 := bstep (se 2 (by rfl) ⟨1313145, by rfl⟩ : syracuseStep 3501721 = 2626291) B2626291
theorem B4149017 : Blo 1843623 4149017 := bstep (se 2 (by rfl) ⟨1555881, by rfl⟩ : syracuseStep 4149017 = 3111763) B3111763
theorem B4149107 : Blo 1843623 4149107 := bstep (se 1 (by rfl) ⟨3111830, by rfl⟩ : syracuseStep 4149107 = 6223661) B6223661
theorem B1970039 : Blo 1843623 1970039 := bstep (se 1 (by rfl) ⟨1477529, by rfl⟩ : syracuseStep 1970039 = 2955059) B2955059
theorem B11825027 : Blo 1843623 11825027 := bstep (se 1 (by rfl) ⟨8868770, by rfl⟩ : syracuseStep 11825027 = 17737541) B17737541
theorem B4149143 : Blo 1843623 4149143 := bstep (se 1 (by rfl) ⟨3111857, by rfl⟩ : syracuseStep 4149143 = 6223715) B6223715
theorem B3551129 : Blo 1843623 3551129 := bstep (se 2 (by rfl) ⟨1331673, by rfl⟩ : syracuseStep 3551129 = 2663347) B2663347
theorem B10506257 : Blo 1843623 10506257 := bstep (se 2 (by rfl) ⟨3939846, by rfl⟩ : syracuseStep 10506257 = 7879693) B7879693
theorem B4149323 : Blo 1843623 4149323 := bstep (se 1 (by rfl) ⟨3111992, by rfl⟩ : syracuseStep 4149323 = 6223985) B6223985
theorem B2625625 : Blo 1843623 2625625 := bstep (se 2 (by rfl) ⟨984609, by rfl⟩ : syracuseStep 2625625 = 1969219) B1969219
theorem B3739763 : Blo 1843623 3739763 := bstep (se 1 (by rfl) ⟨2804822, by rfl⟩ : syracuseStep 3739763 = 5609645) B5609645
theorem B4149377 : Blo 1843623 4149377 := bstep (se 2 (by rfl) ⟨1556016, by rfl⟩ : syracuseStep 4149377 = 3112033) B3112033
theorem B5607575 : Blo 1843623 5607575 := bstep (se 1 (by rfl) ⟨4205681, by rfl⟩ : syracuseStep 5607575 = 8411363) B8411363
theorem B2560279 : Blo 1843623 2560279 := bstep (se 1 (by rfl) ⟨1920209, by rfl⟩ : syracuseStep 2560279 = 3840419) B3840419
theorem B14954827 : Blo 1843623 14954827 := bstep (se 1 (by rfl) ⟨11216120, by rfl⟩ : syracuseStep 14954827 = 22432241) B22432241
theorem B4149593 : Blo 1843623 4149593 := bstep (se 2 (by rfl) ⟨1556097, by rfl⟩ : syracuseStep 4149593 = 3112195) B3112195
theorem B7000451 : Blo 1843623 7000451 := bstep (se 1 (by rfl) ⟨5250338, by rfl⟩ : syracuseStep 7000451 = 10500677) B10500677
theorem B7000465 : Blo 1843623 7000465 := bstep (se 2 (by rfl) ⟨2625174, by rfl⟩ : syracuseStep 7000465 = 5250349) B5250349
theorem B7098797 : Blo 1843623 7098797 := bstep (se 3 (by rfl) ⟨1331024, by rfl⟩ : syracuseStep 7098797 = 2662049) B2662049
theorem B4149683 : Blo 1843623 4149683 := bstep (se 1 (by rfl) ⟨3112262, by rfl⟩ : syracuseStep 4149683 = 6224525) B6224525
theorem B2953675 : Blo 1843623 2953675 := bstep (se 1 (by rfl) ⟨2215256, by rfl⟩ : syracuseStep 2953675 = 4430513) B4430513
theorem B4149719 : Blo 1843623 4149719 := bstep (se 1 (by rfl) ⟨3112289, by rfl⟩ : syracuseStep 4149719 = 6224579) B6224579
theorem B5911001 : Blo 1843623 5911001 := bstep (se 2 (by rfl) ⟨2216625, by rfl⟩ : syracuseStep 5911001 = 4433251) B4433251
theorem B7680577 : Blo 1843623 7680577 := bstep (se 2 (by rfl) ⟨2880216, by rfl⟩ : syracuseStep 7680577 = 5760433) B5760433
theorem B14955083 : Blo 1843623 14955083 := bstep (se 1 (by rfl) ⟨11216312, by rfl⟩ : syracuseStep 14955083 = 22432625) B22432625
theorem B4149899 : Blo 1843623 4149899 := bstep (se 1 (by rfl) ⟨3112424, by rfl⟩ : syracuseStep 4149899 = 6224849) B6224849
theorem B2765465 : Blo 1843623 2765465 := bstep (se 2 (by rfl) ⟨1037049, by rfl⟩ : syracuseStep 2765465 = 2074099) B2074099
theorem B7000769 : Blo 1843623 7000769 := bstep (se 2 (by rfl) ⟨2625288, by rfl⟩ : syracuseStep 7000769 = 5250577) B5250577
theorem B4149953 : Blo 1843623 4149953 := bstep (se 2 (by rfl) ⟨1556232, by rfl⟩ : syracuseStep 4149953 = 3112465) B3112465
theorem B2765579 : Blo 1843623 2765579 := bstep (se 1 (by rfl) ⟨2074184, by rfl⟩ : syracuseStep 2765579 = 4148369) B4148369
theorem B2765591 : Blo 1843623 2765591 := bstep (se 1 (by rfl) ⟨2074193, by rfl⟩ : syracuseStep 2765591 = 4148387) B4148387
theorem B3322711 : Blo 1843623 3322711 := bstep (se 1 (by rfl) ⟨2492033, by rfl⟩ : syracuseStep 3322711 = 4984067) B4984067
theorem B2765657 : Blo 1843623 2765657 := bstep (se 2 (by rfl) ⟨1037121, by rfl⟩ : syracuseStep 2765657 = 2074243) B2074243
theorem B6222743 : Blo 1843623 6222743 := bstep (se 1 (by rfl) ⟨4667057, by rfl⟩ : syracuseStep 6222743 = 9334115) B9334115
theorem B4150169 : Blo 1843623 4150169 := bstep (se 2 (by rfl) ⟨1556313, by rfl⟩ : syracuseStep 4150169 = 3112627) B3112627
theorem B44880817 : Blo 1843623 44880817 := bstep (se 2 (by rfl) ⟨16830306, by rfl⟩ : syracuseStep 44880817 = 33660613) B33660613
theorem B3503027 : Blo 1843623 3503027 := bstep (se 1 (by rfl) ⟨2627270, by rfl⟩ : syracuseStep 3503027 = 5254541) B5254541
theorem B2765771 : Blo 1843623 2765771 := bstep (se 1 (by rfl) ⟨2074328, by rfl⟩ : syracuseStep 2765771 = 4148657) B4148657
theorem B2765783 : Blo 1843623 2765783 := bstep (se 1 (by rfl) ⟨2074337, by rfl⟩ : syracuseStep 2765783 = 4148675) B4148675
theorem B2626519 : Blo 1843623 2626519 := bstep (se 1 (by rfl) ⟨1969889, by rfl⟩ : syracuseStep 2626519 = 3939779) B3939779
theorem B4150259 : Blo 1843623 4150259 := bstep (se 1 (by rfl) ⟨3112694, by rfl⟩ : syracuseStep 4150259 = 6225389) B6225389
theorem B11818001 : Blo 1843623 11818001 := bstep (se 2 (by rfl) ⟨4431750, by rfl⟩ : syracuseStep 11818001 = 8863501) B8863501
theorem B4150295 : Blo 1843623 4150295 := bstep (se 1 (by rfl) ⟨3112721, by rfl⟩ : syracuseStep 4150295 = 6225443) B6225443
theorem B2765849 : Blo 1843623 2765849 := bstep (se 2 (by rfl) ⟨1037193, by rfl⟩ : syracuseStep 2765849 = 2074387) B2074387
theorem B3503179 : Blo 1843623 3503179 := bstep (se 1 (by rfl) ⟨2627384, by rfl⟩ : syracuseStep 3503179 = 5254769) B5254769
theorem B6648925 : Blo 1843623 6648925 := bstep (se 3 (by rfl) ⟨1246673, by rfl⟩ : syracuseStep 6648925 = 2493347) B2493347
theorem B7984259 : Blo 1843623 7984259 := bstep (se 1 (by rfl) ⟨5988194, by rfl⟩ : syracuseStep 7984259 = 11976389) B11976389
theorem B2765963 : Blo 1843623 2765963 := bstep (se 1 (by rfl) ⟨2074472, by rfl⟩ : syracuseStep 2765963 = 4148945) B4148945
theorem B2765975 : Blo 1843623 2765975 := bstep (se 1 (by rfl) ⟨2074481, by rfl⟩ : syracuseStep 2765975 = 4148963) B4148963
theorem B4150475 : Blo 1843623 4150475 := bstep (se 1 (by rfl) ⟨3112856, by rfl⟩ : syracuseStep 4150475 = 6225713) B6225713
theorem B2766041 : Blo 1843623 2766041 := bstep (se 2 (by rfl) ⟨1037265, by rfl⟩ : syracuseStep 2766041 = 2074531) B2074531
theorem B4150529 : Blo 1843623 4150529 := bstep (se 2 (by rfl) ⟨1556448, by rfl⟩ : syracuseStep 4150529 = 3112897) B3112897
theorem B2766155 : Blo 1843623 2766155 := bstep (se 1 (by rfl) ⟨2074616, by rfl⟩ : syracuseStep 2766155 = 4149233) B4149233
theorem B2766167 : Blo 1843623 2766167 := bstep (se 1 (by rfl) ⟨2074625, by rfl⟩ : syracuseStep 2766167 = 4149251) B4149251
theorem B7001437 : Blo 1843623 7001437 := bstep (se 3 (by rfl) ⟨1312769, by rfl⟩ : syracuseStep 7001437 = 2625539) B2625539
theorem B7878019 : Blo 1843623 7878019 := bstep (se 1 (by rfl) ⟨5908514, by rfl⟩ : syracuseStep 7878019 = 11817029) B11817029
theorem B12146051 : Blo 1843623 12146051 := bstep (se 1 (by rfl) ⟨9109538, by rfl⟩ : syracuseStep 12146051 = 18219077) B18219077
theorem B2766233 : Blo 1843623 2766233 := bstep (se 2 (by rfl) ⟨1037337, by rfl⟩ : syracuseStep 2766233 = 2074675) B2074675
theorem B3503513 : Blo 1843623 3503513 := bstep (se 2 (by rfl) ⟨1313817, by rfl⟩ : syracuseStep 3503513 = 2627635) B2627635
theorem B6223283 : Blo 1843623 6223283 := bstep (se 1 (by rfl) ⟨4667462, by rfl⟩ : syracuseStep 6223283 = 9334925) B9334925
theorem B17724851 : Blo 1843623 17724851 := bstep (se 1 (by rfl) ⟨13293638, by rfl⟩ : syracuseStep 17724851 = 26587277) B26587277
theorem B4150745 : Blo 1843623 4150745 := bstep (se 2 (by rfl) ⟨1556529, by rfl⟩ : syracuseStep 4150745 = 3113059) B3113059
theorem B2766347 : Blo 1843623 2766347 := bstep (se 1 (by rfl) ⟨2074760, by rfl⟩ : syracuseStep 2766347 = 4149521) B4149521
theorem B2627083 : Blo 1843623 2627083 := bstep (se 1 (by rfl) ⟨1970312, by rfl⟩ : syracuseStep 2627083 = 3940625) B3940625
theorem B2766359 : Blo 1843623 2766359 := bstep (se 1 (by rfl) ⟨2074769, by rfl⟩ : syracuseStep 2766359 = 4149539) B4149539
theorem B4150835 : Blo 1843623 4150835 := bstep (se 1 (by rfl) ⟨3113126, by rfl⟩ : syracuseStep 4150835 = 6226253) B6226253
theorem B4732481 : Blo 1843623 4732481 := bstep (se 2 (by rfl) ⟨1774680, by rfl⟩ : syracuseStep 4732481 = 3549361) B3549361
theorem B5912129 : Blo 1843623 5912129 := bstep (se 2 (by rfl) ⟨2217048, by rfl⟩ : syracuseStep 5912129 = 4434097) B4434097
theorem B4150871 : Blo 1843623 4150871 := bstep (se 1 (by rfl) ⟨3113153, by rfl⟩ : syracuseStep 4150871 = 6226307) B6226307
theorem B2766425 : Blo 1843623 2766425 := bstep (se 2 (by rfl) ⟨1037409, by rfl⟩ : syracuseStep 2766425 = 2074819) B2074819
theorem B8410775 : Blo 1843623 8410775 := bstep (se 1 (by rfl) ⟨6308081, by rfl⟩ : syracuseStep 8410775 = 12616163) B12616163
theorem B23647895 : Blo 1843623 23647895 := bstep (se 1 (by rfl) ⟨17735921, by rfl⟩ : syracuseStep 23647895 = 35471843) B35471843
theorem B6223553 : Blo 1843623 6223553 := bstep (se 2 (by rfl) ⟨2333832, by rfl⟩ : syracuseStep 6223553 = 4667665) B4667665
theorem B2766539 : Blo 1843623 2766539 := bstep (se 1 (by rfl) ⟨2074904, by rfl⟩ : syracuseStep 2766539 = 4149809) B4149809
theorem B2766551 : Blo 1843623 2766551 := bstep (se 1 (by rfl) ⟨2074913, by rfl⟩ : syracuseStep 2766551 = 4149827) B4149827
theorem B5912281 : Blo 1843623 5912281 := bstep (se 2 (by rfl) ⟨2217105, by rfl⟩ : syracuseStep 5912281 = 4434211) B4434211
theorem B4151051 : Blo 1843623 4151051 := bstep (se 1 (by rfl) ⟨3113288, by rfl⟩ : syracuseStep 4151051 = 6226577) B6226577
theorem B14006033 : Blo 1843623 14006033 := bstep (se 2 (by rfl) ⟨5252262, by rfl⟩ : syracuseStep 14006033 = 10504525) B10504525
theorem B4667159 : Blo 1843623 4667159 := bstep (se 1 (by rfl) ⟨3500369, by rfl⟩ : syracuseStep 4667159 = 7000739) B7000739
theorem B2766617 : Blo 1843623 2766617 := bstep (se 2 (by rfl) ⟨1037481, by rfl⟩ : syracuseStep 2766617 = 2074963) B2074963
theorem B4151105 : Blo 1843623 4151105 := bstep (se 2 (by rfl) ⟨1556664, by rfl⟩ : syracuseStep 4151105 = 3113329) B3113329
theorem B13301597 : Blo 1843623 13301597 := bstep (se 3 (by rfl) ⟨2494049, by rfl⟩ : syracuseStep 13301597 = 4988099) B4988099
theorem B9336707 : Blo 1843623 9336707 := bstep (se 1 (by rfl) ⟨7002530, by rfl⟩ : syracuseStep 9336707 = 14005061) B14005061
theorem B2766731 : Blo 1843623 2766731 := bstep (se 1 (by rfl) ⟨2075048, by rfl⟩ : syracuseStep 2766731 = 4150097) B4150097
theorem B2766743 : Blo 1843623 2766743 := bstep (se 1 (by rfl) ⟨2075057, by rfl⟩ : syracuseStep 2766743 = 4150115) B4150115
theorem B2955161 : Blo 1843623 2955161 := bstep (se 2 (by rfl) ⟨1108185, by rfl⟩ : syracuseStep 2955161 = 2216371) B2216371
theorem B100931507 : Blo 1843623 100931507 := bstep (se 1 (by rfl) ⟨75698630, by rfl⟩ : syracuseStep 100931507 = 151397261) B151397261
theorem B2766809 : Blo 1843623 2766809 := bstep (se 2 (by rfl) ⟨1037553, by rfl⟩ : syracuseStep 2766809 = 2075107) B2075107
theorem B4732951 : Blo 1843623 4732951 := bstep (se 1 (by rfl) ⟨3549713, by rfl⟩ : syracuseStep 4732951 = 7099427) B7099427
theorem B3323929 : Blo 1843623 3323929 := bstep (se 2 (by rfl) ⟨1246473, by rfl⟩ : syracuseStep 3323929 = 2492947) B2492947
theorem B4151321 : Blo 1843623 4151321 := bstep (se 2 (by rfl) ⟨1556745, by rfl⟩ : syracuseStep 4151321 = 3113491) B3113491
theorem B2766923 : Blo 1843623 2766923 := bstep (se 1 (by rfl) ⟨2075192, by rfl⟩ : syracuseStep 2766923 = 4150385) B4150385
theorem B2103383 : Blo 1843623 2103383 := bstep (se 1 (by rfl) ⟨1577537, by rfl⟩ : syracuseStep 2103383 = 3155075) B3155075
theorem B2766935 : Blo 1843623 2766935 := bstep (se 1 (by rfl) ⟨2075201, by rfl⟩ : syracuseStep 2766935 = 4150403) B4150403
theorem B4151411 : Blo 1843623 4151411 := bstep (se 1 (by rfl) ⟨3113558, by rfl⟩ : syracuseStep 4151411 = 6227117) B6227117
theorem B4151447 : Blo 1843623 4151447 := bstep (se 1 (by rfl) ⟨3113585, by rfl⟩ : syracuseStep 4151447 = 6227171) B6227171
theorem B2767001 : Blo 1843623 2767001 := bstep (se 2 (by rfl) ⟨1037625, by rfl⟩ : syracuseStep 2767001 = 2075251) B2075251
theorem B3111115 : Blo 1843623 3111115 := bstep (se 1 (by rfl) ⟨2333336, by rfl⟩ : syracuseStep 3111115 = 4666673) B4666673
theorem B6224093 : Blo 1843623 6224093 := bstep (se 3 (by rfl) ⟨1167017, by rfl⟩ : syracuseStep 6224093 = 2334035) B2334035
theorem B2767115 : Blo 1843623 2767115 := bstep (se 1 (by rfl) ⟨2075336, by rfl⟩ : syracuseStep 2767115 = 4150673) B4150673
theorem B2767127 : Blo 1843623 2767127 := bstep (se 1 (by rfl) ⟨2075345, by rfl⟩ : syracuseStep 2767127 = 4150691) B4150691
theorem B4266263 : Blo 1843623 4266263 := bstep (se 1 (by rfl) ⟨3199697, by rfl⟩ : syracuseStep 4266263 = 6399395) B6399395
theorem B2103607 : Blo 1843623 2103607 := bstep (se 1 (by rfl) ⟨1577705, by rfl⟩ : syracuseStep 2103607 = 3155411) B3155411
theorem B7878977 : Blo 1843623 7878977 := bstep (se 2 (by rfl) ⟨2954616, by rfl⟩ : syracuseStep 7878977 = 5909233) B5909233
theorem B4151627 : Blo 1843623 4151627 := bstep (se 1 (by rfl) ⟨3113720, by rfl⟩ : syracuseStep 4151627 = 6227441) B6227441
theorem B3111257 : Blo 1843623 3111257 := bstep (se 2 (by rfl) ⟨1166721, by rfl⟩ : syracuseStep 3111257 = 2333443) B2333443
theorem B2767193 : Blo 1843623 2767193 := bstep (se 2 (by rfl) ⟨1037697, by rfl⟩ : syracuseStep 2767193 = 2075395) B2075395
theorem B4151681 : Blo 1843623 4151681 := bstep (se 2 (by rfl) ⟨1556880, by rfl⟩ : syracuseStep 4151681 = 3113761) B3113761
theorem B8411543 : Blo 1843623 8411543 := bstep (se 1 (by rfl) ⟨6308657, by rfl⟩ : syracuseStep 8411543 = 12617315) B12617315
theorem B4667827 : Blo 1843623 4667827 := bstep (se 1 (by rfl) ⟨3500870, by rfl⟩ : syracuseStep 4667827 = 7001741) B7001741
theorem B3938753 : Blo 1843623 3938753 := bstep (se 2 (by rfl) ⟨1477032, by rfl⟩ : syracuseStep 3938753 = 2954065) B2954065
theorem B2767307 : Blo 1843623 2767307 := bstep (se 1 (by rfl) ⟨2075480, by rfl⟩ : syracuseStep 2767307 = 4150961) B4150961
theorem B2767319 : Blo 1843623 2767319 := bstep (se 1 (by rfl) ⟨2075489, by rfl⟩ : syracuseStep 2767319 = 4150979) B4150979
theorem B3111385 : Blo 1843623 3111385 := bstep (se 2 (by rfl) ⟨1166769, by rfl⟩ : syracuseStep 3111385 = 2333539) B2333539
theorem B2767385 : Blo 1843623 2767385 := bstep (se 2 (by rfl) ⟨1037769, by rfl⟩ : syracuseStep 2767385 = 2075539) B2075539
theorem B4667969 : Blo 1843623 4667969 := bstep (se 2 (by rfl) ⟨1750488, by rfl⟩ : syracuseStep 4667969 = 3500977) B3500977
theorem B7002713 : Blo 1843623 7002713 := bstep (se 2 (by rfl) ⟨2626017, by rfl⟩ : syracuseStep 7002713 = 5252035) B5252035
theorem B4151897 : Blo 1843623 4151897 := bstep (se 2 (by rfl) ⟨1556961, by rfl⟩ : syracuseStep 4151897 = 3113923) B3113923
theorem B2767499 : Blo 1843623 2767499 := bstep (se 1 (by rfl) ⟨2075624, by rfl⟩ : syracuseStep 2767499 = 4151249) B4151249
theorem B2767511 : Blo 1843623 2767511 := bstep (se 1 (by rfl) ⟨2075633, by rfl⟩ : syracuseStep 2767511 = 4151267) B4151267
theorem B4151987 : Blo 1843623 4151987 := bstep (se 1 (by rfl) ⟨3113990, by rfl⟩ : syracuseStep 4151987 = 6227981) B6227981
theorem B2333387 : Blo 1843623 2333387 := bstep (se 1 (by rfl) ⟨1750040, by rfl⟩ : syracuseStep 2333387 = 3500081) B3500081
theorem B4152023 : Blo 1843623 4152023 := bstep (se 1 (by rfl) ⟨3114017, by rfl⟩ : syracuseStep 4152023 = 6228035) B6228035
theorem B2767577 : Blo 1843623 2767577 := bstep (se 2 (by rfl) ⟨1037841, by rfl⟩ : syracuseStep 2767577 = 2075683) B2075683
theorem B2767691 : Blo 1843623 2767691 := bstep (se 1 (by rfl) ⟨2075768, by rfl⟩ : syracuseStep 2767691 = 4151537) B4151537
theorem B2767703 : Blo 1843623 2767703 := bstep (se 1 (by rfl) ⟨2075777, by rfl⟩ : syracuseStep 2767703 = 4151555) B4151555
theorem B4152203 : Blo 1843623 4152203 := bstep (se 1 (by rfl) ⟨3114152, by rfl⟩ : syracuseStep 4152203 = 6228305) B6228305
theorem B2767769 : Blo 1843623 2767769 := bstep (se 2 (by rfl) ⟨1037913, by rfl⟩ : syracuseStep 2767769 = 2075827) B2075827
theorem B4152257 : Blo 1843623 4152257 := bstep (se 2 (by rfl) ⟨1557096, by rfl⟩ : syracuseStep 4152257 = 3114193) B3114193
theorem B15752141 : Blo 1843623 15752141 := bstep (se 3 (by rfl) ⟨2953526, by rfl⟩ : syracuseStep 15752141 = 5907053) B5907053
theorem B2767883 : Blo 1843623 2767883 := bstep (se 1 (by rfl) ⟨2075912, by rfl⟩ : syracuseStep 2767883 = 4151825) B4151825
theorem B3111959 : Blo 1843623 3111959 := bstep (se 1 (by rfl) ⟨2333969, by rfl⟩ : syracuseStep 3111959 = 4667939) B4667939
theorem B2767895 : Blo 1843623 2767895 := bstep (se 1 (by rfl) ⟨2075921, by rfl⟩ : syracuseStep 2767895 = 4151843) B4151843
theorem B42581027 : Blo 1843623 42581027 := bstep (se 1 (by rfl) ⟨31935770, by rfl⟩ : syracuseStep 42581027 = 63871541) B63871541
theorem B2767961 : Blo 1843623 2767961 := bstep (se 2 (by rfl) ⟨1037985, by rfl⟩ : syracuseStep 2767961 = 2075971) B2075971
theorem B4987993 : Blo 1843623 4987993 := bstep (se 2 (by rfl) ⟨1870497, by rfl⟩ : syracuseStep 4987993 = 3740995) B3740995
theorem B3112087 : Blo 1843623 3112087 := bstep (se 1 (by rfl) ⟨2334065, by rfl⟩ : syracuseStep 3112087 = 4668131) B4668131
theorem B4152473 : Blo 1843623 4152473 := bstep (se 2 (by rfl) ⟨1557177, by rfl⟩ : syracuseStep 4152473 = 3114355) B3114355
theorem B2768075 : Blo 1843623 2768075 := bstep (se 1 (by rfl) ⟨2076056, by rfl⟩ : syracuseStep 2768075 = 4152113) B4152113
theorem B2768087 : Blo 1843623 2768087 := bstep (se 1 (by rfl) ⟨2076065, by rfl⟩ : syracuseStep 2768087 = 4152131) B4152131
theorem B4152563 : Blo 1843623 4152563 := bstep (se 1 (by rfl) ⟨3114422, by rfl⟩ : syracuseStep 4152563 = 6228845) B6228845
theorem B16833809 : Blo 1843623 16833809 := bstep (se 2 (by rfl) ⟨6312678, by rfl⟩ : syracuseStep 16833809 = 12625357) B12625357
theorem B3939607 : Blo 1843623 3939607 := bstep (se 1 (by rfl) ⟨2954705, by rfl⟩ : syracuseStep 3939607 = 5909411) B5909411
theorem B2768153 : Blo 1843623 2768153 := bstep (se 2 (by rfl) ⟨1038057, by rfl⟩ : syracuseStep 2768153 = 2076115) B2076115
theorem B4152599 : Blo 1843623 4152599 := bstep (se 1 (by rfl) ⟨3114449, by rfl⟩ : syracuseStep 4152599 = 6228899) B6228899
theorem B6225227 : Blo 1843623 6225227 := bstep (se 1 (by rfl) ⟨4668920, by rfl⟩ : syracuseStep 6225227 = 9337841) B9337841
theorem B3325313 : Blo 1843623 3325313 := bstep (se 2 (by rfl) ⟨1246992, by rfl⟩ : syracuseStep 3325313 = 2493985) B2493985
theorem B2334091 : Blo 1843623 2334091 := bstep (se 1 (by rfl) ⟨1750568, by rfl⟩ : syracuseStep 2334091 = 3501137) B3501137
theorem B2768267 : Blo 1843623 2768267 := bstep (se 1 (by rfl) ⟨2076200, by rfl⟩ : syracuseStep 2768267 = 4152401) B4152401
theorem B2768279 : Blo 1843623 2768279 := bstep (se 1 (by rfl) ⟨2076209, by rfl⟩ : syracuseStep 2768279 = 4152419) B4152419
theorem B5250521 : Blo 1843623 5250521 := bstep (se 2 (by rfl) ⟨1968945, by rfl⟩ : syracuseStep 5250521 = 3937891) B3937891
theorem B2768345 : Blo 1843623 2768345 := bstep (se 2 (by rfl) ⟨1038129, by rfl⟩ : syracuseStep 2768345 = 2076259) B2076259
theorem B6225497 : Blo 1843623 6225497 := bstep (se 2 (by rfl) ⟨2334561, by rfl⟩ : syracuseStep 6225497 = 4669123) B4669123
theorem B2334359 : Blo 1843623 2334359 := bstep (se 1 (by rfl) ⟨1750769, by rfl⟩ : syracuseStep 2334359 = 3501539) B3501539
theorem B3112715 : Blo 1843623 3112715 := bstep (se 1 (by rfl) ⟨2334536, by rfl⟩ : syracuseStep 3112715 = 4669073) B4669073
theorem B4669235 : Blo 1843623 4669235 := bstep (se 1 (by rfl) ⟨3501926, by rfl⟩ : syracuseStep 4669235 = 7003853) B7003853
theorem B3112843 : Blo 1843623 3112843 := bstep (se 1 (by rfl) ⟨2334632, by rfl⟩ : syracuseStep 3112843 = 4669265) B4669265
theorem B7880651 : Blo 1843623 7880651 := bstep (se 1 (by rfl) ⟨5910488, by rfl⟩ : syracuseStep 7880651 = 11820977) B11820977
theorem B7004171 : Blo 1843623 7004171 := bstep (se 1 (by rfl) ⟨5253128, by rfl⟩ : syracuseStep 7004171 = 10506257) B10506257
theorem B4431905 : Blo 1843623 4431905 := bstep (se 2 (by rfl) ⟨1661964, by rfl⟩ : syracuseStep 4431905 = 3323929) B3323929
theorem B31514669 : Blo 1843623 31514669 := bstep (se 3 (by rfl) ⟨5909000, by rfl⟩ : syracuseStep 31514669 = 11818001) B11818001
theorem B4669559 : Blo 1843623 4669559 := bstep (se 1 (by rfl) ⟨3502169, by rfl⟩ : syracuseStep 4669559 = 7004339) B7004339
theorem B17719469 : Blo 1843623 17719469 := bstep (se 3 (by rfl) ⟨3322400, by rfl⟩ : syracuseStep 17719469 = 6644801) B6644801
theorem B9339137 : Blo 1843623 9339137 := bstep (se 2 (by rfl) ⟨3502176, by rfl⟩ : syracuseStep 9339137 = 7004353) B7004353
theorem B3113275 : Blo 1843623 3113275 := bstep (se 1 (by rfl) ⟨2334956, by rfl⟩ : syracuseStep 3113275 = 4669913) B4669913
theorem B3940667 : Blo 1843623 3940667 := bstep (se 1 (by rfl) ⟨2955500, by rfl⟩ : syracuseStep 3940667 = 5911001) B5911001
theorem B9970055 : Blo 1843623 9970055 := bstep (se 1 (by rfl) ⟨7477541, by rfl⟩ : syracuseStep 9970055 = 14955083) B14955083
theorem B19939769 : Blo 1843623 19939769 := bstep (se 2 (by rfl) ⟨7477413, by rfl⟩ : syracuseStep 19939769 = 14954827) B14954827
theorem B6226361 : Blo 1843623 6226361 := bstep (se 2 (by rfl) ⟨2334885, by rfl⟩ : syracuseStep 6226361 = 4669771) B4669771
theorem B1843643 : Blo 1843623 1843643 := bstep (se 1 (by rfl) ⟨1382732, by rfl⟩ : syracuseStep 1843643 = 2765465) B2765465
theorem B3113417 : Blo 1843623 3113417 := bstep (se 2 (by rfl) ⟨1167531, by rfl⟩ : syracuseStep 3113417 = 2335063) B2335063
theorem B1843719 : Blo 1843623 1843719 := bstep (se 1 (by rfl) ⟨1382789, by rfl⟩ : syracuseStep 1843719 = 2765579) B2765579
theorem B1843727 : Blo 1843623 1843727 := bstep (se 1 (by rfl) ⟨1382795, by rfl⟩ : syracuseStep 1843727 = 2765591) B2765591
theorem B1843771 : Blo 1843623 1843771 := bstep (se 1 (by rfl) ⟨1382828, by rfl⟩ : syracuseStep 1843771 = 2765657) B2765657
theorem B1843847 : Blo 1843623 1843847 := bstep (se 1 (by rfl) ⟨1382885, by rfl⟩ : syracuseStep 1843847 = 2765771) B2765771
theorem B1843855 : Blo 1843623 1843855 := bstep (se 1 (by rfl) ⟨1382891, by rfl⟩ : syracuseStep 1843855 = 2765783) B2765783
theorem B1843899 : Blo 1843623 1843899 := bstep (se 1 (by rfl) ⟨1382924, by rfl⟩ : syracuseStep 1843899 = 2765849) B2765849
theorem B10502885 : Blo 1843623 10502885 := bstep (se 4 (by rfl) ⟨984645, by rfl⟩ : syracuseStep 10502885 = 1969291) B1969291
theorem B10240769 : Blo 1843623 10240769 := bstep (se 2 (by rfl) ⟨3840288, by rfl⟩ : syracuseStep 10240769 = 7680577) B7680577
theorem B1843975 : Blo 1843623 1843975 := bstep (se 1 (by rfl) ⟨1382981, by rfl⟩ : syracuseStep 1843975 = 2765963) B2765963
theorem B1843983 : Blo 1843623 1843983 := bstep (se 1 (by rfl) ⟨1382987, by rfl⟩ : syracuseStep 1843983 = 2765975) B2765975
theorem B1844027 : Blo 1843623 1844027 := bstep (se 1 (by rfl) ⟨1383020, by rfl⟩ : syracuseStep 1844027 = 2766041) B2766041
theorem B1844103 : Blo 1843623 1844103 := bstep (se 1 (by rfl) ⟨1383077, by rfl⟩ : syracuseStep 1844103 = 2766155) B2766155
theorem B1844111 : Blo 1843623 1844111 := bstep (se 1 (by rfl) ⟨1383083, by rfl⟩ : syracuseStep 1844111 = 2766167) B2766167
theorem B7005113 : Blo 1843623 7005113 := bstep (se 2 (by rfl) ⟨2626917, by rfl⟩ : syracuseStep 7005113 = 5253835) B5253835
theorem B1844155 : Blo 1843623 1844155 := bstep (se 1 (by rfl) ⟨1383116, by rfl⟩ : syracuseStep 1844155 = 2766233) B2766233
theorem B1844231 : Blo 1843623 1844231 := bstep (se 1 (by rfl) ⟨1383173, by rfl⟩ : syracuseStep 1844231 = 2766347) B2766347
theorem B6226955 : Blo 1843623 6226955 := bstep (se 1 (by rfl) ⟨4670216, by rfl⟩ : syracuseStep 6226955 = 9340433) B9340433
theorem B1844239 : Blo 1843623 1844239 := bstep (se 1 (by rfl) ⟨1383179, by rfl⟩ : syracuseStep 1844239 = 2766359) B2766359
theorem B3154987 : Blo 1843623 3154987 := bstep (se 1 (by rfl) ⟨2366240, by rfl⟩ : syracuseStep 3154987 = 4732481) B4732481
theorem B9339947 : Blo 1843623 9339947 := bstep (se 1 (by rfl) ⟨7004960, by rfl⟩ : syracuseStep 9339947 = 14009921) B14009921
theorem B3941419 : Blo 1843623 3941419 := bstep (se 1 (by rfl) ⟨2956064, by rfl⟩ : syracuseStep 3941419 = 5912129) B5912129
theorem B1844283 : Blo 1843623 1844283 := bstep (se 1 (by rfl) ⟨1383212, by rfl⟩ : syracuseStep 1844283 = 2766425) B2766425
theorem B134628439 : Blo 1843623 134628439 := bstep (se 1 (by rfl) ⟨100971329, by rfl⟩ : syracuseStep 134628439 = 201942659) B201942659
theorem B6227063 : Blo 1843623 6227063 := bstep (se 1 (by rfl) ⟨4670297, by rfl⟩ : syracuseStep 6227063 = 9340595) B9340595
theorem B31532165 : Blo 1843623 31532165 := bstep (se 4 (by rfl) ⟨2956140, by rfl⟩ : syracuseStep 31532165 = 5912281) B5912281
theorem B1844359 : Blo 1843623 1844359 := bstep (se 1 (by rfl) ⟨1383269, by rfl⟩ : syracuseStep 1844359 = 2766539) B2766539
theorem B3114119 : Blo 1843623 3114119 := bstep (se 1 (by rfl) ⟨2335589, by rfl⟩ : syracuseStep 3114119 = 4671179) B4671179
theorem B1844367 : Blo 1843623 1844367 := bstep (se 1 (by rfl) ⟨1383275, by rfl⟩ : syracuseStep 1844367 = 2766551) B2766551
theorem B10503341 : Blo 1843623 10503341 := bstep (se 3 (by rfl) ⟨1969376, by rfl⟩ : syracuseStep 10503341 = 3938753) B3938753
theorem B1844411 : Blo 1843623 1844411 := bstep (se 1 (by rfl) ⟨1383308, by rfl⟩ : syracuseStep 1844411 = 2766617) B2766617
theorem B1844487 : Blo 1843623 1844487 := bstep (se 1 (by rfl) ⟨1383365, by rfl⟩ : syracuseStep 1844487 = 2766731) B2766731
theorem B1844495 : Blo 1843623 1844495 := bstep (se 1 (by rfl) ⟨1383371, by rfl⟩ : syracuseStep 1844495 = 2766743) B2766743
theorem B1844539 : Blo 1843623 1844539 := bstep (se 1 (by rfl) ⟨1383404, by rfl⟩ : syracuseStep 1844539 = 2766809) B2766809
theorem B1844615 : Blo 1843623 1844615 := bstep (se 1 (by rfl) ⟨1383461, by rfl⟩ : syracuseStep 1844615 = 2766923) B2766923
theorem B4670855 : Blo 1843623 4670855 := bstep (se 1 (by rfl) ⟨3503141, by rfl⟩ : syracuseStep 4670855 = 7006283) B7006283
theorem B1844623 : Blo 1843623 1844623 := bstep (se 1 (by rfl) ⟨1383467, by rfl⟩ : syracuseStep 1844623 = 2766935) B2766935
theorem B4670905 : Blo 1843623 4670905 := bstep (se 2 (by rfl) ⟨1751589, by rfl⟩ : syracuseStep 4670905 = 3503179) B3503179
theorem B1844667 : Blo 1843623 1844667 := bstep (se 1 (by rfl) ⟨1383500, by rfl⟩ : syracuseStep 1844667 = 2767001) B2767001
theorem B8865233 : Blo 1843623 8865233 := bstep (se 2 (by rfl) ⟨3324462, by rfl⟩ : syracuseStep 8865233 = 6648925) B6648925
theorem B1844743 : Blo 1843623 1844743 := bstep (se 1 (by rfl) ⟨1383557, by rfl⟩ : syracuseStep 1844743 = 2767115) B2767115
theorem B1844751 : Blo 1843623 1844751 := bstep (se 1 (by rfl) ⟨1383563, by rfl⟩ : syracuseStep 1844751 = 2767127) B2767127
theorem B2844175 : Blo 1843623 2844175 := bstep (se 1 (by rfl) ⟨2133131, by rfl⟩ : syracuseStep 2844175 = 4266263) B4266263
theorem B5252651 : Blo 1843623 5252651 := bstep (se 1 (by rfl) ⟨3939488, by rfl⟩ : syracuseStep 5252651 = 7878977) B7878977
theorem B2074171 : Blo 1843623 2074171 := bstep (se 1 (by rfl) ⟨1555628, by rfl⟩ : syracuseStep 2074171 = 3111257) B3111257
theorem B1844795 : Blo 1843623 1844795 := bstep (se 1 (by rfl) ⟨1383596, by rfl⟩ : syracuseStep 1844795 = 2767193) B2767193
theorem B68257349 : Blo 1843623 68257349 := bstep (se 4 (by rfl) ⟨6399126, by rfl⟩ : syracuseStep 68257349 = 12798253) B12798253
theorem B1844871 : Blo 1843623 1844871 := bstep (se 1 (by rfl) ⟨1383653, by rfl⟩ : syracuseStep 1844871 = 2767307) B2767307
theorem B1844879 : Blo 1843623 1844879 := bstep (se 1 (by rfl) ⟨1383659, by rfl⟩ : syracuseStep 1844879 = 2767319) B2767319
theorem B1844923 : Blo 1843623 1844923 := bstep (se 1 (by rfl) ⟨1383692, by rfl⟩ : syracuseStep 1844923 = 2767385) B2767385
theorem B6227657 : Blo 1843623 6227657 := bstep (se 2 (by rfl) ⟨2335371, by rfl⟩ : syracuseStep 6227657 = 4670743) B4670743
theorem B1844999 : Blo 1843623 1844999 := bstep (se 1 (by rfl) ⟨1383749, by rfl⟩ : syracuseStep 1844999 = 2767499) B2767499
theorem B1845007 : Blo 1843623 1845007 := bstep (se 1 (by rfl) ⟨1383755, by rfl⟩ : syracuseStep 1845007 = 2767511) B2767511
theorem B17721125 : Blo 1843623 17721125 := bstep (se 4 (by rfl) ⟨1661355, by rfl⟩ : syracuseStep 17721125 = 3322711) B3322711
theorem B1845051 : Blo 1843623 1845051 := bstep (se 1 (by rfl) ⟨1383788, by rfl⟩ : syracuseStep 1845051 = 2767577) B2767577
theorem B10504025 : Blo 1843623 10504025 := bstep (se 2 (by rfl) ⟨3939009, by rfl⟩ : syracuseStep 10504025 = 7878019) B7878019
theorem B1845127 : Blo 1843623 1845127 := bstep (se 1 (by rfl) ⟨1383845, by rfl⟩ : syracuseStep 1845127 = 2767691) B2767691
theorem B1845135 : Blo 1843623 1845135 := bstep (se 1 (by rfl) ⟨1383851, by rfl⟩ : syracuseStep 1845135 = 2767703) B2767703
theorem B1845179 : Blo 1843623 1845179 := bstep (se 1 (by rfl) ⟨1383884, by rfl⟩ : syracuseStep 1845179 = 2767769) B2767769
theorem B1845255 : Blo 1843623 1845255 := bstep (se 1 (by rfl) ⟨1383941, by rfl⟩ : syracuseStep 1845255 = 2767883) B2767883
theorem B2074639 : Blo 1843623 2074639 := bstep (se 1 (by rfl) ⟨1555979, by rfl⟩ : syracuseStep 2074639 = 3111959) B3111959
theorem B1845263 : Blo 1843623 1845263 := bstep (se 1 (by rfl) ⟨1383947, by rfl⟩ : syracuseStep 1845263 = 2767895) B2767895
theorem B4671503 : Blo 1843623 4671503 := bstep (se 1 (by rfl) ⟨3503627, by rfl⟩ : syracuseStep 4671503 = 7007255) B7007255
theorem B28387351 : Blo 1843623 28387351 := bstep (se 1 (by rfl) ⟨21290513, by rfl⟩ : syracuseStep 28387351 = 42581027) B42581027
theorem B1845307 : Blo 1843623 1845307 := bstep (se 1 (by rfl) ⟨1383980, by rfl⟩ : syracuseStep 1845307 = 2767961) B2767961
theorem B1845383 : Blo 1843623 1845383 := bstep (se 1 (by rfl) ⟨1384037, by rfl⟩ : syracuseStep 1845383 = 2768075) B2768075
theorem B1845391 : Blo 1843623 1845391 := bstep (se 1 (by rfl) ⟨1384043, by rfl⟩ : syracuseStep 1845391 = 2768087) B2768087
theorem B1845435 : Blo 1843623 1845435 := bstep (se 1 (by rfl) ⟨1384076, by rfl⟩ : syracuseStep 1845435 = 2768153) B2768153
theorem B1845511 : Blo 1843623 1845511 := bstep (se 1 (by rfl) ⟨1384133, by rfl⟩ : syracuseStep 1845511 = 2768267) B2768267
theorem B2492687 : Blo 1843623 2492687 := bstep (se 1 (by rfl) ⟨1869515, by rfl⟩ : syracuseStep 2492687 = 3739031) B3739031
theorem B1845519 : Blo 1843623 1845519 := bstep (se 1 (by rfl) ⟨1384139, by rfl⟩ : syracuseStep 1845519 = 2768279) B2768279
theorem B3500347 : Blo 1843623 3500347 := bstep (se 1 (by rfl) ⟨2625260, by rfl⟩ : syracuseStep 3500347 = 5250521) B5250521
theorem B9341243 : Blo 1843623 9341243 := bstep (se 1 (by rfl) ⟨7005932, by rfl⟩ : syracuseStep 9341243 = 14011865) B14011865
theorem B5253437 : Blo 1843623 5253437 := bstep (se 3 (by rfl) ⟨985019, by rfl⟩ : syracuseStep 5253437 = 1970039) B1970039
theorem B1845563 : Blo 1843623 1845563 := bstep (se 1 (by rfl) ⟨1384172, by rfl⟩ : syracuseStep 1845563 = 2768345) B2768345
theorem B17729927 : Blo 1843623 17729927 := bstep (se 1 (by rfl) ⟨13297445, by rfl⟩ : syracuseStep 17729927 = 26594891) B26594891
theorem B6228359 : Blo 1843623 6228359 := bstep (se 1 (by rfl) ⟨4671269, by rfl⟩ : syracuseStep 6228359 = 9342539) B9342539
theorem B9341405 : Blo 1843623 9341405 := bstep (se 3 (by rfl) ⟨1751513, by rfl⟩ : syracuseStep 9341405 = 3503027) B3503027
theorem B2075143 : Blo 1843623 2075143 := bstep (se 1 (by rfl) ⟨1556357, by rfl⟩ : syracuseStep 2075143 = 3112715) B3112715
theorem B2493001 : Blo 1843623 2493001 := bstep (se 2 (by rfl) ⟨934875, by rfl⟩ : syracuseStep 2493001 = 1869751) B1869751
theorem B7883351 : Blo 1843623 7883351 := bstep (se 1 (by rfl) ⟨5912513, by rfl⟩ : syracuseStep 7883351 = 11825027) B11825027
theorem B5253767 : Blo 1843623 5253767 := bstep (se 1 (by rfl) ⟨3940325, by rfl⟩ : syracuseStep 5253767 = 7880651) B7880651
theorem B2075323 : Blo 1843623 2075323 := bstep (se 1 (by rfl) ⟨1556492, by rfl⟩ : syracuseStep 2075323 = 3112985) B3112985
theorem B6310601 : Blo 1843623 6310601 := bstep (se 2 (by rfl) ⟨2366475, by rfl⟩ : syracuseStep 6310601 = 4732951) B4732951
theorem B2493175 : Blo 1843623 2493175 := bstep (se 1 (by rfl) ⟨1869881, by rfl⟩ : syracuseStep 2493175 = 3739763) B3739763
theorem B6228737 : Blo 1843623 6228737 := bstep (se 2 (by rfl) ⟨2335776, by rfl⟩ : syracuseStep 6228737 = 4671553) B4671553
theorem B3738383 : Blo 1843623 3738383 := bstep (se 1 (by rfl) ⟨2803787, by rfl⟩ : syracuseStep 3738383 = 5607575) B5607575
theorem B4983581 : Blo 1843623 4983581 := bstep (se 3 (by rfl) ⟨934421, by rfl⟩ : syracuseStep 4983581 = 1868843) B1868843
theorem B3500833 : Blo 1843623 3500833 := bstep (se 2 (by rfl) ⟨1312812, by rfl⟩ : syracuseStep 3500833 = 2625625) B2625625
theorem B9341729 : Blo 1843623 9341729 := bstep (se 2 (by rfl) ⟨3503148, by rfl⟩ : syracuseStep 9341729 = 7006297) B7006297
theorem B26585891 : Blo 1843623 26585891 := bstep (se 1 (by rfl) ⟨19939418, by rfl⟩ : syracuseStep 26585891 = 39878837) B39878837
theorem B4148153 : Blo 1843623 4148153 := bstep (se 2 (by rfl) ⟨1555557, by rfl⟩ : syracuseStep 4148153 = 3111115) B3111115
theorem B2804809 : Blo 1843623 2804809 := bstep (se 2 (by rfl) ⟨1051803, by rfl⟩ : syracuseStep 2804809 = 2103607) B2103607
theorem B9972823 : Blo 1843623 9972823 := bstep (se 1 (by rfl) ⟨7479617, by rfl⟩ : syracuseStep 9972823 = 14959235) B14959235
theorem B2075791 : Blo 1843623 2075791 := bstep (se 1 (by rfl) ⟨1556843, by rfl⟩ : syracuseStep 2075791 = 3113687) B3113687
theorem B54619285 : Blo 1843623 54619285 := bstep (se 6 (by rfl) ⟨1280139, by rfl⟩ : syracuseStep 54619285 = 2560279) B2560279
theorem B9333953 : Blo 1843623 9333953 := bstep (se 2 (by rfl) ⟨3500232, by rfl⟩ : syracuseStep 9333953 = 7000465) B7000465
theorem B59821253 : Blo 1843623 59821253 := bstep (se 4 (by rfl) ⟨5608242, by rfl⟩ : syracuseStep 59821253 = 11216485) B11216485
theorem B4148495 : Blo 1843623 4148495 := bstep (se 1 (by rfl) ⟨3111371, by rfl⟩ : syracuseStep 4148495 = 6222743) B6222743
theorem B4148513 : Blo 1843623 4148513 := bstep (se 2 (by rfl) ⟨1555692, by rfl⟩ : syracuseStep 4148513 = 3111385) B3111385
theorem B2493769 : Blo 1843623 2493769 := bstep (se 2 (by rfl) ⟨935163, by rfl⟩ : syracuseStep 2493769 = 1870327) B1870327
theorem B14003603 : Blo 1843623 14003603 := bstep (se 1 (by rfl) ⟨10502702, by rfl⟩ : syracuseStep 14003603 = 21005405) B21005405
theorem B17731001 : Blo 1843623 17731001 := bstep (se 2 (by rfl) ⟨6649125, by rfl⟩ : syracuseStep 17731001 = 13298251) B13298251
theorem B14192081 : Blo 1843623 14192081 := bstep (se 2 (by rfl) ⟨5322030, by rfl⟩ : syracuseStep 14192081 = 10644061) B10644061
theorem B4148855 : Blo 1843623 4148855 := bstep (se 1 (by rfl) ⟨3111641, by rfl⟩ : syracuseStep 4148855 = 6223283) B6223283
theorem B11816567 : Blo 1843623 11816567 := bstep (se 1 (by rfl) ⟨8862425, by rfl⟩ : syracuseStep 11816567 = 17724851) B17724851
theorem B2076295 : Blo 1843623 2076295 := bstep (se 1 (by rfl) ⟨1557221, by rfl⟩ : syracuseStep 2076295 = 3114443) B3114443
theorem B8867501 : Blo 1843623 8867501 := bstep (se 3 (by rfl) ⟨1662656, by rfl⟩ : syracuseStep 8867501 = 3325313) B3325313
theorem B16821989 : Blo 1843623 16821989 := bstep (se 4 (by rfl) ⟨1577061, by rfl⟩ : syracuseStep 16821989 = 3154123) B3154123
theorem B9342701 : Blo 1843623 9342701 := bstep (se 3 (by rfl) ⟨1751756, by rfl⟩ : syracuseStep 9342701 = 3503513) B3503513
theorem B15765263 : Blo 1843623 15765263 := bstep (se 1 (by rfl) ⟨11823947, by rfl⟩ : syracuseStep 15765263 = 23647895) B23647895
theorem B4149035 : Blo 1843623 4149035 := bstep (se 1 (by rfl) ⟨3111776, by rfl⟩ : syracuseStep 4149035 = 6223553) B6223553
theorem B8867731 : Blo 1843623 8867731 := bstep (se 1 (by rfl) ⟨6650798, by rfl⟩ : syracuseStep 8867731 = 13301597) B13301597
theorem B3502025 : Blo 1843623 3502025 := bstep (se 2 (by rfl) ⟨1313259, by rfl⟩ : syracuseStep 3502025 = 2626519) B2626519
theorem B4149395 : Blo 1843623 4149395 := bstep (se 1 (by rfl) ⟨3112046, by rfl⟩ : syracuseStep 4149395 = 6224093) B6224093
theorem B4149449 : Blo 1843623 4149449 := bstep (se 2 (by rfl) ⟨1556043, by rfl⟩ : syracuseStep 4149449 = 3112087) B3112087
theorem B5607695 : Blo 1843623 5607695 := bstep (se 1 (by rfl) ⟨4205771, by rfl⟩ : syracuseStep 5607695 = 8411543) B8411543
theorem B5255543 : Blo 1843623 5255543 := bstep (se 1 (by rfl) ⟨3941657, by rfl⟩ : syracuseStep 5255543 = 7883315) B7883315
theorem B9335249 : Blo 1843623 9335249 := bstep (se 2 (by rfl) ⟨3500718, by rfl⟩ : syracuseStep 9335249 = 7001437) B7001437
theorem B5911051 : Blo 1843623 5911051 := bstep (se 1 (by rfl) ⟨4433288, by rfl⟩ : syracuseStep 5911051 = 8866577) B8866577
theorem B6222365 : Blo 1843623 6222365 := bstep (se 3 (by rfl) ⟨1166693, by rfl⟩ : syracuseStep 6222365 = 2333387) B2333387
theorem B2765447 : Blo 1843623 2765447 := bstep (se 1 (by rfl) ⟨2074085, by rfl⟩ : syracuseStep 2765447 = 4148171) B4148171
theorem B3502739 : Blo 1843623 3502739 := bstep (se 1 (by rfl) ⟨2627054, by rfl⟩ : syracuseStep 3502739 = 5254109) B5254109
theorem B2765483 : Blo 1843623 2765483 := bstep (se 1 (by rfl) ⟨2074112, by rfl⟩ : syracuseStep 2765483 = 4148225) B4148225
theorem B3502777 : Blo 1843623 3502777 := bstep (se 2 (by rfl) ⟨1313541, by rfl⟩ : syracuseStep 3502777 = 2627083) B2627083
theorem B79794881 : Blo 1843623 79794881 := bstep (se 2 (by rfl) ⟨29923080, by rfl⟩ : syracuseStep 79794881 = 59846161) B59846161
theorem B2765513 : Blo 1843623 2765513 := bstep (se 2 (by rfl) ⟨1037067, by rfl⟩ : syracuseStep 2765513 = 2074135) B2074135
theorem B2765627 : Blo 1843623 2765627 := bstep (se 1 (by rfl) ⟨2074220, by rfl⟩ : syracuseStep 2765627 = 4148441) B4148441
theorem B2765687 : Blo 1843623 2765687 := bstep (se 1 (by rfl) ⟨2074265, by rfl⟩ : syracuseStep 2765687 = 4148531) B4148531
theorem B4150151 : Blo 1843623 4150151 := bstep (se 1 (by rfl) ⟨3112613, by rfl⟩ : syracuseStep 4150151 = 6225227) B6225227
theorem B2765711 : Blo 1843623 2765711 := bstep (se 1 (by rfl) ⟨2074283, by rfl⟩ : syracuseStep 2765711 = 4148567) B4148567
theorem B2765753 : Blo 1843623 2765753 := bstep (se 2 (by rfl) ⟨1037157, by rfl⟩ : syracuseStep 2765753 = 2074315) B2074315
theorem B2765831 : Blo 1843623 2765831 := bstep (se 1 (by rfl) ⟨2074373, by rfl⟩ : syracuseStep 2765831 = 4148747) B4148747
theorem B2765867 : Blo 1843623 2765867 := bstep (se 1 (by rfl) ⟨2074400, by rfl⟩ : syracuseStep 2765867 = 4148801) B4148801
theorem B4150331 : Blo 1843623 4150331 := bstep (se 1 (by rfl) ⟨3112748, by rfl⟩ : syracuseStep 4150331 = 6225497) B6225497
theorem B2765897 : Blo 1843623 2765897 := bstep (se 2 (by rfl) ⟨1037211, by rfl⟩ : syracuseStep 2765897 = 2074423) B2074423
theorem B4150457 : Blo 1843623 4150457 := bstep (se 2 (by rfl) ⟨1556421, by rfl⟩ : syracuseStep 4150457 = 3112843) B3112843
theorem B2766011 : Blo 1843623 2766011 := bstep (se 1 (by rfl) ⟨2074508, by rfl⟩ : syracuseStep 2766011 = 4149017) B4149017
theorem B2766071 : Blo 1843623 2766071 := bstep (se 1 (by rfl) ⟨2074553, by rfl⟩ : syracuseStep 2766071 = 4149107) B4149107
theorem B2766095 : Blo 1843623 2766095 := bstep (se 1 (by rfl) ⟨2074571, by rfl⟩ : syracuseStep 2766095 = 4149143) B4149143
theorem B2766137 : Blo 1843623 2766137 := bstep (se 2 (by rfl) ⟨1037301, by rfl⟩ : syracuseStep 2766137 = 2074603) B2074603
theorem B8410483 : Blo 1843623 8410483 := bstep (se 1 (by rfl) ⟨6307862, by rfl⟩ : syracuseStep 8410483 = 12615725) B12615725
theorem B2766215 : Blo 1843623 2766215 := bstep (se 1 (by rfl) ⟨2074661, by rfl⟩ : syracuseStep 2766215 = 4149323) B4149323
theorem B2766251 : Blo 1843623 2766251 := bstep (se 1 (by rfl) ⟨2074688, by rfl⟩ : syracuseStep 2766251 = 4149377) B4149377
theorem B2766281 : Blo 1843623 2766281 := bstep (se 2 (by rfl) ⟨1037355, by rfl⟩ : syracuseStep 2766281 = 2074711) B2074711
theorem B4150799 : Blo 1843623 4150799 := bstep (se 1 (by rfl) ⟨3113099, by rfl⟩ : syracuseStep 4150799 = 6226199) B6226199
theorem B6313501 : Blo 1843623 6313501 := bstep (se 3 (by rfl) ⟨1183781, by rfl⟩ : syracuseStep 6313501 = 2367563) B2367563
theorem B4150817 : Blo 1843623 4150817 := bstep (se 2 (by rfl) ⟨1556556, by rfl⟩ : syracuseStep 4150817 = 3113113) B3113113
theorem B2766395 : Blo 1843623 2766395 := bstep (se 1 (by rfl) ⟨2074796, by rfl⟩ : syracuseStep 2766395 = 4149593) B4149593
theorem B5609021 : Blo 1843623 5609021 := bstep (se 3 (by rfl) ⟨1051691, by rfl⟩ : syracuseStep 5609021 = 2103383) B2103383
theorem B4666967 : Blo 1843623 4666967 := bstep (se 1 (by rfl) ⟨3500225, by rfl⟩ : syracuseStep 4666967 = 7000451) B7000451
theorem B2766455 : Blo 1843623 2766455 := bstep (se 1 (by rfl) ⟨2074841, by rfl⟩ : syracuseStep 2766455 = 4149683) B4149683
theorem B2627191 : Blo 1843623 2627191 := bstep (se 1 (by rfl) ⟨1970393, by rfl⟩ : syracuseStep 2627191 = 3940787) B3940787
theorem B3741319 : Blo 1843623 3741319 := bstep (se 1 (by rfl) ⟨2805989, by rfl⟩ : syracuseStep 3741319 = 5611979) B5611979
theorem B2766479 : Blo 1843623 2766479 := bstep (se 1 (by rfl) ⟨2074859, by rfl⟩ : syracuseStep 2766479 = 4149719) B4149719
theorem B2766521 : Blo 1843623 2766521 := bstep (se 2 (by rfl) ⟨1037445, by rfl⟩ : syracuseStep 2766521 = 2074891) B2074891
theorem B2766599 : Blo 1843623 2766599 := bstep (se 1 (by rfl) ⟨2074949, by rfl⟩ : syracuseStep 2766599 = 4149899) B4149899
theorem B4667179 : Blo 1843623 4667179 := bstep (se 1 (by rfl) ⟨3500384, by rfl⟩ : syracuseStep 4667179 = 7000769) B7000769
theorem B2766635 : Blo 1843623 2766635 := bstep (se 1 (by rfl) ⟨2074976, by rfl⟩ : syracuseStep 2766635 = 4149953) B4149953
theorem B2766665 : Blo 1843623 2766665 := bstep (se 2 (by rfl) ⟨1037499, by rfl⟩ : syracuseStep 2766665 = 2074999) B2074999
theorem B4151159 : Blo 1843623 4151159 := bstep (se 1 (by rfl) ⟨3113369, by rfl⟩ : syracuseStep 4151159 = 6226739) B6226739
theorem B6223769 : Blo 1843623 6223769 := bstep (se 2 (by rfl) ⟨2333913, by rfl⟩ : syracuseStep 6223769 = 4667827) B4667827
theorem B11220889 : Blo 1843623 11220889 := bstep (se 2 (by rfl) ⟨4207833, by rfl⟩ : syracuseStep 11220889 = 8415667) B8415667
theorem B4667321 : Blo 1843623 4667321 := bstep (se 2 (by rfl) ⟨1750245, by rfl⟩ : syracuseStep 4667321 = 3500491) B3500491
theorem B3938233 : Blo 1843623 3938233 := bstep (se 2 (by rfl) ⟨1476837, by rfl⟩ : syracuseStep 3938233 = 2953675) B2953675
theorem B2766779 : Blo 1843623 2766779 := bstep (se 1 (by rfl) ⟨2075084, by rfl⟩ : syracuseStep 2766779 = 4150169) B4150169
theorem B6313913 : Blo 1843623 6313913 := bstep (se 2 (by rfl) ⟨2367717, by rfl⟩ : syracuseStep 6313913 = 4735435) B4735435
theorem B2766839 : Blo 1843623 2766839 := bstep (se 1 (by rfl) ⟨2075129, by rfl⟩ : syracuseStep 2766839 = 4150259) B4150259
theorem B2766863 : Blo 1843623 2766863 := bstep (se 1 (by rfl) ⟨2075147, by rfl⟩ : syracuseStep 2766863 = 4150295) B4150295
theorem B4151339 : Blo 1843623 4151339 := bstep (se 1 (by rfl) ⟨3113504, by rfl⟩ : syracuseStep 4151339 = 6227009) B6227009
theorem B44890157 : Blo 1843623 44890157 := bstep (se 3 (by rfl) ⟨8416904, by rfl⟩ : syracuseStep 44890157 = 16833809) B16833809
theorem B2766905 : Blo 1843623 2766905 := bstep (se 2 (by rfl) ⟨1037589, by rfl⟩ : syracuseStep 2766905 = 2075179) B2075179
theorem B8411197 : Blo 1843623 8411197 := bstep (se 3 (by rfl) ⟨1577099, by rfl⟩ : syracuseStep 8411197 = 3154199) B3154199
theorem B5322839 : Blo 1843623 5322839 := bstep (se 1 (by rfl) ⟨3992129, by rfl⟩ : syracuseStep 5322839 = 7984259) B7984259
theorem B2766983 : Blo 1843623 2766983 := bstep (se 1 (by rfl) ⟨2075237, by rfl⟩ : syracuseStep 2766983 = 4150475) B4150475
theorem B2767019 : Blo 1843623 2767019 := bstep (se 1 (by rfl) ⟨2075264, by rfl⟩ : syracuseStep 2767019 = 4150529) B4150529
theorem B2767049 : Blo 1843623 2767049 := bstep (se 2 (by rfl) ⟨1037643, by rfl⟩ : syracuseStep 2767049 = 2075287) B2075287
theorem B25942289 : Blo 1843623 25942289 := bstep (se 2 (by rfl) ⟨9728358, by rfl⟩ : syracuseStep 25942289 = 19456717) B19456717
theorem B2767163 : Blo 1843623 2767163 := bstep (se 1 (by rfl) ⟨2075372, by rfl⟩ : syracuseStep 2767163 = 4150745) B4150745
theorem B32389469 : Blo 1843623 32389469 := bstep (se 3 (by rfl) ⟨6073025, by rfl⟩ : syracuseStep 32389469 = 12146051) B12146051
theorem B2767223 : Blo 1843623 2767223 := bstep (se 1 (by rfl) ⟨2075417, by rfl⟩ : syracuseStep 2767223 = 4150835) B4150835
theorem B2767247 : Blo 1843623 2767247 := bstep (se 1 (by rfl) ⟨2075435, by rfl⟩ : syracuseStep 2767247 = 4150871) B4150871
theorem B4151699 : Blo 1843623 4151699 := bstep (se 1 (by rfl) ⟨3113774, by rfl⟩ : syracuseStep 4151699 = 6227549) B6227549
theorem B2767289 : Blo 1843623 2767289 := bstep (se 2 (by rfl) ⟨1037733, by rfl⟩ : syracuseStep 2767289 = 2075467) B2075467
theorem B4151753 : Blo 1843623 4151753 := bstep (se 2 (by rfl) ⟨1556907, by rfl⟩ : syracuseStep 4151753 = 3113815) B3113815
theorem B18930125 : Blo 1843623 18930125 := bstep (se 3 (by rfl) ⟨3549398, by rfl⟩ : syracuseStep 18930125 = 7098797) B7098797
theorem B2767367 : Blo 1843623 2767367 := bstep (se 1 (by rfl) ⟨2075525, by rfl⟩ : syracuseStep 2767367 = 4151051) B4151051
theorem B9337355 : Blo 1843623 9337355 := bstep (se 1 (by rfl) ⟨7003016, by rfl⟩ : syracuseStep 9337355 = 14006033) B14006033
theorem B3111439 : Blo 1843623 3111439 := bstep (se 1 (by rfl) ⟨2333579, by rfl⟩ : syracuseStep 3111439 = 4667159) B4667159
theorem B2767403 : Blo 1843623 2767403 := bstep (se 1 (by rfl) ⟨2075552, by rfl⟩ : syracuseStep 2767403 = 4151105) B4151105
theorem B59841089 : Blo 1843623 59841089 := bstep (se 2 (by rfl) ⟨22440408, by rfl⟩ : syracuseStep 59841089 = 44880817) B44880817
theorem B11377219 : Blo 1843623 11377219 := bstep (se 1 (by rfl) ⟨8532914, by rfl⟩ : syracuseStep 11377219 = 17065829) B17065829
theorem B2767433 : Blo 1843623 2767433 := bstep (se 2 (by rfl) ⟨1037787, by rfl⟩ : syracuseStep 2767433 = 2075575) B2075575
theorem B6224471 : Blo 1843623 6224471 := bstep (se 1 (by rfl) ⟨4668353, by rfl⟩ : syracuseStep 6224471 = 9336707) B9336707
theorem B67287671 : Blo 1843623 67287671 := bstep (se 1 (by rfl) ⟨50465753, by rfl⟩ : syracuseStep 67287671 = 100931507) B100931507
theorem B9337517 : Blo 1843623 9337517 := bstep (se 3 (by rfl) ⟨1750784, by rfl⟩ : syracuseStep 9337517 = 3501569) B3501569
theorem B2767547 : Blo 1843623 2767547 := bstep (se 1 (by rfl) ⟨2075660, by rfl⟩ : syracuseStep 2767547 = 4151321) B4151321
theorem B2767607 : Blo 1843623 2767607 := bstep (se 1 (by rfl) ⟨2075705, by rfl⟩ : syracuseStep 2767607 = 4151411) B4151411
theorem B7002881 : Blo 1843623 7002881 := bstep (se 2 (by rfl) ⟨2626080, by rfl⟩ : syracuseStep 7002881 = 5252161) B5252161
theorem B7002895 : Blo 1843623 7002895 := bstep (se 1 (by rfl) ⟨5252171, by rfl⟩ : syracuseStep 7002895 = 10504343) B10504343
theorem B2767631 : Blo 1843623 2767631 := bstep (se 1 (by rfl) ⟨2075723, by rfl⟩ : syracuseStep 2767631 = 4151447) B4151447
theorem B6650657 : Blo 1843623 6650657 := bstep (se 2 (by rfl) ⟨2493996, by rfl⟩ : syracuseStep 6650657 = 4987993) B4987993
theorem B21011237 : Blo 1843623 21011237 := bstep (se 4 (by rfl) ⟨1969803, by rfl⟩ : syracuseStep 21011237 = 3939607) B3939607
theorem B2767673 : Blo 1843623 2767673 := bstep (se 2 (by rfl) ⟨1037877, by rfl⟩ : syracuseStep 2767673 = 2075755) B2075755
theorem B2767751 : Blo 1843623 2767751 := bstep (se 1 (by rfl) ⟨2075813, by rfl⟩ : syracuseStep 2767751 = 4151627) B4151627
theorem B4668313 : Blo 1843623 4668313 := bstep (se 2 (by rfl) ⟨1750617, by rfl⟩ : syracuseStep 4668313 = 3501235) B3501235
theorem B42589091 : Blo 1843623 42589091 := bstep (se 1 (by rfl) ⟨31941818, by rfl⟩ : syracuseStep 42589091 = 63883637) B63883637
theorem B2767787 : Blo 1843623 2767787 := bstep (se 1 (by rfl) ⟨2075840, by rfl⟩ : syracuseStep 2767787 = 4151681) B4151681
theorem B2767817 : Blo 1843623 2767817 := bstep (se 2 (by rfl) ⟨1037931, by rfl⟩ : syracuseStep 2767817 = 2075863) B2075863
theorem B2333711 : Blo 1843623 2333711 := bstep (se 1 (by rfl) ⟨1750283, by rfl⟩ : syracuseStep 2333711 = 3500567) B3500567
theorem B3111979 : Blo 1843623 3111979 := bstep (se 1 (by rfl) ⟨2333984, by rfl⟩ : syracuseStep 3111979 = 4667969) B4667969
theorem B4668475 : Blo 1843623 4668475 := bstep (se 1 (by rfl) ⟨3501356, by rfl⟩ : syracuseStep 4668475 = 7002713) B7002713
theorem B2767931 : Blo 1843623 2767931 := bstep (se 1 (by rfl) ⟨2075948, by rfl⟩ : syracuseStep 2767931 = 4151897) B4151897
theorem B22428733 : Blo 1843623 22428733 := bstep (se 3 (by rfl) ⟨4205387, by rfl⟩ : syracuseStep 22428733 = 8410775) B8410775
theorem B6224957 : Blo 1843623 6224957 := bstep (se 3 (by rfl) ⟨1167179, by rfl⟩ : syracuseStep 6224957 = 2334359) B2334359
theorem B5250167 : Blo 1843623 5250167 := bstep (se 1 (by rfl) ⟨3937625, by rfl⟩ : syracuseStep 5250167 = 7875251) B7875251
theorem B2767991 : Blo 1843623 2767991 := bstep (se 1 (by rfl) ⟨2075993, by rfl⟩ : syracuseStep 2767991 = 4151987) B4151987
theorem B4152455 : Blo 1843623 4152455 := bstep (se 1 (by rfl) ⟨3114341, by rfl⟩ : syracuseStep 4152455 = 6228683) B6228683
theorem B2768015 : Blo 1843623 2768015 := bstep (se 1 (by rfl) ⟨2076011, by rfl⟩ : syracuseStep 2768015 = 4152023) B4152023
theorem B3112121 : Blo 1843623 3112121 := bstep (se 2 (by rfl) ⟨1167045, by rfl⟩ : syracuseStep 3112121 = 2334091) B2334091
theorem B2768057 : Blo 1843623 2768057 := bstep (se 2 (by rfl) ⟨1038021, by rfl⟩ : syracuseStep 2768057 = 2076043) B2076043
theorem B4668617 : Blo 1843623 4668617 := bstep (se 2 (by rfl) ⟨1750731, by rfl⟩ : syracuseStep 4668617 = 3501463) B3501463
theorem B2768135 : Blo 1843623 2768135 := bstep (se 1 (by rfl) ⟨2076101, by rfl⟩ : syracuseStep 2768135 = 4152203) B4152203
theorem B2768171 : Blo 1843623 2768171 := bstep (se 1 (by rfl) ⟨2076128, by rfl⟩ : syracuseStep 2768171 = 4152257) B4152257
theorem B10501427 : Blo 1843623 10501427 := bstep (se 1 (by rfl) ⟨7876070, by rfl⟩ : syracuseStep 10501427 = 15752141) B15752141
theorem B7101755 : Blo 1843623 7101755 := bstep (se 1 (by rfl) ⟨5326316, by rfl⟩ : syracuseStep 7101755 = 10652633) B10652633
theorem B4152635 : Blo 1843623 4152635 := bstep (se 1 (by rfl) ⟨3114476, by rfl⟩ : syracuseStep 4152635 = 6228953) B6228953
theorem B2768201 : Blo 1843623 2768201 := bstep (se 2 (by rfl) ⟨1038075, by rfl⟩ : syracuseStep 2768201 = 2076151) B2076151
theorem B8412569 : Blo 1843623 8412569 := bstep (se 2 (by rfl) ⟨3154713, by rfl⟩ : syracuseStep 8412569 = 6309427) B6309427
theorem B2768315 : Blo 1843623 2768315 := bstep (se 1 (by rfl) ⟨2076236, by rfl⟩ : syracuseStep 2768315 = 4152473) B4152473
theorem B3325385 : Blo 1843623 3325385 := bstep (se 2 (by rfl) ⟨1247019, by rfl⟩ : syracuseStep 3325385 = 2494039) B2494039
theorem B2768375 : Blo 1843623 2768375 := bstep (se 1 (by rfl) ⟨2076281, by rfl⟩ : syracuseStep 2768375 = 4152563) B4152563
theorem B2768399 : Blo 1843623 2768399 := bstep (se 1 (by rfl) ⟨2076299, by rfl⟩ : syracuseStep 2768399 = 4152599) B4152599
theorem B4668961 : Blo 1843623 4668961 := bstep (se 2 (by rfl) ⟨1750860, by rfl⟩ : syracuseStep 4668961 = 3501721) B3501721
theorem B2662031 : Blo 1843623 2662031 := bstep (se 1 (by rfl) ⟨1996523, by rfl⟩ : syracuseStep 2662031 = 3993047) B3993047
theorem B7880429 : Blo 1843623 7880429 := bstep (se 3 (by rfl) ⟨1477580, by rfl⟩ : syracuseStep 7880429 = 2955161) B2955161
theorem B3112823 : Blo 1843623 3112823 := bstep (se 1 (by rfl) ⟨2334617, by rfl⟩ : syracuseStep 3112823 = 4669235) B4669235
theorem B2367419 : Blo 1843623 2367419 := bstep (se 1 (by rfl) ⟨1775564, by rfl⟩ : syracuseStep 2367419 = 3551129) B3551129
theorem B4669447 : Blo 1843623 4669447 := bstep (se 1 (by rfl) ⟨3502085, by rfl⟩ : syracuseStep 4669447 = 7004171) B7004171
theorem B3113039 : Blo 1843623 3113039 := bstep (se 1 (by rfl) ⟨2334779, by rfl⟩ : syracuseStep 3113039 = 4669559) B4669559
theorem B11214929 : Blo 1843623 11214929 := bstep (se 2 (by rfl) ⟨4205598, by rfl⟩ : syracuseStep 11214929 = 8411197) B8411197
theorem B11812979 : Blo 1843623 11812979 := bstep (se 1 (by rfl) ⟨8859734, by rfl⟩ : syracuseStep 11812979 = 17719469) B17719469
theorem B6226091 : Blo 1843623 6226091 := bstep (se 1 (by rfl) ⟨4669568, by rfl⟩ : syracuseStep 6226091 = 9339137) B9339137
theorem B1843631 : Blo 1843623 1843631 := bstep (se 1 (by rfl) ⟨1382723, by rfl⟩ : syracuseStep 1843631 = 2765447) B2765447
theorem B2335159 : Blo 1843623 2335159 := bstep (se 1 (by rfl) ⟨1751369, by rfl⟩ : syracuseStep 2335159 = 3502739) B3502739
theorem B1843655 : Blo 1843623 1843655 := bstep (se 1 (by rfl) ⟨1382741, by rfl⟩ : syracuseStep 1843655 = 2765483) B2765483
theorem B1843675 : Blo 1843623 1843675 := bstep (se 1 (by rfl) ⟨1382756, by rfl⟩ : syracuseStep 1843675 = 2765513) B2765513
theorem B1843751 : Blo 1843623 1843751 := bstep (se 1 (by rfl) ⟨1382813, by rfl⟩ : syracuseStep 1843751 = 2765627) B2765627
theorem B1843791 : Blo 1843623 1843791 := bstep (se 1 (by rfl) ⟨1382843, by rfl⟩ : syracuseStep 1843791 = 2765687) B2765687
theorem B1843807 : Blo 1843623 1843807 := bstep (se 1 (by rfl) ⟨1382855, by rfl⟩ : syracuseStep 1843807 = 2765711) B2765711
theorem B1843835 : Blo 1843623 1843835 := bstep (se 1 (by rfl) ⟨1382876, by rfl⟩ : syracuseStep 1843835 = 2765753) B2765753
theorem B4670075 : Blo 1843623 4670075 := bstep (se 1 (by rfl) ⟨3502556, by rfl⟩ : syracuseStep 4670075 = 7005113) B7005113
theorem B1843887 : Blo 1843623 1843887 := bstep (se 1 (by rfl) ⟨1382915, by rfl⟩ : syracuseStep 1843887 = 2765831) B2765831
theorem B7881401 : Blo 1843623 7881401 := bstep (se 2 (by rfl) ⟨2955525, by rfl⟩ : syracuseStep 7881401 = 5911051) B5911051
theorem B1843911 : Blo 1843623 1843911 := bstep (se 1 (by rfl) ⟨1382933, by rfl⟩ : syracuseStep 1843911 = 2765867) B2765867
theorem B6226631 : Blo 1843623 6226631 := bstep (se 1 (by rfl) ⟨4669973, by rfl⟩ : syracuseStep 6226631 = 9339947) B9339947
theorem B1843931 : Blo 1843623 1843931 := bstep (se 1 (by rfl) ⟨1382948, by rfl⟩ : syracuseStep 1843931 = 2765897) B2765897
theorem B21021443 : Blo 1843623 21021443 := bstep (se 1 (by rfl) ⟨15766082, by rfl⟩ : syracuseStep 21021443 = 31532165) B31532165
theorem B1844007 : Blo 1843623 1844007 := bstep (se 1 (by rfl) ⟨1383005, by rfl⟩ : syracuseStep 1844007 = 2766011) B2766011
theorem B1844047 : Blo 1843623 1844047 := bstep (se 1 (by rfl) ⟨1383035, by rfl⟩ : syracuseStep 1844047 = 2766071) B2766071
theorem B1844063 : Blo 1843623 1844063 := bstep (se 1 (by rfl) ⟨1383047, by rfl⟩ : syracuseStep 1844063 = 2766095) B2766095
theorem B1844091 : Blo 1843623 1844091 := bstep (se 1 (by rfl) ⟨1383068, by rfl⟩ : syracuseStep 1844091 = 2766137) B2766137
theorem B4670369 : Blo 1843623 4670369 := bstep (se 2 (by rfl) ⟨1751388, by rfl⟩ : syracuseStep 4670369 = 3502777) B3502777
theorem B1844143 : Blo 1843623 1844143 := bstep (se 1 (by rfl) ⟨1383107, by rfl⟩ : syracuseStep 1844143 = 2766215) B2766215
theorem B3113903 : Blo 1843623 3113903 := bstep (se 1 (by rfl) ⟨2335427, by rfl⟩ : syracuseStep 3113903 = 4670855) B4670855
theorem B1844167 : Blo 1843623 1844167 := bstep (se 1 (by rfl) ⟨1383125, by rfl⟩ : syracuseStep 1844167 = 2766251) B2766251
theorem B1844187 : Blo 1843623 1844187 := bstep (se 1 (by rfl) ⟨1383140, by rfl⟩ : syracuseStep 1844187 = 2766281) B2766281
theorem B1844263 : Blo 1843623 1844263 := bstep (se 1 (by rfl) ⟨1383197, by rfl⟩ : syracuseStep 1844263 = 2766395) B2766395
theorem B1844303 : Blo 1843623 1844303 := bstep (se 1 (by rfl) ⟨1383227, by rfl⟩ : syracuseStep 1844303 = 2766455) B2766455
theorem B1844319 : Blo 1843623 1844319 := bstep (se 1 (by rfl) ⟨1383239, by rfl⟩ : syracuseStep 1844319 = 2766479) B2766479
theorem B1844347 : Blo 1843623 1844347 := bstep (se 1 (by rfl) ⟨1383260, by rfl⟩ : syracuseStep 1844347 = 2766521) B2766521
theorem B1844399 : Blo 1843623 1844399 := bstep (se 1 (by rfl) ⟨1383299, by rfl⟩ : syracuseStep 1844399 = 2766599) B2766599
theorem B11814083 : Blo 1843623 11814083 := bstep (se 1 (by rfl) ⟨8860562, by rfl⟩ : syracuseStep 11814083 = 17721125) B17721125
theorem B1844423 : Blo 1843623 1844423 := bstep (se 1 (by rfl) ⟨1383317, by rfl⟩ : syracuseStep 1844423 = 2766635) B2766635
theorem B50480333 : Blo 1843623 50480333 := bstep (se 3 (by rfl) ⟨9465062, by rfl⟩ : syracuseStep 50480333 = 18930125) B18930125
theorem B1844443 : Blo 1843623 1844443 := bstep (se 1 (by rfl) ⟨1383332, by rfl⟩ : syracuseStep 1844443 = 2766665) B2766665
theorem B1844519 : Blo 1843623 1844519 := bstep (se 1 (by rfl) ⟨1383389, by rfl⟩ : syracuseStep 1844519 = 2766779) B2766779
theorem B1844559 : Blo 1843623 1844559 := bstep (se 1 (by rfl) ⟨1383419, by rfl⟩ : syracuseStep 1844559 = 2766839) B2766839
theorem B1844575 : Blo 1843623 1844575 := bstep (se 1 (by rfl) ⟨1383431, by rfl⟩ : syracuseStep 1844575 = 2766863) B2766863
theorem B3114335 : Blo 1843623 3114335 := bstep (se 1 (by rfl) ⟨2335751, by rfl⟩ : syracuseStep 3114335 = 4671503) B4671503
theorem B1844603 : Blo 1843623 1844603 := bstep (se 1 (by rfl) ⟨1383452, by rfl⟩ : syracuseStep 1844603 = 2766905) B2766905
theorem B1844655 : Blo 1843623 1844655 := bstep (se 1 (by rfl) ⟨1383491, by rfl⟩ : syracuseStep 1844655 = 2766983) B2766983
theorem B1844679 : Blo 1843623 1844679 := bstep (se 1 (by rfl) ⟨1383509, by rfl⟩ : syracuseStep 1844679 = 2767019) B2767019
theorem B179504585 : Blo 1843623 179504585 := bstep (se 2 (by rfl) ⟨67314219, by rfl⟩ : syracuseStep 179504585 = 134628439) B134628439
theorem B13297097 : Blo 1843623 13297097 := bstep (se 2 (by rfl) ⟨4986411, by rfl⟩ : syracuseStep 13297097 = 9972823) B9972823
theorem B1844699 : Blo 1843623 1844699 := bstep (se 1 (by rfl) ⟨1383524, by rfl⟩ : syracuseStep 1844699 = 2767049) B2767049
theorem B1844775 : Blo 1843623 1844775 := bstep (se 1 (by rfl) ⟨1383581, by rfl⟩ : syracuseStep 1844775 = 2767163) B2767163
theorem B6227495 : Blo 1843623 6227495 := bstep (se 1 (by rfl) ⟨4670621, by rfl⟩ : syracuseStep 6227495 = 9341243) B9341243
theorem B1844815 : Blo 1843623 1844815 := bstep (se 1 (by rfl) ⟨1383611, by rfl⟩ : syracuseStep 1844815 = 2767223) B2767223
theorem B1844831 : Blo 1843623 1844831 := bstep (se 1 (by rfl) ⟨1383623, by rfl⟩ : syracuseStep 1844831 = 2767247) B2767247
theorem B1844859 : Blo 1843623 1844859 := bstep (se 1 (by rfl) ⟨1383644, by rfl⟩ : syracuseStep 1844859 = 2767289) B2767289
theorem B6227603 : Blo 1843623 6227603 := bstep (se 1 (by rfl) ⟨4670702, by rfl⟩ : syracuseStep 6227603 = 9341405) B9341405
theorem B1844911 : Blo 1843623 1844911 := bstep (se 1 (by rfl) ⟨1383683, by rfl⟩ : syracuseStep 1844911 = 2767367) B2767367
theorem B1844935 : Blo 1843623 1844935 := bstep (se 1 (by rfl) ⟨1383701, by rfl⟩ : syracuseStep 1844935 = 2767403) B2767403
theorem B1844955 : Blo 1843623 1844955 := bstep (se 1 (by rfl) ⟨1383716, by rfl⟩ : syracuseStep 1844955 = 2767433) B2767433
theorem B1845031 : Blo 1843623 1845031 := bstep (se 1 (by rfl) ⟨1383773, by rfl⟩ : syracuseStep 1845031 = 2767547) B2767547
theorem B1845071 : Blo 1843623 1845071 := bstep (se 1 (by rfl) ⟨1383803, by rfl⟩ : syracuseStep 1845071 = 2767607) B2767607
theorem B2492255 : Blo 1843623 2492255 := bstep (se 1 (by rfl) ⟨1869191, by rfl⟩ : syracuseStep 2492255 = 3738383) B3738383
theorem B1845087 : Blo 1843623 1845087 := bstep (se 1 (by rfl) ⟨1383815, by rfl⟩ : syracuseStep 1845087 = 2767631) B2767631
theorem B6227819 : Blo 1843623 6227819 := bstep (se 1 (by rfl) ⟨4670864, by rfl⟩ : syracuseStep 6227819 = 9341729) B9341729
theorem B4433771 : Blo 1843623 4433771 := bstep (se 1 (by rfl) ⟨3325328, by rfl⟩ : syracuseStep 4433771 = 6650657) B6650657
theorem B1845115 : Blo 1843623 1845115 := bstep (se 1 (by rfl) ⟨1383836, by rfl⟩ : syracuseStep 1845115 = 2767673) B2767673
theorem B6227873 : Blo 1843623 6227873 := bstep (se 2 (by rfl) ⟨2335452, by rfl⟩ : syracuseStep 6227873 = 4670905) B4670905
theorem B1845167 : Blo 1843623 1845167 := bstep (se 1 (by rfl) ⟨1383875, by rfl⟩ : syracuseStep 1845167 = 2767751) B2767751
theorem B1845191 : Blo 1843623 1845191 := bstep (se 1 (by rfl) ⟨1383893, by rfl⟩ : syracuseStep 1845191 = 2767787) B2767787
theorem B1845211 : Blo 1843623 1845211 := bstep (se 1 (by rfl) ⟨1383908, by rfl⟩ : syracuseStep 1845211 = 2767817) B2767817
theorem B1845287 : Blo 1843623 1845287 := bstep (se 1 (by rfl) ⟨1383965, by rfl⟩ : syracuseStep 1845287 = 2767931) B2767931
theorem B3500111 : Blo 1843623 3500111 := bstep (se 1 (by rfl) ⟨2625083, by rfl⟩ : syracuseStep 3500111 = 5250167) B5250167
theorem B1845327 : Blo 1843623 1845327 := bstep (se 1 (by rfl) ⟨1383995, by rfl⟩ : syracuseStep 1845327 = 2767991) B2767991
theorem B1845343 : Blo 1843623 1845343 := bstep (se 1 (by rfl) ⟨1384007, by rfl⟩ : syracuseStep 1845343 = 2768015) B2768015
theorem B2074747 : Blo 1843623 2074747 := bstep (se 1 (by rfl) ⟨1556060, by rfl⟩ : syracuseStep 2074747 = 3112121) B3112121
theorem B1845371 : Blo 1843623 1845371 := bstep (se 1 (by rfl) ⟨1384028, by rfl⟩ : syracuseStep 1845371 = 2768057) B2768057
theorem B39880835 : Blo 1843623 39880835 := bstep (se 1 (by rfl) ⟨29910626, by rfl⟩ : syracuseStep 39880835 = 59821253) B59821253
theorem B1845423 : Blo 1843623 1845423 := bstep (se 1 (by rfl) ⟨1384067, by rfl⟩ : syracuseStep 1845423 = 2768135) B2768135
theorem B1845447 : Blo 1843623 1845447 := bstep (se 1 (by rfl) ⟨1384085, by rfl⟩ : syracuseStep 1845447 = 2768171) B2768171
theorem B1845467 : Blo 1843623 1845467 := bstep (se 1 (by rfl) ⟨1384100, by rfl⟩ : syracuseStep 1845467 = 2768201) B2768201
theorem B1845543 : Blo 1843623 1845543 := bstep (se 1 (by rfl) ⟨1384157, by rfl⟩ : syracuseStep 1845543 = 2768315) B2768315
theorem B1845583 : Blo 1843623 1845583 := bstep (se 1 (by rfl) ⟨1384187, by rfl⟩ : syracuseStep 1845583 = 2768375) B2768375
theorem B1845599 : Blo 1843623 1845599 := bstep (se 1 (by rfl) ⟨1384199, by rfl⟩ : syracuseStep 1845599 = 2768399) B2768399
theorem B5253619 : Blo 1843623 5253619 := bstep (se 1 (by rfl) ⟨3940214, by rfl⟩ : syracuseStep 5253619 = 7880429) B7880429
theorem B6228467 : Blo 1843623 6228467 := bstep (se 1 (by rfl) ⟨4671350, by rfl⟩ : syracuseStep 6228467 = 9342701) B9342701
theorem B11823641 : Blo 1843623 11823641 := bstep (se 2 (by rfl) ⟨4433865, by rfl⟩ : syracuseStep 11823641 = 8867731) B8867731
theorem B14961185 : Blo 1843623 14961185 := bstep (se 2 (by rfl) ⟨5610444, by rfl⟩ : syracuseStep 14961185 = 11220889) B11220889
theorem B2075215 : Blo 1843623 2075215 := bstep (se 1 (by rfl) ⟨1556411, by rfl⟩ : syracuseStep 2075215 = 3112823) B3112823
theorem B37849801 : Blo 1843623 37849801 := bstep (se 2 (by rfl) ⟨14193675, by rfl⟩ : syracuseStep 37849801 = 28387351) B28387351
theorem B3738463 : Blo 1843623 3738463 := bstep (se 1 (by rfl) ⟨2803847, by rfl⟩ : syracuseStep 3738463 = 5607695) B5607695
theorem B6646703 : Blo 1843623 6646703 := bstep (se 1 (by rfl) ⟨4985027, by rfl⟩ : syracuseStep 6646703 = 9970055) B9970055
theorem B2075611 : Blo 1843623 2075611 := bstep (se 1 (by rfl) ⟨1556708, by rfl⟩ : syracuseStep 2075611 = 3113417) B3113417
theorem B4148243 : Blo 1843623 4148243 := bstep (se 1 (by rfl) ⟨3111182, by rfl⟩ : syracuseStep 4148243 = 6222365) B6222365
theorem B6827179 : Blo 1843623 6827179 := bstep (se 1 (by rfl) ⟨5120384, by rfl⟩ : syracuseStep 6827179 = 10240769) B10240769
theorem B4148585 : Blo 1843623 4148585 := bstep (se 2 (by rfl) ⟨1555719, by rfl⟩ : syracuseStep 4148585 = 3111439) B3111439
theorem B6647165 : Blo 1843623 6647165 := bstep (se 3 (by rfl) ⟨1246343, by rfl⟩ : syracuseStep 6647165 = 2492687) B2492687
theorem B2076079 : Blo 1843623 2076079 := bstep (se 1 (by rfl) ⟨1557059, by rfl⟩ : syracuseStep 2076079 = 3114119) B3114119
theorem B5910155 : Blo 1843623 5910155 := bstep (se 1 (by rfl) ⟨4432616, by rfl⟩ : syracuseStep 5910155 = 8865233) B8865233
theorem B3501767 : Blo 1843623 3501767 := bstep (se 1 (by rfl) ⟨2626325, by rfl⟩ : syracuseStep 3501767 = 5252651) B5252651
theorem B8867693 : Blo 1843623 8867693 := bstep (se 3 (by rfl) ⟨1662692, by rfl⟩ : syracuseStep 8867693 = 3325385) B3325385
theorem B4149179 : Blo 1843623 4149179 := bstep (se 1 (by rfl) ⟨3111884, by rfl⟩ : syracuseStep 4149179 = 6223769) B6223769
theorem B4149305 : Blo 1843623 4149305 := bstep (se 2 (by rfl) ⟨1555989, by rfl⟩ : syracuseStep 4149305 = 3111979) B3111979
theorem B4206649 : Blo 1843623 4206649 := bstep (se 2 (by rfl) ⟨1577493, by rfl⟩ : syracuseStep 4206649 = 3154987) B3154987
theorem B5255225 : Blo 1843623 5255225 := bstep (se 2 (by rfl) ⟨1970709, by rfl⟩ : syracuseStep 5255225 = 3941419) B3941419
theorem B29904977 : Blo 1843623 29904977 := bstep (se 2 (by rfl) ⟨11214366, by rfl⟩ : syracuseStep 29904977 = 22428733) B22428733
theorem B3739745 : Blo 1843623 3739745 := bstep (se 2 (by rfl) ⟨1402404, by rfl⟩ : syracuseStep 3739745 = 2804809) B2804809
theorem B3502291 : Blo 1843623 3502291 := bstep (se 1 (by rfl) ⟨2626718, by rfl⟩ : syracuseStep 3502291 = 5253437) B5253437
theorem B7098749 : Blo 1843623 7098749 := bstep (se 3 (by rfl) ⟨1331015, by rfl⟩ : syracuseStep 7098749 = 2662031) B2662031
theorem B4149647 : Blo 1843623 4149647 := bstep (se 1 (by rfl) ⟨3112235, by rfl⟩ : syracuseStep 4149647 = 6224471) B6224471
theorem B5255567 : Blo 1843623 5255567 := bstep (se 1 (by rfl) ⟨3941675, by rfl⟩ : syracuseStep 5255567 = 7883351) B7883351
theorem B3502511 : Blo 1843623 3502511 := bstep (se 1 (by rfl) ⟨2626883, by rfl⟩ : syracuseStep 3502511 = 5253767) B5253767
theorem B4207067 : Blo 1843623 4207067 := bstep (se 1 (by rfl) ⟨3155300, by rfl⟩ : syracuseStep 4207067 = 6310601) B6310601
theorem B3322387 : Blo 1843623 3322387 := bstep (se 1 (by rfl) ⟨2491790, by rfl⟩ : syracuseStep 3322387 = 4983581) B4983581
theorem B17723927 : Blo 1843623 17723927 := bstep (se 1 (by rfl) ⟨13292945, by rfl⟩ : syracuseStep 17723927 = 26585891) B26585891
theorem B25252469 : Blo 1843623 25252469 := bstep (se 5 (by rfl) ⟨1183709, by rfl⟩ : syracuseStep 25252469 = 2367419) B2367419
theorem B2765435 : Blo 1843623 2765435 := bstep (se 1 (by rfl) ⟨2074076, by rfl⟩ : syracuseStep 2765435 = 4148153) B4148153
theorem B8418001 : Blo 1843623 8418001 := bstep (se 2 (by rfl) ⟨3156750, by rfl⟩ : syracuseStep 8418001 = 6313501) B6313501
theorem B4149971 : Blo 1843623 4149971 := bstep (se 1 (by rfl) ⟨3112478, by rfl⟩ : syracuseStep 4149971 = 6224957) B6224957
theorem B2765561 : Blo 1843623 2765561 := bstep (se 2 (by rfl) ⟨1037085, by rfl⟩ : syracuseStep 2765561 = 2074171) B2074171
theorem B6222635 : Blo 1843623 6222635 := bstep (se 1 (by rfl) ⟨4666976, by rfl⟩ : syracuseStep 6222635 = 9333953) B9333953
theorem B3502921 : Blo 1843623 3502921 := bstep (se 2 (by rfl) ⟨1313595, by rfl⟩ : syracuseStep 3502921 = 2627191) B2627191
theorem B2765663 : Blo 1843623 2765663 := bstep (se 1 (by rfl) ⟨2074247, by rfl⟩ : syracuseStep 2765663 = 4148495) B4148495
theorem B2765675 : Blo 1843623 2765675 := bstep (se 1 (by rfl) ⟨2074256, by rfl⟩ : syracuseStep 2765675 = 4148513) B4148513
theorem B7000951 : Blo 1843623 7000951 := bstep (se 1 (by rfl) ⟨5250713, by rfl⟩ : syracuseStep 7000951 = 10501427) B10501427
theorem B9335735 : Blo 1843623 9335735 := bstep (se 1 (by rfl) ⟨7001801, by rfl⟩ : syracuseStep 9335735 = 14003603) B14003603
theorem B5608379 : Blo 1843623 5608379 := bstep (se 1 (by rfl) ⟨4206284, by rfl⟩ : syracuseStep 5608379 = 8412569) B8412569
theorem B6222905 : Blo 1843623 6222905 := bstep (se 2 (by rfl) ⟨2333589, by rfl⟩ : syracuseStep 6222905 = 4667179) B4667179
theorem B2765903 : Blo 1843623 2765903 := bstep (se 1 (by rfl) ⟨2074427, by rfl⟩ : syracuseStep 2765903 = 4148855) B4148855
theorem B7877711 : Blo 1843623 7877711 := bstep (se 1 (by rfl) ⟨5908283, by rfl⟩ : syracuseStep 7877711 = 11816567) B11816567
theorem B5911667 : Blo 1843623 5911667 := bstep (se 1 (by rfl) ⟨4433750, by rfl⟩ : syracuseStep 5911667 = 8867501) B8867501
theorem B2766023 : Blo 1843623 2766023 := bstep (se 1 (by rfl) ⟨2074517, by rfl⟩ : syracuseStep 2766023 = 4149035) B4149035
theorem B2766185 : Blo 1843623 2766185 := bstep (se 2 (by rfl) ⟨1037319, by rfl⟩ : syracuseStep 2766185 = 2074639) B2074639
theorem B2954603 : Blo 1843623 2954603 := bstep (se 1 (by rfl) ⟨2215952, by rfl⟩ : syracuseStep 2954603 = 4431905) B4431905
theorem B21009779 : Blo 1843623 21009779 := bstep (se 1 (by rfl) ⟨15757334, by rfl⟩ : syracuseStep 21009779 = 31514669) B31514669
theorem B6223229 : Blo 1843623 6223229 := bstep (se 3 (by rfl) ⟨1166855, by rfl⟩ : syracuseStep 6223229 = 2333711) B2333711
theorem B2766263 : Blo 1843623 2766263 := bstep (se 1 (by rfl) ⟨2074697, by rfl⟩ : syracuseStep 2766263 = 4149395) B4149395
theorem B119707085 : Blo 1843623 119707085 := bstep (se 3 (by rfl) ⟨22445078, by rfl⟩ : syracuseStep 119707085 = 44890157) B44890157
theorem B2766299 : Blo 1843623 2766299 := bstep (se 1 (by rfl) ⟨2074724, by rfl⟩ : syracuseStep 2766299 = 4149449) B4149449
theorem B2627111 : Blo 1843623 2627111 := bstep (se 1 (by rfl) ⟨1970333, by rfl⟩ : syracuseStep 2627111 = 3940667) B3940667
theorem B13293179 : Blo 1843623 13293179 := bstep (se 1 (by rfl) ⟨9969884, by rfl⟩ : syracuseStep 13293179 = 19939769) B19939769
theorem B4150907 : Blo 1843623 4150907 := bstep (se 1 (by rfl) ⟨3113180, by rfl⟩ : syracuseStep 4150907 = 6226361) B6226361
theorem B6223499 : Blo 1843623 6223499 := bstep (se 1 (by rfl) ⟨4667624, by rfl⟩ : syracuseStep 6223499 = 9335249) B9335249
theorem B4667129 : Blo 1843623 4667129 := bstep (se 2 (by rfl) ⟨1750173, by rfl⟩ : syracuseStep 4667129 = 3500347) B3500347
theorem B4151033 : Blo 1843623 4151033 := bstep (se 2 (by rfl) ⟨1556637, by rfl⟩ : syracuseStep 4151033 = 3113275) B3113275
theorem B53196587 : Blo 1843623 53196587 := bstep (se 1 (by rfl) ⟨39897440, by rfl⟩ : syracuseStep 53196587 = 79794881) B79794881
theorem B7001923 : Blo 1843623 7001923 := bstep (se 1 (by rfl) ⟨5251442, by rfl⟩ : syracuseStep 7001923 = 10502885) B10502885
theorem B2766767 : Blo 1843623 2766767 := bstep (se 1 (by rfl) ⟨2075075, by rfl⟩ : syracuseStep 2766767 = 4150151) B4150151
theorem B4151303 : Blo 1843623 4151303 := bstep (se 1 (by rfl) ⟨3113477, by rfl⟩ : syracuseStep 4151303 = 6226955) B6226955
theorem B2766857 : Blo 1843623 2766857 := bstep (se 2 (by rfl) ⟨1037571, by rfl⟩ : syracuseStep 2766857 = 2075143) B2075143
theorem B2766887 : Blo 1843623 2766887 := bstep (se 1 (by rfl) ⟨2075165, by rfl⟩ : syracuseStep 2766887 = 4150331) B4150331
theorem B69179437 : Blo 1843623 69179437 := bstep (se 3 (by rfl) ⟨12971144, by rfl⟩ : syracuseStep 69179437 = 25942289) B25942289
theorem B4151375 : Blo 1843623 4151375 := bstep (se 1 (by rfl) ⟨3113531, by rfl⟩ : syracuseStep 4151375 = 6227063) B6227063
theorem B15169625 : Blo 1843623 15169625 := bstep (se 2 (by rfl) ⟨5688609, by rfl⟩ : syracuseStep 15169625 = 11377219) B11377219
theorem B3324001 : Blo 1843623 3324001 := bstep (se 2 (by rfl) ⟨1246500, by rfl⟩ : syracuseStep 3324001 = 2493001) B2493001
theorem B7002227 : Blo 1843623 7002227 := bstep (se 1 (by rfl) ⟨5251670, by rfl⟩ : syracuseStep 7002227 = 10503341) B10503341
theorem B2766971 : Blo 1843623 2766971 := bstep (se 1 (by rfl) ⟨2075228, by rfl⟩ : syracuseStep 2766971 = 4150457) B4150457
theorem B56776949 : Blo 1843623 56776949 := bstep (se 5 (by rfl) ⟨2661419, by rfl⟩ : syracuseStep 56776949 = 5322839) B5322839
theorem B2767097 : Blo 1843623 2767097 := bstep (se 2 (by rfl) ⟨1037661, by rfl⟩ : syracuseStep 2767097 = 2075323) B2075323
theorem B14014781 : Blo 1843623 14014781 := bstep (se 3 (by rfl) ⟨2627771, by rfl⟩ : syracuseStep 14014781 = 5255543) B5255543
theorem B3324233 : Blo 1843623 3324233 := bstep (se 2 (by rfl) ⟨1246587, by rfl⟩ : syracuseStep 3324233 = 2493175) B2493175
theorem B2767199 : Blo 1843623 2767199 := bstep (se 1 (by rfl) ⟨2075399, by rfl⟩ : syracuseStep 2767199 = 4150799) B4150799
theorem B9337193 : Blo 1843623 9337193 := bstep (se 2 (by rfl) ⟨3501447, by rfl⟩ : syracuseStep 9337193 = 7002895) B7002895
theorem B2767211 : Blo 1843623 2767211 := bstep (se 1 (by rfl) ⟨2075408, by rfl⟩ : syracuseStep 2767211 = 4150817) B4150817
theorem B4667777 : Blo 1843623 4667777 := bstep (se 2 (by rfl) ⟨1750416, by rfl⟩ : syracuseStep 4667777 = 3500833) B3500833
theorem B45504899 : Blo 1843623 45504899 := bstep (se 1 (by rfl) ⟨34128674, by rfl⟩ : syracuseStep 45504899 = 68257349) B68257349
theorem B3111311 : Blo 1843623 3111311 := bstep (se 1 (by rfl) ⟨2333483, by rfl⟩ : syracuseStep 3111311 = 4666967) B4666967
theorem B4151771 : Blo 1843623 4151771 := bstep (se 1 (by rfl) ⟨3113828, by rfl⟩ : syracuseStep 4151771 = 6227657) B6227657
theorem B6224417 : Blo 1843623 6224417 := bstep (se 2 (by rfl) ⟨2334156, by rfl⟩ : syracuseStep 6224417 = 4668313) B4668313
theorem B7002683 : Blo 1843623 7002683 := bstep (se 1 (by rfl) ⟨5252012, by rfl⟩ : syracuseStep 7002683 = 10504025) B10504025
theorem B2767439 : Blo 1843623 2767439 := bstep (se 1 (by rfl) ⟨2075579, by rfl⟩ : syracuseStep 2767439 = 4151159) B4151159
theorem B3111547 : Blo 1843623 3111547 := bstep (se 1 (by rfl) ⟨2333660, by rfl⟩ : syracuseStep 3111547 = 4667321) B4667321
theorem B4209275 : Blo 1843623 4209275 := bstep (se 1 (by rfl) ⟨3156956, by rfl⟩ : syracuseStep 4209275 = 6313913) B6313913
theorem B2767559 : Blo 1843623 2767559 := bstep (se 1 (by rfl) ⟨2075669, by rfl⟩ : syracuseStep 2767559 = 4151339) B4151339
theorem B6224633 : Blo 1843623 6224633 := bstep (se 2 (by rfl) ⟨2334237, by rfl⟩ : syracuseStep 6224633 = 4668475) B4668475
theorem B14957389 : Blo 1843623 14957389 := bstep (se 3 (by rfl) ⟨2804510, by rfl⟩ : syracuseStep 14957389 = 5609021) B5609021
theorem B2767721 : Blo 1843623 2767721 := bstep (se 2 (by rfl) ⟨1037895, by rfl⟩ : syracuseStep 2767721 = 2075791) B2075791
theorem B72825713 : Blo 1843623 72825713 := bstep (se 2 (by rfl) ⟨27309642, by rfl⟩ : syracuseStep 72825713 = 54619285) B54619285
theorem B21592979 : Blo 1843623 21592979 := bstep (se 1 (by rfl) ⟨16194734, by rfl⟩ : syracuseStep 21592979 = 32389469) B32389469
theorem B11819951 : Blo 1843623 11819951 := bstep (se 1 (by rfl) ⟨8864963, by rfl⟩ : syracuseStep 11819951 = 17729927) B17729927
theorem B4152239 : Blo 1843623 4152239 := bstep (se 1 (by rfl) ⟨3114179, by rfl⟩ : syracuseStep 4152239 = 6228359) B6228359
theorem B2767799 : Blo 1843623 2767799 := bstep (se 1 (by rfl) ⟨2075849, by rfl⟩ : syracuseStep 2767799 = 4151699) B4151699
theorem B2767835 : Blo 1843623 2767835 := bstep (se 1 (by rfl) ⟨2075876, by rfl⟩ : syracuseStep 2767835 = 4151753) B4151753
theorem B6224903 : Blo 1843623 6224903 := bstep (se 1 (by rfl) ⟨4668677, by rfl⟩ : syracuseStep 6224903 = 9337355) B9337355
theorem B39894059 : Blo 1843623 39894059 := bstep (se 1 (by rfl) ⟨29920544, by rfl⟩ : syracuseStep 39894059 = 59841089) B59841089
theorem B44858447 : Blo 1843623 44858447 := bstep (se 1 (by rfl) ⟨33643835, by rfl⟩ : syracuseStep 44858447 = 67287671) B67287671
theorem B3325025 : Blo 1843623 3325025 := bstep (se 2 (by rfl) ⟨1246884, by rfl⟩ : syracuseStep 3325025 = 2493769) B2493769
theorem B6225011 : Blo 1843623 6225011 := bstep (se 1 (by rfl) ⟨4668758, by rfl⟩ : syracuseStep 6225011 = 9337517) B9337517
theorem B11213977 : Blo 1843623 11213977 := bstep (se 2 (by rfl) ⟨4205241, by rfl⟩ : syracuseStep 11213977 = 8410483) B8410483
theorem B4668587 : Blo 1843623 4668587 := bstep (se 1 (by rfl) ⟨3501440, by rfl⟩ : syracuseStep 4668587 = 7002881) B7002881
theorem B4152491 : Blo 1843623 4152491 := bstep (se 1 (by rfl) ⟨3114368, by rfl⟩ : syracuseStep 4152491 = 6228737) B6228737
theorem B14007491 : Blo 1843623 14007491 := bstep (se 1 (by rfl) ⟨10505618, by rfl⟩ : syracuseStep 14007491 = 21011237) B21011237
theorem B28392727 : Blo 1843623 28392727 := bstep (se 1 (by rfl) ⟨21294545, by rfl⟩ : syracuseStep 28392727 = 42589091) B42589091
theorem B3792233 : Blo 1843623 3792233 := bstep (se 2 (by rfl) ⟨1422087, by rfl⟩ : syracuseStep 3792233 = 2844175) B2844175
theorem B6225281 : Blo 1843623 6225281 := bstep (se 2 (by rfl) ⟨2334480, by rfl⟩ : syracuseStep 6225281 = 4668961) B4668961
theorem B2768303 : Blo 1843623 2768303 := bstep (se 1 (by rfl) ⟨2076227, by rfl⟩ : syracuseStep 2768303 = 4152455) B4152455
theorem B3112411 : Blo 1843623 3112411 := bstep (se 1 (by rfl) ⟨2334308, by rfl⟩ : syracuseStep 3112411 = 4668617) B4668617
theorem B4988425 : Blo 1843623 4988425 := bstep (se 2 (by rfl) ⟨1870659, by rfl⟩ : syracuseStep 4988425 = 3741319) B3741319
theorem B2768393 : Blo 1843623 2768393 := bstep (se 2 (by rfl) ⟨1038147, by rfl⟩ : syracuseStep 2768393 = 2076295) B2076295
theorem B4734503 : Blo 1843623 4734503 := bstep (se 1 (by rfl) ⟨3550877, by rfl⟩ : syracuseStep 4734503 = 7101755) B7101755
theorem B2768423 : Blo 1843623 2768423 := bstep (se 1 (by rfl) ⟨2076317, by rfl⟩ : syracuseStep 2768423 = 4152635) B4152635
theorem B11820667 : Blo 1843623 11820667 := bstep (se 1 (by rfl) ⟨8865500, by rfl⟩ : syracuseStep 11820667 = 17731001) B17731001
theorem B9461387 : Blo 1843623 9461387 := bstep (se 1 (by rfl) ⟨7096040, by rfl⟩ : syracuseStep 9461387 = 14192081) B14192081
theorem B11214659 : Blo 1843623 11214659 := bstep (se 1 (by rfl) ⟨8410994, by rfl⟩ : syracuseStep 11214659 = 16821989) B16821989
theorem B10510175 : Blo 1843623 10510175 := bstep (se 1 (by rfl) ⟨7882631, by rfl⟩ : syracuseStep 10510175 = 15765263) B15765263
theorem B5250977 : Blo 1843623 5250977 := bstep (se 2 (by rfl) ⟨1969116, by rfl⟩ : syracuseStep 5250977 = 3938233) B3938233
theorem B2334683 : Blo 1843623 2334683 := bstep (se 1 (by rfl) ⟨1751012, by rfl⟩ : syracuseStep 2334683 = 3502025) B3502025
theorem B6225929 : Blo 1843623 6225929 := bstep (se 2 (by rfl) ⟨2334723, by rfl⟩ : syracuseStep 6225929 = 4669447) B4669447
theorem B4432001 : Blo 1843623 4432001 := bstep (se 2 (by rfl) ⟨1662000, by rfl⟩ : syracuseStep 4432001 = 3324001) B3324001
theorem B4669721 : Blo 1843623 4669721 := bstep (se 2 (by rfl) ⟨1751145, by rfl⟩ : syracuseStep 4669721 = 3502291) B3502291
theorem B2335007 : Blo 1843623 2335007 := bstep (se 1 (by rfl) ⟨1751255, by rfl⟩ : syracuseStep 2335007 = 3502511) B3502511
theorem B16834979 : Blo 1843623 16834979 := bstep (se 1 (by rfl) ⟨12626234, by rfl⟩ : syracuseStep 16834979 = 25252469) B25252469
theorem B1843623 : Blo 1843623 1843623 := bstep (se 1 (by rfl) ⟨1382717, by rfl⟩ : syracuseStep 1843623 = 2765435) B2765435
theorem B3113383 : Blo 1843623 3113383 := bstep (se 1 (by rfl) ⟨2335037, by rfl⟩ : syracuseStep 3113383 = 4670075) B4670075
theorem B1843707 : Blo 1843623 1843707 := bstep (se 1 (by rfl) ⟨1382780, by rfl⟩ : syracuseStep 1843707 = 2765561) B2765561
theorem B1843775 : Blo 1843623 1843775 := bstep (se 1 (by rfl) ⟨1382831, by rfl⟩ : syracuseStep 1843775 = 2765663) B2765663
theorem B1843783 : Blo 1843623 1843783 := bstep (se 1 (by rfl) ⟨1382837, by rfl⟩ : syracuseStep 1843783 = 2765675) B2765675
theorem B3113545 : Blo 1843623 3113545 := bstep (se 2 (by rfl) ⟨1167579, by rfl⟩ : syracuseStep 3113545 = 2335159) B2335159
theorem B3113579 : Blo 1843623 3113579 := bstep (se 1 (by rfl) ⟨2335184, by rfl⟩ : syracuseStep 3113579 = 4670369) B4670369
theorem B7004825 : Blo 1843623 7004825 := bstep (se 2 (by rfl) ⟨2626809, by rfl⟩ : syracuseStep 7004825 = 5253619) B5253619
theorem B1843935 : Blo 1843623 1843935 := bstep (se 1 (by rfl) ⟨1382951, by rfl⟩ : syracuseStep 1843935 = 2765903) B2765903
theorem B5251807 : Blo 1843623 5251807 := bstep (se 1 (by rfl) ⟨3938855, by rfl⟩ : syracuseStep 5251807 = 7877711) B7877711
theorem B3941111 : Blo 1843623 3941111 := bstep (se 1 (by rfl) ⟨2955833, by rfl⟩ : syracuseStep 3941111 = 5911667) B5911667
theorem B1844015 : Blo 1843623 1844015 := bstep (se 1 (by rfl) ⟨1383011, by rfl⟩ : syracuseStep 1844015 = 2766023) B2766023
theorem B33653555 : Blo 1843623 33653555 := bstep (se 1 (by rfl) ⟨25240166, by rfl⟩ : syracuseStep 33653555 = 50480333) B50480333
theorem B1844123 : Blo 1843623 1844123 := bstep (se 1 (by rfl) ⟨1383092, by rfl⟩ : syracuseStep 1844123 = 2766185) B2766185
theorem B11224001 : Blo 1843623 11224001 := bstep (se 2 (by rfl) ⟨4209000, by rfl⟩ : syracuseStep 11224001 = 8418001) B8418001
theorem B1844175 : Blo 1843623 1844175 := bstep (se 1 (by rfl) ⟨1383131, by rfl⟩ : syracuseStep 1844175 = 2766263) B2766263
theorem B119669723 : Blo 1843623 119669723 := bstep (se 1 (by rfl) ⟨89752292, by rfl⟩ : syracuseStep 119669723 = 179504585) B179504585
theorem B8864731 : Blo 1843623 8864731 := bstep (se 1 (by rfl) ⟨6648548, by rfl⟩ : syracuseStep 8864731 = 13297097) B13297097
theorem B1844199 : Blo 1843623 1844199 := bstep (se 1 (by rfl) ⟨1383149, by rfl⟩ : syracuseStep 1844199 = 2766299) B2766299
theorem B4670561 : Blo 1843623 4670561 := bstep (se 2 (by rfl) ⟨1751460, by rfl⟩ : syracuseStep 4670561 = 3502921) B3502921
theorem B35464391 : Blo 1843623 35464391 := bstep (se 1 (by rfl) ⟨26598293, by rfl⟩ : syracuseStep 35464391 = 53196587) B53196587
theorem B1844511 : Blo 1843623 1844511 := bstep (se 1 (by rfl) ⟨1383383, by rfl⟩ : syracuseStep 1844511 = 2766767) B2766767
theorem B1844571 : Blo 1843623 1844571 := bstep (se 1 (by rfl) ⟨1383428, by rfl⟩ : syracuseStep 1844571 = 2766857) B2766857
theorem B1844591 : Blo 1843623 1844591 := bstep (se 1 (by rfl) ⟨1383443, by rfl⟩ : syracuseStep 1844591 = 2766887) B2766887
theorem B1844647 : Blo 1843623 1844647 := bstep (se 1 (by rfl) ⟨1383485, by rfl⟩ : syracuseStep 1844647 = 2766971) B2766971
theorem B7005629 : Blo 1843623 7005629 := bstep (se 3 (by rfl) ⟨1313555, by rfl⟩ : syracuseStep 7005629 = 2627111) B2627111
theorem B1844731 : Blo 1843623 1844731 := bstep (se 1 (by rfl) ⟨1383548, by rfl⟩ : syracuseStep 1844731 = 2767097) B2767097
theorem B14951969 : Blo 1843623 14951969 := bstep (se 2 (by rfl) ⟨5606988, by rfl⟩ : syracuseStep 14951969 = 11213977) B11213977
theorem B9102905 : Blo 1843623 9102905 := bstep (se 2 (by rfl) ⟨3413589, by rfl⟩ : syracuseStep 9102905 = 6827179) B6827179
theorem B1844799 : Blo 1843623 1844799 := bstep (se 1 (by rfl) ⟨1383599, by rfl⟩ : syracuseStep 1844799 = 2767199) B2767199
theorem B1844807 : Blo 1843623 1844807 := bstep (se 1 (by rfl) ⟨1383605, by rfl⟩ : syracuseStep 1844807 = 2767211) B2767211
theorem B30336599 : Blo 1843623 30336599 := bstep (se 1 (by rfl) ⟨22752449, by rfl⟩ : syracuseStep 30336599 = 45504899) B45504899
theorem B2074207 : Blo 1843623 2074207 := bstep (se 1 (by rfl) ⟨1555655, by rfl⟩ : syracuseStep 2074207 = 3111311) B3111311
theorem B7882427 : Blo 1843623 7882427 := bstep (se 1 (by rfl) ⟨5911820, by rfl⟩ : syracuseStep 7882427 = 11823641) B11823641
theorem B37856969 : Blo 1843623 37856969 := bstep (se 2 (by rfl) ⟨14196363, by rfl⟩ : syracuseStep 37856969 = 28392727) B28392727
theorem B1844959 : Blo 1843623 1844959 := bstep (se 1 (by rfl) ⟨1383719, by rfl⟩ : syracuseStep 1844959 = 2767439) B2767439
theorem B1845039 : Blo 1843623 1845039 := bstep (se 1 (by rfl) ⟨1383779, by rfl⟩ : syracuseStep 1845039 = 2767559) B2767559
theorem B1845147 : Blo 1843623 1845147 := bstep (se 1 (by rfl) ⟨1383860, by rfl⟩ : syracuseStep 1845147 = 2767721) B2767721
theorem B14395319 : Blo 1843623 14395319 := bstep (se 1 (by rfl) ⟨10796489, by rfl⟩ : syracuseStep 14395319 = 21592979) B21592979
theorem B1845199 : Blo 1843623 1845199 := bstep (se 1 (by rfl) ⟨1383899, by rfl⟩ : syracuseStep 1845199 = 2767799) B2767799
theorem B1845223 : Blo 1843623 1845223 := bstep (se 1 (by rfl) ⟨1383917, by rfl⟩ : syracuseStep 1845223 = 2767835) B2767835
theorem B6646013 : Blo 1843623 6646013 := bstep (se 3 (by rfl) ⟨1246127, by rfl⟩ : syracuseStep 6646013 = 2492255) B2492255
theorem B1845535 : Blo 1843623 1845535 := bstep (se 1 (by rfl) ⟨1384151, by rfl⟩ : syracuseStep 1845535 = 2768303) B2768303
theorem B1845595 : Blo 1843623 1845595 := bstep (se 1 (by rfl) ⟨1384196, by rfl⟩ : syracuseStep 1845595 = 2768393) B2768393
theorem B3156335 : Blo 1843623 3156335 := bstep (se 1 (by rfl) ⟨2367251, by rfl⟩ : syracuseStep 3156335 = 4734503) B4734503
theorem B1845615 : Blo 1843623 1845615 := bstep (se 1 (by rfl) ⟨1384211, by rfl⟩ : syracuseStep 1845615 = 2768423) B2768423
theorem B7006783 : Blo 1843623 7006783 := bstep (se 1 (by rfl) ⟨5255087, by rfl⟩ : syracuseStep 7006783 = 10510175) B10510175
theorem B3500651 : Blo 1843623 3500651 := bstep (se 1 (by rfl) ⟨2625488, by rfl⟩ : syracuseStep 3500651 = 5250977) B5250977
theorem B2075359 : Blo 1843623 2075359 := bstep (se 1 (by rfl) ⟨1556519, by rfl⟩ : syracuseStep 2075359 = 3113039) B3113039
theorem B2493163 : Blo 1843623 2493163 := bstep (se 1 (by rfl) ⟨1869872, by rfl⟩ : syracuseStep 2493163 = 3739745) B3739745
theorem B7875319 : Blo 1843623 7875319 := bstep (se 1 (by rfl) ⟨5906489, by rfl⟩ : syracuseStep 7875319 = 11812979) B11812979
theorem B9333629 : Blo 1843623 9333629 := bstep (se 3 (by rfl) ⟨1750055, by rfl⟩ : syracuseStep 9333629 = 3500111) B3500111
theorem B2804711 : Blo 1843623 2804711 := bstep (se 1 (by rfl) ⟨2103533, by rfl⟩ : syracuseStep 2804711 = 4207067) B4207067
theorem B11815951 : Blo 1843623 11815951 := bstep (se 1 (by rfl) ⟨8861963, by rfl⟩ : syracuseStep 11815951 = 17723927) B17723927
theorem B4148423 : Blo 1843623 4148423 := bstep (se 1 (by rfl) ⟨3111317, by rfl⟩ : syracuseStep 4148423 = 6222635) B6222635
theorem B2075935 : Blo 1843623 2075935 := bstep (se 1 (by rfl) ⟨1556951, by rfl⟩ : syracuseStep 2075935 = 3113903) B3113903
theorem B4148603 : Blo 1843623 4148603 := bstep (se 1 (by rfl) ⟨3111452, by rfl⟩ : syracuseStep 4148603 = 6222905) B6222905
theorem B7876055 : Blo 1843623 7876055 := bstep (se 1 (by rfl) ⟨5907041, by rfl⟩ : syracuseStep 7876055 = 11814083) B11814083
theorem B4148729 : Blo 1843623 4148729 := bstep (se 2 (by rfl) ⟨1555773, by rfl⟩ : syracuseStep 4148729 = 3111547) B3111547
theorem B2076223 : Blo 1843623 2076223 := bstep (se 1 (by rfl) ⟨1557167, by rfl⟩ : syracuseStep 2076223 = 3114335) B3114335
theorem B4148819 : Blo 1843623 4148819 := bstep (se 1 (by rfl) ⟨3111614, by rfl⟩ : syracuseStep 4148819 = 6223229) B6223229
theorem B50466401 : Blo 1843623 50466401 := bstep (se 2 (by rfl) ⟨18924900, by rfl⟩ : syracuseStep 50466401 = 37849801) B37849801
theorem B4148999 : Blo 1843623 4148999 := bstep (se 1 (by rfl) ⟨3111749, by rfl⟩ : syracuseStep 4148999 = 6223499) B6223499
theorem B19943185 : Blo 1843623 19943185 := bstep (se 2 (by rfl) ⟨7478694, by rfl⟩ : syracuseStep 19943185 = 14957389) B14957389
theorem B9334601 : Blo 1843623 9334601 := bstep (se 2 (by rfl) ⟨3500475, by rfl⟩ : syracuseStep 9334601 = 7000951) B7000951
theorem B10113083 : Blo 1843623 10113083 := bstep (se 1 (by rfl) ⟨7584812, by rfl⟩ : syracuseStep 10113083 = 15169625) B15169625
theorem B26587223 : Blo 1843623 26587223 := bstep (se 1 (by rfl) ⟨19940417, by rfl⟩ : syracuseStep 26587223 = 39880835) B39880835
theorem B37851299 : Blo 1843623 37851299 := bstep (se 1 (by rfl) ⟨28388474, by rfl⟩ : syracuseStep 37851299 = 56776949) B56776949
theorem B9343187 : Blo 1843623 9343187 := bstep (se 1 (by rfl) ⟨7007390, by rfl⟩ : syracuseStep 9343187 = 14014781) B14014781
theorem B2216155 : Blo 1843623 2216155 := bstep (se 1 (by rfl) ⟨1662116, by rfl⟩ : syracuseStep 2216155 = 3324233) B3324233
theorem B4149611 : Blo 1843623 4149611 := bstep (se 1 (by rfl) ⟨3112208, by rfl⟩ : syracuseStep 4149611 = 6224417) B6224417
theorem B9974123 : Blo 1843623 9974123 := bstep (se 1 (by rfl) ⟨7480592, by rfl⟩ : syracuseStep 9974123 = 14961185) B14961185
theorem B2806183 : Blo 1843623 2806183 := bstep (se 1 (by rfl) ⟨2104637, by rfl⟩ : syracuseStep 2806183 = 4209275) B4209275
theorem B21017069 : Blo 1843623 21017069 := bstep (se 3 (by rfl) ⟨3940700, by rfl⟩ : syracuseStep 21017069 = 7881401) B7881401
theorem B70898165 : Blo 1843623 70898165 := bstep (se 5 (by rfl) ⟨3323351, by rfl⟩ : syracuseStep 70898165 = 6646703) B6646703
theorem B4149755 : Blo 1843623 4149755 := bstep (se 1 (by rfl) ⟨3112316, by rfl⟩ : syracuseStep 4149755 = 6224633) B6224633
theorem B48550475 : Blo 1843623 48550475 := bstep (se 1 (by rfl) ⟨36412856, by rfl⟩ : syracuseStep 48550475 = 72825713) B72825713
theorem B4149881 : Blo 1843623 4149881 := bstep (se 2 (by rfl) ⟨1556205, by rfl⟩ : syracuseStep 4149881 = 3112411) B3112411
theorem B4149935 : Blo 1843623 4149935 := bstep (se 1 (by rfl) ⟨3112451, by rfl⟩ : syracuseStep 4149935 = 6224903) B6224903
theorem B2765495 : Blo 1843623 2765495 := bstep (se 1 (by rfl) ⟨2074121, by rfl⟩ : syracuseStep 2765495 = 4148243) B4148243
theorem B26596039 : Blo 1843623 26596039 := bstep (se 1 (by rfl) ⟨19947029, by rfl⟩ : syracuseStep 26596039 = 39894059) B39894059
theorem B29905631 : Blo 1843623 29905631 := bstep (se 1 (by rfl) ⟨22429223, by rfl⟩ : syracuseStep 29905631 = 44858447) B44858447
theorem B2216683 : Blo 1843623 2216683 := bstep (se 1 (by rfl) ⟨1662512, by rfl⟩ : syracuseStep 2216683 = 3325025) B3325025
theorem B4150007 : Blo 1843623 4150007 := bstep (se 1 (by rfl) ⟨3112505, by rfl⟩ : syracuseStep 4150007 = 6225011) B6225011
theorem B29905757 : Blo 1843623 29905757 := bstep (se 3 (by rfl) ⟨5607329, by rfl⟩ : syracuseStep 29905757 = 11214659) B11214659
theorem B2765723 : Blo 1843623 2765723 := bstep (se 1 (by rfl) ⟨2074292, by rfl⟩ : syracuseStep 2765723 = 4148585) B4148585
theorem B2528155 : Blo 1843623 2528155 := bstep (se 1 (by rfl) ⟨1896116, by rfl⟩ : syracuseStep 2528155 = 3792233) B3792233
theorem B4150187 : Blo 1843623 4150187 := bstep (se 1 (by rfl) ⟨3112640, by rfl⟩ : syracuseStep 4150187 = 6225281) B6225281
theorem B9335897 : Blo 1843623 9335897 := bstep (se 2 (by rfl) ⟨3500961, by rfl⟩ : syracuseStep 9335897 = 7001923) B7001923
theorem B14955677 : Blo 1843623 14955677 := bstep (se 3 (by rfl) ⟨2804189, by rfl⟩ : syracuseStep 14955677 = 5608379) B5608379
theorem B5911795 : Blo 1843623 5911795 := bstep (se 1 (by rfl) ⟨4433846, by rfl⟩ : syracuseStep 5911795 = 8867693) B8867693
theorem B2766119 : Blo 1843623 2766119 := bstep (se 1 (by rfl) ⟨2074589, by rfl⟩ : syracuseStep 2766119 = 4149179) B4149179
theorem B2766203 : Blo 1843623 2766203 := bstep (se 1 (by rfl) ⟨2074652, by rfl⟩ : syracuseStep 2766203 = 4149305) B4149305
theorem B3503483 : Blo 1843623 3503483 := bstep (se 1 (by rfl) ⟨2627612, by rfl⟩ : syracuseStep 3503483 = 5255225) B5255225
theorem B19936651 : Blo 1843623 19936651 := bstep (se 1 (by rfl) ⟨14952488, by rfl⟩ : syracuseStep 19936651 = 29904977) B29904977
theorem B7476619 : Blo 1843623 7476619 := bstep (se 1 (by rfl) ⟨5607464, by rfl⟩ : syracuseStep 7476619 = 11214929) B11214929
theorem B92239249 : Blo 1843623 92239249 := bstep (se 2 (by rfl) ⟨34589718, by rfl⟩ : syracuseStep 92239249 = 69179437) B69179437
theorem B5608865 : Blo 1843623 5608865 := bstep (se 2 (by rfl) ⟨2103324, by rfl⟩ : syracuseStep 5608865 = 4206649) B4206649
theorem B4150727 : Blo 1843623 4150727 := bstep (se 1 (by rfl) ⟨3113045, by rfl⟩ : syracuseStep 4150727 = 6226091) B6226091
theorem B2766329 : Blo 1843623 2766329 := bstep (se 2 (by rfl) ⟨1037373, by rfl⟩ : syracuseStep 2766329 = 2074747) B2074747
theorem B4732499 : Blo 1843623 4732499 := bstep (se 1 (by rfl) ⟨3549374, by rfl⟩ : syracuseStep 4732499 = 7098749) B7098749
theorem B2766431 : Blo 1843623 2766431 := bstep (se 1 (by rfl) ⟨2074823, by rfl⟩ : syracuseStep 2766431 = 4149647) B4149647
theorem B3503711 : Blo 1843623 3503711 := bstep (se 1 (by rfl) ⟨2627783, by rfl⟩ : syracuseStep 3503711 = 5255567) B5255567
theorem B4151087 : Blo 1843623 4151087 := bstep (se 1 (by rfl) ⟨3113315, by rfl⟩ : syracuseStep 4151087 = 6226631) B6226631
theorem B2766647 : Blo 1843623 2766647 := bstep (se 1 (by rfl) ⟨2074985, by rfl⟩ : syracuseStep 2766647 = 4149971) B4149971
theorem B14014295 : Blo 1843623 14014295 := bstep (se 1 (by rfl) ⟨10510721, by rfl⟩ : syracuseStep 14014295 = 21021443) B21021443
theorem B6223823 : Blo 1843623 6223823 := bstep (se 1 (by rfl) ⟨4667867, by rfl⟩ : syracuseStep 6223823 = 9335735) B9335735
theorem B4429849 : Blo 1843623 4429849 := bstep (se 2 (by rfl) ⟨1661193, by rfl⟩ : syracuseStep 4429849 = 3322387) B3322387
theorem B2766953 : Blo 1843623 2766953 := bstep (se 2 (by rfl) ⟨1037607, by rfl⟩ : syracuseStep 2766953 = 2075215) B2075215
theorem B14006519 : Blo 1843623 14006519 := bstep (se 1 (by rfl) ⟨10504889, by rfl⟩ : syracuseStep 14006519 = 21009779) B21009779
theorem B7878941 : Blo 1843623 7878941 := bstep (se 3 (by rfl) ⟨1477301, by rfl⟩ : syracuseStep 7878941 = 2954603) B2954603
theorem B79804723 : Blo 1843623 79804723 := bstep (se 1 (by rfl) ⟨59853542, by rfl⟩ : syracuseStep 79804723 = 119707085) B119707085
theorem B4151663 : Blo 1843623 4151663 := bstep (se 1 (by rfl) ⟨3113747, by rfl⟩ : syracuseStep 4151663 = 6227495) B6227495
theorem B8862119 : Blo 1843623 8862119 := bstep (se 1 (by rfl) ⟨6646589, by rfl⟩ : syracuseStep 8862119 = 13293179) B13293179
theorem B2767271 : Blo 1843623 2767271 := bstep (se 1 (by rfl) ⟨2075453, by rfl⟩ : syracuseStep 2767271 = 4150907) B4150907
theorem B4151735 : Blo 1843623 4151735 := bstep (se 1 (by rfl) ⟨3113801, by rfl⟩ : syracuseStep 4151735 = 6227603) B6227603
theorem B3111419 : Blo 1843623 3111419 := bstep (se 1 (by rfl) ⟨2333564, by rfl⟩ : syracuseStep 3111419 = 4667129) B4667129
theorem B2767355 : Blo 1843623 2767355 := bstep (se 1 (by rfl) ⟨2075516, by rfl⟩ : syracuseStep 2767355 = 4151033) B4151033
theorem B4151879 : Blo 1843623 4151879 := bstep (se 1 (by rfl) ⟨3113909, by rfl⟩ : syracuseStep 4151879 = 6227819) B6227819
theorem B2955847 : Blo 1843623 2955847 := bstep (se 1 (by rfl) ⟨2216885, by rfl⟩ : syracuseStep 2955847 = 4433771) B4433771
theorem B4151915 : Blo 1843623 4151915 := bstep (se 1 (by rfl) ⟨3113936, by rfl⟩ : syracuseStep 4151915 = 6227873) B6227873
theorem B2767481 : Blo 1843623 2767481 := bstep (se 2 (by rfl) ⟨1037805, by rfl⟩ : syracuseStep 2767481 = 2075611) B2075611
theorem B2767535 : Blo 1843623 2767535 := bstep (se 1 (by rfl) ⟨2075651, by rfl⟩ : syracuseStep 2767535 = 4151303) B4151303
theorem B2767583 : Blo 1843623 2767583 := bstep (se 1 (by rfl) ⟨2075687, by rfl⟩ : syracuseStep 2767583 = 4151375) B4151375
theorem B4668151 : Blo 1843623 4668151 := bstep (se 1 (by rfl) ⟨3501113, by rfl⟩ : syracuseStep 4668151 = 7002227) B7002227
theorem B6224795 : Blo 1843623 6224795 := bstep (se 1 (by rfl) ⟨4668596, by rfl⟩ : syracuseStep 6224795 = 9337193) B9337193
theorem B3111851 : Blo 1843623 3111851 := bstep (se 1 (by rfl) ⟨2333888, by rfl⟩ : syracuseStep 3111851 = 4667777) B4667777
theorem B2767847 : Blo 1843623 2767847 := bstep (se 1 (by rfl) ⟨2075885, by rfl⟩ : syracuseStep 2767847 = 4151771) B4151771
theorem B4152311 : Blo 1843623 4152311 := bstep (se 1 (by rfl) ⟨3114233, by rfl⟩ : syracuseStep 4152311 = 6228467) B6228467
theorem B4668455 : Blo 1843623 4668455 := bstep (se 1 (by rfl) ⟨3501341, by rfl⟩ : syracuseStep 4668455 = 7002683) B7002683
theorem B19938469 : Blo 1843623 19938469 := bstep (se 4 (by rfl) ⟨1869231, by rfl⟩ : syracuseStep 19938469 = 3738463) B3738463
theorem B2768105 : Blo 1843623 2768105 := bstep (se 2 (by rfl) ⟨1038039, by rfl⟩ : syracuseStep 2768105 = 2076079) B2076079
theorem B7879967 : Blo 1843623 7879967 := bstep (se 1 (by rfl) ⟨5909975, by rfl⟩ : syracuseStep 7879967 = 11819951) B11819951
theorem B2768159 : Blo 1843623 2768159 := bstep (se 1 (by rfl) ⟨2076119, by rfl⟩ : syracuseStep 2768159 = 4152239) B4152239
theorem B6651233 : Blo 1843623 6651233 := bstep (se 2 (by rfl) ⟨2494212, by rfl⟩ : syracuseStep 6651233 = 4988425) B4988425
theorem B3112391 : Blo 1843623 3112391 := bstep (se 1 (by rfl) ⟨2334293, by rfl⟩ : syracuseStep 3112391 = 4668587) B4668587
theorem B2768327 : Blo 1843623 2768327 := bstep (se 1 (by rfl) ⟨2076245, by rfl⟩ : syracuseStep 2768327 = 4152491) B4152491
theorem B9338327 : Blo 1843623 9338327 := bstep (se 1 (by rfl) ⟨7003745, by rfl⟩ : syracuseStep 9338327 = 14007491) B14007491
theorem B15760889 : Blo 1843623 15760889 := bstep (se 2 (by rfl) ⟨5910333, by rfl⟩ : syracuseStep 15760889 = 11820667) B11820667
theorem B4431443 : Blo 1843623 4431443 := bstep (se 1 (by rfl) ⟨3323582, by rfl⟩ : syracuseStep 4431443 = 6647165) B6647165
theorem B6307591 : Blo 1843623 6307591 := bstep (se 1 (by rfl) ⟨4730693, by rfl⟩ : syracuseStep 6307591 = 9461387) B9461387
theorem B3940103 : Blo 1843623 3940103 := bstep (se 1 (by rfl) ⟨2955077, by rfl⟩ : syracuseStep 3940103 = 5910155) B5910155
theorem B2334511 : Blo 1843623 2334511 := bstep (se 1 (by rfl) ⟨1750883, by rfl⟩ : syracuseStep 2334511 = 3501767) B3501767
theorem B6225821 : Blo 1843623 6225821 := bstep (se 3 (by rfl) ⟨1167341, by rfl⟩ : syracuseStep 6225821 = 2334683) B2334683
theorem B5906465 : Blo 1843623 5906465 := bstep (se 2 (by rfl) ⟨2214924, by rfl⟩ : syracuseStep 5906465 = 4429849) B4429849
theorem B6742055 : Blo 1843623 6742055 := bstep (se 1 (by rfl) ⟨5056541, by rfl⟩ : syracuseStep 6742055 = 10113083) B10113083
theorem B3113147 : Blo 1843623 3113147 := bstep (se 1 (by rfl) ⟨2334860, by rfl⟩ : syracuseStep 3113147 = 4669721) B4669721
theorem B106406297 : Blo 1843623 106406297 := bstep (se 2 (by rfl) ⟨39902361, by rfl⟩ : syracuseStep 106406297 = 79804723) B79804723
theorem B4669883 : Blo 1843623 4669883 := bstep (se 1 (by rfl) ⟨3502412, by rfl⟩ : syracuseStep 4669883 = 7004825) B7004825
theorem B1843663 : Blo 1843623 1843663 := bstep (se 1 (by rfl) ⟨1382747, by rfl⟩ : syracuseStep 1843663 = 2765495) B2765495
theorem B1843815 : Blo 1843623 1843815 := bstep (se 1 (by rfl) ⟨1382861, by rfl⟩ : syracuseStep 1843815 = 2765723) B2765723
theorem B3113707 : Blo 1843623 3113707 := bstep (se 1 (by rfl) ⟨2335280, by rfl⟩ : syracuseStep 3113707 = 4670561) B4670561
theorem B6226685 : Blo 1843623 6226685 := bstep (se 3 (by rfl) ⟨1167503, by rfl⟩ : syracuseStep 6226685 = 2335007) B2335007
theorem B3941129 : Blo 1843623 3941129 := bstep (se 2 (by rfl) ⟨1477923, by rfl⟩ : syracuseStep 3941129 = 2955847) B2955847
theorem B9970451 : Blo 1843623 9970451 := bstep (se 1 (by rfl) ⟨7477838, by rfl⟩ : syracuseStep 9970451 = 14955677) B14955677
theorem B23642927 : Blo 1843623 23642927 := bstep (se 1 (by rfl) ⟨17732195, by rfl⟩ : syracuseStep 23642927 = 35464391) B35464391
theorem B1844079 : Blo 1843623 1844079 := bstep (se 1 (by rfl) ⟨1383059, by rfl⟩ : syracuseStep 1844079 = 2766119) B2766119
theorem B1844135 : Blo 1843623 1844135 := bstep (se 1 (by rfl) ⟨1383101, by rfl⟩ : syracuseStep 1844135 = 2766203) B2766203
theorem B2335655 : Blo 1843623 2335655 := bstep (se 1 (by rfl) ⟨1751741, by rfl⟩ : syracuseStep 2335655 = 3503483) B3503483
theorem B4670419 : Blo 1843623 4670419 := bstep (se 1 (by rfl) ⟨3502814, by rfl⟩ : syracuseStep 4670419 = 7005629) B7005629
theorem B1844219 : Blo 1843623 1844219 := bstep (se 1 (by rfl) ⟨1383164, by rfl⟩ : syracuseStep 1844219 = 2766329) B2766329
theorem B3154999 : Blo 1843623 3154999 := bstep (se 1 (by rfl) ⟨2366249, by rfl⟩ : syracuseStep 3154999 = 4732499) B4732499
theorem B1844287 : Blo 1843623 1844287 := bstep (se 1 (by rfl) ⟨1383215, by rfl⟩ : syracuseStep 1844287 = 2766431) B2766431
theorem B2335807 : Blo 1843623 2335807 := bstep (se 1 (by rfl) ⟨1751855, by rfl⟩ : syracuseStep 2335807 = 3503711) B3503711
theorem B44893277 : Blo 1843623 44893277 := bstep (se 3 (by rfl) ⟨8417489, by rfl⟩ : syracuseStep 44893277 = 16834979) B16834979
theorem B1844431 : Blo 1843623 1844431 := bstep (se 1 (by rfl) ⟨1383323, by rfl⟩ : syracuseStep 1844431 = 2766647) B2766647
theorem B13296869 : Blo 1843623 13296869 := bstep (se 4 (by rfl) ⟨1246581, by rfl⟩ : syracuseStep 13296869 = 2493163) B2493163
theorem B15754601 : Blo 1843623 15754601 := bstep (se 2 (by rfl) ⟨5907975, by rfl⟩ : syracuseStep 15754601 = 11815951) B11815951
theorem B1844635 : Blo 1843623 1844635 := bstep (se 1 (by rfl) ⟨1383476, by rfl⟩ : syracuseStep 1844635 = 2766953) B2766953
theorem B5252627 : Blo 1843623 5252627 := bstep (se 1 (by rfl) ⟨3939470, by rfl⟩ : syracuseStep 5252627 = 7878941) B7878941
theorem B129467933 : Blo 1843623 129467933 := bstep (se 3 (by rfl) ⟨24275237, by rfl⟩ : syracuseStep 129467933 = 48550475) B48550475
theorem B26584625 : Blo 1843623 26584625 := bstep (se 2 (by rfl) ⟨9969234, by rfl⟩ : syracuseStep 26584625 = 19938469) B19938469
theorem B5908079 : Blo 1843623 5908079 := bstep (se 1 (by rfl) ⟨4431059, by rfl⟩ : syracuseStep 5908079 = 8862119) B8862119
theorem B1844847 : Blo 1843623 1844847 := bstep (se 1 (by rfl) ⟨1383635, by rfl⟩ : syracuseStep 1844847 = 2767271) B2767271
theorem B7882393 : Blo 1843623 7882393 := bstep (se 2 (by rfl) ⟨2955897, by rfl⟩ : syracuseStep 7882393 = 5911795) B5911795
theorem B2074279 : Blo 1843623 2074279 := bstep (se 1 (by rfl) ⟨1555709, by rfl⟩ : syracuseStep 2074279 = 3111419) B3111419
theorem B1844903 : Blo 1843623 1844903 := bstep (se 1 (by rfl) ⟨1383677, by rfl⟩ : syracuseStep 1844903 = 2767355) B2767355
theorem B1844987 : Blo 1843623 1844987 := bstep (se 1 (by rfl) ⟨1383740, by rfl⟩ : syracuseStep 1844987 = 2767481) B2767481
theorem B1845023 : Blo 1843623 1845023 := bstep (se 1 (by rfl) ⟨1383767, by rfl⟩ : syracuseStep 1845023 = 2767535) B2767535
theorem B1845055 : Blo 1843623 1845055 := bstep (se 1 (by rfl) ⟨1383791, by rfl⟩ : syracuseStep 1845055 = 2767583) B2767583
theorem B2074567 : Blo 1843623 2074567 := bstep (se 1 (by rfl) ⟨1555925, by rfl⟩ : syracuseStep 2074567 = 3111851) B3111851
theorem B1845231 : Blo 1843623 1845231 := bstep (se 1 (by rfl) ⟨1383923, by rfl⟩ : syracuseStep 1845231 = 2767847) B2767847
theorem B1845403 : Blo 1843623 1845403 := bstep (se 1 (by rfl) ⟨1384052, by rfl⟩ : syracuseStep 1845403 = 2768105) B2768105
theorem B5253311 : Blo 1843623 5253311 := bstep (se 1 (by rfl) ⟨3939983, by rfl⟩ : syracuseStep 5253311 = 7879967) B7879967
theorem B1845439 : Blo 1843623 1845439 := bstep (se 1 (by rfl) ⟨1384079, by rfl⟩ : syracuseStep 1845439 = 2768159) B2768159
theorem B4434155 : Blo 1843623 4434155 := bstep (se 1 (by rfl) ⟨3325616, by rfl⟩ : syracuseStep 4434155 = 6651233) B6651233
theorem B2074927 : Blo 1843623 2074927 := bstep (se 1 (by rfl) ⟨1556195, by rfl⟩ : syracuseStep 2074927 = 3112391) B3112391
theorem B1845551 : Blo 1843623 1845551 := bstep (se 1 (by rfl) ⟨1384163, by rfl⟩ : syracuseStep 1845551 = 2768327) B2768327
theorem B47278565 : Blo 1843623 47278565 := bstep (se 4 (by rfl) ⟨4432365, by rfl⟩ : syracuseStep 47278565 = 8864731) B8864731
theorem B25234199 : Blo 1843623 25234199 := bstep (se 1 (by rfl) ⟨18925649, by rfl⟩ : syracuseStep 25234199 = 37851299) B37851299
theorem B6228791 : Blo 1843623 6228791 := bstep (se 1 (by rfl) ⟨4671593, by rfl⟩ : syracuseStep 6228791 = 9343187) B9343187
theorem B14011379 : Blo 1843623 14011379 := bstep (se 1 (by rfl) ⟨10508534, by rfl⟩ : syracuseStep 14011379 = 21017069) B21017069
theorem B2075719 : Blo 1843623 2075719 := bstep (se 1 (by rfl) ⟨1556789, by rfl⟩ : syracuseStep 2075719 = 3113579) B3113579
theorem B7482667 : Blo 1843623 7482667 := bstep (se 1 (by rfl) ⟨5612000, by rfl⟩ : syracuseStep 7482667 = 11224001) B11224001
theorem B9342377 : Blo 1843623 9342377 := bstep (se 2 (by rfl) ⟨3503391, by rfl⟩ : syracuseStep 9342377 = 7006783) B7006783
theorem B3739243 : Blo 1843623 3739243 := bstep (se 1 (by rfl) ⟨2804432, by rfl⟩ : syracuseStep 3739243 = 5608865) B5608865
theorem B5254951 : Blo 1843623 5254951 := bstep (se 1 (by rfl) ⟨3941213, by rfl⟩ : syracuseStep 5254951 = 7882427) B7882427
theorem B9342863 : Blo 1843623 9342863 := bstep (se 1 (by rfl) ⟨7007147, by rfl⟩ : syracuseStep 9342863 = 14014295) B14014295
theorem B9596879 : Blo 1843623 9596879 := bstep (se 1 (by rfl) ⟨7197659, by rfl⟩ : syracuseStep 9596879 = 14395319) B14395319
theorem B4149215 : Blo 1843623 4149215 := bstep (se 1 (by rfl) ⟨3111911, by rfl⟩ : syracuseStep 4149215 = 6223823) B6223823
theorem B11817181 : Blo 1843623 11817181 := bstep (se 3 (by rfl) ⟨2215721, by rfl⟩ : syracuseStep 11817181 = 4431443) B4431443
theorem B6222419 : Blo 1843623 6222419 := bstep (se 1 (by rfl) ⟨4666814, by rfl⟩ : syracuseStep 6222419 = 9333629) B9333629
theorem B4149863 : Blo 1843623 4149863 := bstep (se 1 (by rfl) ⟨3112397, by rfl⟩ : syracuseStep 4149863 = 6224795) B6224795
theorem B10506941 : Blo 1843623 10506941 := bstep (se 3 (by rfl) ⟨1970051, by rfl⟩ : syracuseStep 10506941 = 3940103) B3940103
theorem B2765609 : Blo 1843623 2765609 := bstep (se 2 (by rfl) ⟨1037103, by rfl⟩ : syracuseStep 2765609 = 2074207) B2074207
theorem B2765615 : Blo 1843623 2765615 := bstep (se 1 (by rfl) ⟨2074211, by rfl⟩ : syracuseStep 2765615 = 4148423) B4148423
theorem B2765735 : Blo 1843623 2765735 := bstep (se 1 (by rfl) ⟨2074301, by rfl⟩ : syracuseStep 2765735 = 4148603) B4148603
theorem B2765819 : Blo 1843623 2765819 := bstep (se 1 (by rfl) ⟨2074364, by rfl⟩ : syracuseStep 2765819 = 4148729) B4148729
theorem B10507259 : Blo 1843623 10507259 := bstep (se 1 (by rfl) ⟨7880444, by rfl⟩ : syracuseStep 10507259 = 15760889) B15760889
theorem B8410121 : Blo 1843623 8410121 := bstep (se 2 (by rfl) ⟨3153795, by rfl⟩ : syracuseStep 8410121 = 6307591) B6307591
theorem B2765879 : Blo 1843623 2765879 := bstep (se 1 (by rfl) ⟨2074409, by rfl⟩ : syracuseStep 2765879 = 4148819) B4148819
theorem B2765999 : Blo 1843623 2765999 := bstep (se 1 (by rfl) ⟨2074499, by rfl⟩ : syracuseStep 2765999 = 4148999) B4148999
theorem B6223067 : Blo 1843623 6223067 := bstep (se 1 (by rfl) ⟨4667300, by rfl⟩ : syracuseStep 6223067 = 9334601) B9334601
theorem B4150547 : Blo 1843623 4150547 := bstep (se 1 (by rfl) ⟨3112910, by rfl⟩ : syracuseStep 4150547 = 6225821) B6225821
theorem B4150619 : Blo 1843623 4150619 := bstep (se 1 (by rfl) ⟨3112964, by rfl⟩ : syracuseStep 4150619 = 6225929) B6225929
theorem B17724815 : Blo 1843623 17724815 := bstep (se 1 (by rfl) ⟨13293611, by rfl⟩ : syracuseStep 17724815 = 26587223) B26587223
theorem B2766407 : Blo 1843623 2766407 := bstep (se 1 (by rfl) ⟨2074805, by rfl⟩ : syracuseStep 2766407 = 4149611) B4149611
theorem B6649415 : Blo 1843623 6649415 := bstep (se 1 (by rfl) ⟨4987061, by rfl⟩ : syracuseStep 6649415 = 9974123) B9974123
theorem B2954873 : Blo 1843623 2954873 := bstep (se 2 (by rfl) ⟨1108077, by rfl⟩ : syracuseStep 2954873 = 2216155) B2216155
theorem B47265443 : Blo 1843623 47265443 := bstep (se 1 (by rfl) ⟨35449082, by rfl⟩ : syracuseStep 47265443 = 70898165) B70898165
theorem B2766503 : Blo 1843623 2766503 := bstep (se 1 (by rfl) ⟨2074877, by rfl⟩ : syracuseStep 2766503 = 4149755) B4149755
theorem B11818669 : Blo 1843623 11818669 := bstep (se 3 (by rfl) ⟨2216000, by rfl⟩ : syracuseStep 11818669 = 4432001) B4432001
theorem B2766587 : Blo 1843623 2766587 := bstep (se 1 (by rfl) ⟨2074940, by rfl⟩ : syracuseStep 2766587 = 4149881) B4149881
theorem B2766623 : Blo 1843623 2766623 := bstep (se 1 (by rfl) ⟨2074967, by rfl⟩ : syracuseStep 2766623 = 4149935) B4149935
theorem B19937087 : Blo 1843623 19937087 := bstep (se 1 (by rfl) ⟨14952815, by rfl⟩ : syracuseStep 19937087 = 29905631) B29905631
theorem B2766671 : Blo 1843623 2766671 := bstep (se 1 (by rfl) ⟨2075003, by rfl⟩ : syracuseStep 2766671 = 4150007) B4150007
theorem B2627407 : Blo 1843623 2627407 := bstep (se 1 (by rfl) ⟨1970555, by rfl⟩ : syracuseStep 2627407 = 3941111) B3941111
theorem B22435703 : Blo 1843623 22435703 := bstep (se 1 (by rfl) ⟨16826777, by rfl⟩ : syracuseStep 22435703 = 33653555) B33653555
theorem B4151177 : Blo 1843623 4151177 := bstep (se 2 (by rfl) ⟨1556691, by rfl⟩ : syracuseStep 4151177 = 3113383) B3113383
theorem B19937171 : Blo 1843623 19937171 := bstep (se 1 (by rfl) ⟨14952878, by rfl⟩ : syracuseStep 19937171 = 29905757) B29905757
theorem B2766791 : Blo 1843623 2766791 := bstep (se 1 (by rfl) ⟨2075093, by rfl⟩ : syracuseStep 2766791 = 4150187) B4150187
theorem B79779815 : Blo 1843623 79779815 := bstep (se 1 (by rfl) ⟨59834861, by rfl⟩ : syracuseStep 79779815 = 119669723) B119669723
theorem B6223931 : Blo 1843623 6223931 := bstep (se 1 (by rfl) ⟨4667948, by rfl⟩ : syracuseStep 6223931 = 9335897) B9335897
theorem B4151393 : Blo 1843623 4151393 := bstep (se 2 (by rfl) ⟨1556772, by rfl⟩ : syracuseStep 4151393 = 3113545) B3113545
theorem B35461385 : Blo 1843623 35461385 := bstep (se 2 (by rfl) ⟨13298019, by rfl⟩ : syracuseStep 35461385 = 26596039) B26596039
theorem B7002409 : Blo 1843623 7002409 := bstep (se 2 (by rfl) ⟨2625903, by rfl⟩ : syracuseStep 7002409 = 5251807) B5251807
theorem B2767145 : Blo 1843623 2767145 := bstep (se 2 (by rfl) ⟨1037679, by rfl⟩ : syracuseStep 2767145 = 2075359) B2075359
theorem B2767151 : Blo 1843623 2767151 := bstep (se 1 (by rfl) ⟨2075363, by rfl⟩ : syracuseStep 2767151 = 4150727) B4150727
theorem B2955577 : Blo 1843623 2955577 := bstep (se 2 (by rfl) ⟨1108341, by rfl⟩ : syracuseStep 2955577 = 2216683) B2216683
theorem B10500425 : Blo 1843623 10500425 := bstep (se 2 (by rfl) ⟨3937659, by rfl⟩ : syracuseStep 10500425 = 7875319) B7875319
theorem B6224201 : Blo 1843623 6224201 := bstep (se 2 (by rfl) ⟨2334075, by rfl⟩ : syracuseStep 6224201 = 4668151) B4668151
theorem B9967979 : Blo 1843623 9967979 := bstep (se 1 (by rfl) ⟨7475984, by rfl⟩ : syracuseStep 9967979 = 14951969) B14951969
theorem B6068603 : Blo 1843623 6068603 := bstep (se 1 (by rfl) ⟨4551452, by rfl⟩ : syracuseStep 6068603 = 9102905) B9102905
theorem B20224399 : Blo 1843623 20224399 := bstep (se 1 (by rfl) ⟨15168299, by rfl⟩ : syracuseStep 20224399 = 30336599) B30336599
theorem B25237979 : Blo 1843623 25237979 := bstep (se 1 (by rfl) ⟨18928484, by rfl⟩ : syracuseStep 25237979 = 37856969) B37856969
theorem B2767391 : Blo 1843623 2767391 := bstep (se 1 (by rfl) ⟨2075543, by rfl⟩ : syracuseStep 2767391 = 4151087) B4151087
theorem B9337679 : Blo 1843623 9337679 := bstep (se 1 (by rfl) ⟨7003259, by rfl⟩ : syracuseStep 9337679 = 14006519) B14006519
theorem B4430675 : Blo 1843623 4430675 := bstep (se 1 (by rfl) ⟨3323006, by rfl⟩ : syracuseStep 4430675 = 6646013) B6646013
theorem B2767775 : Blo 1843623 2767775 := bstep (se 1 (by rfl) ⟨2075831, by rfl⟩ : syracuseStep 2767775 = 4151663) B4151663
theorem B2104223 : Blo 1843623 2104223 := bstep (se 1 (by rfl) ⟨1578167, by rfl⟩ : syracuseStep 2104223 = 3156335) B3156335
theorem B2767823 : Blo 1843623 2767823 := bstep (se 1 (by rfl) ⟨2075867, by rfl⟩ : syracuseStep 2767823 = 4151735) B4151735
theorem B2767913 : Blo 1843623 2767913 := bstep (se 2 (by rfl) ⟨1037967, by rfl⟩ : syracuseStep 2767913 = 2075935) B2075935
theorem B2767919 : Blo 1843623 2767919 := bstep (se 1 (by rfl) ⟨2075939, by rfl⟩ : syracuseStep 2767919 = 4151879) B4151879
theorem B2333767 : Blo 1843623 2333767 := bstep (se 1 (by rfl) ⟨1750325, by rfl⟩ : syracuseStep 2333767 = 3500651) B3500651
theorem B2767943 : Blo 1843623 2767943 := bstep (se 1 (by rfl) ⟨2075957, by rfl⟩ : syracuseStep 2767943 = 4151915) B4151915
theorem B26582201 : Blo 1843623 26582201 := bstep (se 2 (by rfl) ⟨9968325, by rfl⟩ : syracuseStep 26582201 = 19936651) B19936651
theorem B9968825 : Blo 1843623 9968825 := bstep (se 2 (by rfl) ⟨3738309, by rfl⟩ : syracuseStep 9968825 = 7476619) B7476619
theorem B122985665 : Blo 1843623 122985665 := bstep (se 2 (by rfl) ⟨46119624, by rfl⟩ : syracuseStep 122985665 = 92239249) B92239249
theorem B2768207 : Blo 1843623 2768207 := bstep (se 1 (by rfl) ⟨2076155, by rfl⟩ : syracuseStep 2768207 = 4152311) B4152311
theorem B3112303 : Blo 1843623 3112303 := bstep (se 1 (by rfl) ⟨2334227, by rfl⟩ : syracuseStep 3112303 = 4668455) B4668455
theorem B2768297 : Blo 1843623 2768297 := bstep (se 2 (by rfl) ⟨1038111, by rfl⟩ : syracuseStep 2768297 = 2076223) B2076223
theorem B13483493 : Blo 1843623 13483493 := bstep (se 4 (by rfl) ⟨1264077, by rfl⟩ : syracuseStep 13483493 = 2528155) B2528155
theorem B14966309 : Blo 1843623 14966309 := bstep (se 4 (by rfl) ⟨1403091, by rfl⟩ : syracuseStep 14966309 = 2806183) B2806183
theorem B5250703 : Blo 1843623 5250703 := bstep (se 1 (by rfl) ⟨3938027, by rfl⟩ : syracuseStep 5250703 = 7876055) B7876055
theorem B6225551 : Blo 1843623 6225551 := bstep (se 1 (by rfl) ⟨4669163, by rfl⟩ : syracuseStep 6225551 = 9338327) B9338327
theorem B26590913 : Blo 1843623 26590913 := bstep (se 2 (by rfl) ⟨9971592, by rfl⟩ : syracuseStep 26590913 = 19943185) B19943185
theorem B3112681 : Blo 1843623 3112681 := bstep (se 2 (by rfl) ⟨1167255, by rfl⟩ : syracuseStep 3112681 = 2334511) B2334511
theorem B33644267 : Blo 1843623 33644267 := bstep (se 1 (by rfl) ⟨25233200, by rfl⟩ : syracuseStep 33644267 = 50466401) B50466401
theorem B7479229 : Blo 1843623 7479229 := bstep (se 3 (by rfl) ⟨1402355, by rfl⟩ : syracuseStep 7479229 = 2804711) B2804711
theorem B3113255 : Blo 1843623 3113255 := bstep (se 1 (by rfl) ⟨2334941, by rfl⟩ : syracuseStep 3113255 = 4669883) B4669883
theorem B3940769 : Blo 1843623 3940769 := bstep (se 2 (by rfl) ⟨1477788, by rfl⟩ : syracuseStep 3940769 = 2955577) B2955577
theorem B7004627 : Blo 1843623 7004627 := bstep (se 1 (by rfl) ⟨5253470, by rfl⟩ : syracuseStep 7004627 = 10506941) B10506941
theorem B1843739 : Blo 1843623 1843739 := bstep (se 1 (by rfl) ⟨1382804, by rfl⟩ : syracuseStep 1843739 = 2765609) B2765609
theorem B1843743 : Blo 1843623 1843743 := bstep (se 1 (by rfl) ⟨1382807, by rfl⟩ : syracuseStep 1843743 = 2765615) B2765615
theorem B15761951 : Blo 1843623 15761951 := bstep (se 1 (by rfl) ⟨11821463, by rfl⟩ : syracuseStep 15761951 = 23642927) B23642927
theorem B1843823 : Blo 1843623 1843823 := bstep (se 1 (by rfl) ⟨1382867, by rfl⟩ : syracuseStep 1843823 = 2765735) B2765735
theorem B1843879 : Blo 1843623 1843879 := bstep (se 1 (by rfl) ⟨1382909, by rfl⟩ : syracuseStep 1843879 = 2765819) B2765819
theorem B7004839 : Blo 1843623 7004839 := bstep (se 1 (by rfl) ⟨5253629, by rfl⟩ : syracuseStep 7004839 = 10507259) B10507259
theorem B1843919 : Blo 1843623 1843919 := bstep (se 1 (by rfl) ⟨1382939, by rfl⟩ : syracuseStep 1843919 = 2765879) B2765879
theorem B1843999 : Blo 1843623 1843999 := bstep (se 1 (by rfl) ⟨1382999, by rfl⟩ : syracuseStep 1843999 = 2765999) B2765999
theorem B8864579 : Blo 1843623 8864579 := bstep (se 1 (by rfl) ⟨6648434, by rfl⟩ : syracuseStep 8864579 = 13296869) B13296869
theorem B10503067 : Blo 1843623 10503067 := bstep (se 1 (by rfl) ⟨7877300, by rfl⟩ : syracuseStep 10503067 = 15754601) B15754601
theorem B86311955 : Blo 1843623 86311955 := bstep (se 1 (by rfl) ⟨64733966, by rfl⟩ : syracuseStep 86311955 = 129467933) B129467933
theorem B1844271 : Blo 1843623 1844271 := bstep (se 1 (by rfl) ⟨1383203, by rfl⟩ : syracuseStep 1844271 = 2766407) B2766407
theorem B4432943 : Blo 1843623 4432943 := bstep (se 1 (by rfl) ⟨3324707, by rfl⟩ : syracuseStep 4432943 = 6649415) B6649415
theorem B1844335 : Blo 1843623 1844335 := bstep (se 1 (by rfl) ⟨1383251, by rfl⟩ : syracuseStep 1844335 = 2766503) B2766503
theorem B1844391 : Blo 1843623 1844391 := bstep (se 1 (by rfl) ⟨1383293, by rfl⟩ : syracuseStep 1844391 = 2766587) B2766587
theorem B1844415 : Blo 1843623 1844415 := bstep (se 1 (by rfl) ⟨1383311, by rfl⟩ : syracuseStep 1844415 = 2766623) B2766623
theorem B1844447 : Blo 1843623 1844447 := bstep (se 1 (by rfl) ⟨1383335, by rfl⟩ : syracuseStep 1844447 = 2766671) B2766671
theorem B6227225 : Blo 1843623 6227225 := bstep (se 2 (by rfl) ⟨2335209, by rfl⟩ : syracuseStep 6227225 = 4670419) B4670419
theorem B1844527 : Blo 1843623 1844527 := bstep (se 1 (by rfl) ⟨1383395, by rfl⟩ : syracuseStep 1844527 = 2766791) B2766791
theorem B3114409 : Blo 1843623 3114409 := bstep (se 2 (by rfl) ⟨1167903, by rfl⟩ : syracuseStep 3114409 = 2335807) B2335807
theorem B1844763 : Blo 1843623 1844763 := bstep (se 1 (by rfl) ⟨1383572, by rfl⟩ : syracuseStep 1844763 = 2767145) B2767145
theorem B1844767 : Blo 1843623 1844767 := bstep (se 1 (by rfl) ⟨1383575, by rfl⟩ : syracuseStep 1844767 = 2767151) B2767151
theorem B1844927 : Blo 1843623 1844927 := bstep (se 1 (by rfl) ⟨1383695, by rfl⟩ : syracuseStep 1844927 = 2767391) B2767391
theorem B1845183 : Blo 1843623 1845183 := bstep (se 1 (by rfl) ⟨1383887, by rfl⟩ : syracuseStep 1845183 = 2767775) B2767775
theorem B1845215 : Blo 1843623 1845215 := bstep (se 1 (by rfl) ⟨1383911, by rfl⟩ : syracuseStep 1845215 = 2767823) B2767823
theorem B9340919 : Blo 1843623 9340919 := bstep (se 1 (by rfl) ⟨7005689, by rfl⟩ : syracuseStep 9340919 = 14011379) B14011379
theorem B1845275 : Blo 1843623 1845275 := bstep (se 1 (by rfl) ⟨1383956, by rfl⟩ : syracuseStep 1845275 = 2767913) B2767913
theorem B1845279 : Blo 1843623 1845279 := bstep (se 1 (by rfl) ⟨1383959, by rfl⟩ : syracuseStep 1845279 = 2767919) B2767919
theorem B1845295 : Blo 1843623 1845295 := bstep (se 1 (by rfl) ⟨1383971, by rfl⟩ : syracuseStep 1845295 = 2767943) B2767943
theorem B17721467 : Blo 1843623 17721467 := bstep (se 1 (by rfl) ⟨13291100, by rfl⟩ : syracuseStep 17721467 = 26582201) B26582201
theorem B6645883 : Blo 1843623 6645883 := bstep (se 1 (by rfl) ⟨4984412, by rfl⟩ : syracuseStep 6645883 = 9968825) B9968825
theorem B1845471 : Blo 1843623 1845471 := bstep (se 1 (by rfl) ⟨1384103, by rfl⟩ : syracuseStep 1845471 = 2768207) B2768207
theorem B6228251 : Blo 1843623 6228251 := bstep (se 1 (by rfl) ⟨4671188, by rfl⟩ : syracuseStep 6228251 = 9342377) B9342377
theorem B1845531 : Blo 1843623 1845531 := bstep (se 1 (by rfl) ⟨1384148, by rfl⟩ : syracuseStep 1845531 = 2768297) B2768297
theorem B8988995 : Blo 1843623 8988995 := bstep (se 1 (by rfl) ⟨6741746, by rfl⟩ : syracuseStep 8988995 = 13483493) B13483493
theorem B7006601 : Blo 1843623 7006601 := bstep (se 2 (by rfl) ⟨2627475, by rfl⟩ : syracuseStep 7006601 = 5254951) B5254951
theorem B6228413 : Blo 1843623 6228413 := bstep (se 3 (by rfl) ⟨1167827, by rfl⟩ : syracuseStep 6228413 = 2335655) B2335655
theorem B9972305 : Blo 1843623 9972305 := bstep (se 2 (by rfl) ⟨3739614, by rfl⟩ : syracuseStep 9972305 = 7479229) B7479229
theorem B6228575 : Blo 1843623 6228575 := bstep (se 1 (by rfl) ⟨4671431, by rfl⟩ : syracuseStep 6228575 = 9342863) B9342863
theorem B2075431 : Blo 1843623 2075431 := bstep (se 1 (by rfl) ⟨1556573, by rfl⟩ : syracuseStep 2075431 = 3113147) B3113147
theorem B70937531 : Blo 1843623 70937531 := bstep (se 1 (by rfl) ⟨53203148, by rfl⟩ : syracuseStep 70937531 = 106406297) B106406297
theorem B15756241 : Blo 1843623 15756241 := bstep (se 2 (by rfl) ⟨5908590, by rfl⟩ : syracuseStep 15756241 = 11817181) B11817181
theorem B4148279 : Blo 1843623 4148279 := bstep (se 1 (by rfl) ⟨3111209, by rfl⟩ : syracuseStep 4148279 = 6222419) B6222419
theorem B6646967 : Blo 1843623 6646967 := bstep (se 1 (by rfl) ⟨4985225, by rfl⟩ : syracuseStep 6646967 = 9970451) B9970451
theorem B5606747 : Blo 1843623 5606747 := bstep (se 1 (by rfl) ⟨4205060, by rfl⟩ : syracuseStep 5606747 = 8410121) B8410121
theorem B29928851 : Blo 1843623 29928851 := bstep (se 1 (by rfl) ⟨22446638, by rfl⟩ : syracuseStep 29928851 = 44893277) B44893277
theorem B4148711 : Blo 1843623 4148711 := bstep (se 1 (by rfl) ⟨3111533, by rfl⟩ : syracuseStep 4148711 = 6223067) B6223067
theorem B11816543 : Blo 1843623 11816543 := bstep (se 1 (by rfl) ⟨8862407, by rfl⟩ : syracuseStep 11816543 = 17724815) B17724815
theorem B17723083 : Blo 1843623 17723083 := bstep (se 1 (by rfl) ⟨13292312, by rfl⟩ : syracuseStep 17723083 = 26584625) B26584625
theorem B1969915 : Blo 1843623 1969915 := bstep (se 1 (by rfl) ⟨1477436, by rfl⟩ : syracuseStep 1969915 = 2954873) B2954873
theorem B31510295 : Blo 1843623 31510295 := bstep (se 1 (by rfl) ⟨23632721, by rfl⟩ : syracuseStep 31510295 = 47265443) B47265443
theorem B13291391 : Blo 1843623 13291391 := bstep (se 1 (by rfl) ⟨9968543, by rfl⟩ : syracuseStep 13291391 = 19937087) B19937087
theorem B13291447 : Blo 1843623 13291447 := bstep (se 1 (by rfl) ⟨9968585, by rfl⟩ : syracuseStep 13291447 = 19937171) B19937171
theorem B53186543 : Blo 1843623 53186543 := bstep (se 1 (by rfl) ⟨39889907, by rfl⟩ : syracuseStep 53186543 = 79779815) B79779815
theorem B4149287 : Blo 1843623 4149287 := bstep (se 1 (by rfl) ⟨3111965, by rfl⟩ : syracuseStep 4149287 = 6223931) B6223931
theorem B4206665 : Blo 1843623 4206665 := bstep (se 2 (by rfl) ⟨1577499, by rfl⟩ : syracuseStep 4206665 = 3154999) B3154999
theorem B3502207 : Blo 1843623 3502207 := bstep (se 1 (by rfl) ⟨2626655, by rfl⟩ : syracuseStep 3502207 = 5253311) B5253311
theorem B7000283 : Blo 1843623 7000283 := bstep (se 1 (by rfl) ⟨5250212, by rfl⟩ : syracuseStep 7000283 = 10500425) B10500425
theorem B4149467 : Blo 1843623 4149467 := bstep (se 1 (by rfl) ⟨3112100, by rfl⟩ : syracuseStep 4149467 = 6224201) B6224201
theorem B31519043 : Blo 1843623 31519043 := bstep (se 1 (by rfl) ⟨23639282, by rfl⟩ : syracuseStep 31519043 = 47278565) B47278565
theorem B14012837 : Blo 1843623 14012837 := bstep (se 4 (by rfl) ⟨1313703, by rfl⟩ : syracuseStep 14012837 = 2627407) B2627407
theorem B4149737 : Blo 1843623 4149737 := bstep (se 2 (by rfl) ⟨1556151, by rfl⟩ : syracuseStep 4149737 = 3112303) B3112303
theorem B16822799 : Blo 1843623 16822799 := bstep (se 1 (by rfl) ⟨12617099, by rfl⟩ : syracuseStep 16822799 = 25234199) B25234199
theorem B2953783 : Blo 1843623 2953783 := bstep (se 1 (by rfl) ⟨2215337, by rfl⟩ : syracuseStep 2953783 = 4430675) B4430675
theorem B81990443 : Blo 1843623 81990443 := bstep (se 1 (by rfl) ⟨61492832, by rfl⟩ : syracuseStep 81990443 = 122985665) B122985665
theorem B4985657 : Blo 1843623 4985657 := bstep (se 2 (by rfl) ⟨1869621, by rfl⟩ : syracuseStep 4985657 = 3739243) B3739243
theorem B7000937 : Blo 1843623 7000937 := bstep (se 2 (by rfl) ⟨2625351, by rfl⟩ : syracuseStep 7000937 = 5250703) B5250703
theorem B2765705 : Blo 1843623 2765705 := bstep (se 2 (by rfl) ⟨1037139, by rfl⟩ : syracuseStep 2765705 = 2074279) B2074279
theorem B15758225 : Blo 1843623 15758225 := bstep (se 2 (by rfl) ⟨5909334, by rfl⟩ : syracuseStep 15758225 = 11818669) B11818669
theorem B4150241 : Blo 1843623 4150241 := bstep (se 2 (by rfl) ⟨1556340, by rfl⟩ : syracuseStep 4150241 = 3112681) B3112681
theorem B4150367 : Blo 1843623 4150367 := bstep (se 1 (by rfl) ⟨3112775, by rfl⟩ : syracuseStep 4150367 = 6225551) B6225551
theorem B2766089 : Blo 1843623 2766089 := bstep (se 2 (by rfl) ⟨1037283, by rfl⟩ : syracuseStep 2766089 = 2074567) B2074567
theorem B2766143 : Blo 1843623 2766143 := bstep (se 1 (by rfl) ⟨2074607, by rfl⟩ : syracuseStep 2766143 = 4149215) B4149215
theorem B3937643 : Blo 1843623 3937643 := bstep (se 1 (by rfl) ⟨2953232, by rfl⟩ : syracuseStep 3937643 = 5906465) B5906465
theorem B4494703 : Blo 1843623 4494703 := bstep (se 1 (by rfl) ⟨3371027, by rfl⟩ : syracuseStep 4494703 = 6742055) B6742055
theorem B9336545 : Blo 1843623 9336545 := bstep (se 2 (by rfl) ⟨3501204, by rfl⟩ : syracuseStep 9336545 = 7002409) B7002409
theorem B2766569 : Blo 1843623 2766569 := bstep (se 2 (by rfl) ⟨1037463, by rfl⟩ : syracuseStep 2766569 = 2074927) B2074927
theorem B2766575 : Blo 1843623 2766575 := bstep (se 1 (by rfl) ⟨2074931, by rfl⟩ : syracuseStep 2766575 = 4149863) B4149863
theorem B4151123 : Blo 1843623 4151123 := bstep (se 1 (by rfl) ⟨3113342, by rfl⟩ : syracuseStep 4151123 = 6226685) B6226685
theorem B2627419 : Blo 1843623 2627419 := bstep (se 1 (by rfl) ⟨1970564, by rfl⟩ : syracuseStep 2627419 = 3941129) B3941129
theorem B26965865 : Blo 1843623 26965865 := bstep (se 2 (by rfl) ⟨10112199, by rfl⟩ : syracuseStep 26965865 = 20224399) B20224399
theorem B2767031 : Blo 1843623 2767031 := bstep (se 1 (by rfl) ⟨2075273, by rfl⟩ : syracuseStep 2767031 = 4150547) B4150547
theorem B2767079 : Blo 1843623 2767079 := bstep (se 1 (by rfl) ⟨2075309, by rfl⟩ : syracuseStep 2767079 = 4150619) B4150619
theorem B26581277 : Blo 1843623 26581277 := bstep (se 3 (by rfl) ⟨4983989, by rfl⟩ : syracuseStep 26581277 = 9967979) B9967979
theorem B4151609 : Blo 1843623 4151609 := bstep (se 2 (by rfl) ⟨1556853, by rfl⟩ : syracuseStep 4151609 = 3113707) B3113707
theorem B3938719 : Blo 1843623 3938719 := bstep (se 1 (by rfl) ⟨2954039, by rfl⟩ : syracuseStep 3938719 = 5908079) B5908079
theorem B14957135 : Blo 1843623 14957135 := bstep (se 1 (by rfl) ⟨11217851, by rfl⟩ : syracuseStep 14957135 = 22435703) B22435703
theorem B2767451 : Blo 1843623 2767451 := bstep (se 1 (by rfl) ⟨2075588, by rfl⟩ : syracuseStep 2767451 = 4151177) B4151177
theorem B14007005 : Blo 1843623 14007005 := bstep (se 3 (by rfl) ⟨2626313, by rfl⟩ : syracuseStep 14007005 = 5252627) B5252627
theorem B2767595 : Blo 1843623 2767595 := bstep (se 1 (by rfl) ⟨2075696, by rfl⟩ : syracuseStep 2767595 = 4151393) B4151393
theorem B3111689 : Blo 1843623 3111689 := bstep (se 2 (by rfl) ⟨1166883, by rfl⟩ : syracuseStep 3111689 = 2333767) B2333767
theorem B2767625 : Blo 1843623 2767625 := bstep (se 2 (by rfl) ⟨1037859, by rfl⟩ : syracuseStep 2767625 = 2075719) B2075719
theorem B2956103 : Blo 1843623 2956103 := bstep (se 1 (by rfl) ⟨2217077, by rfl⟩ : syracuseStep 2956103 = 4434155) B4434155
theorem B23640923 : Blo 1843623 23640923 := bstep (se 1 (by rfl) ⟨17730692, by rfl⟩ : syracuseStep 23640923 = 35461385) B35461385
theorem B4045735 : Blo 1843623 4045735 := bstep (se 1 (by rfl) ⟨3034301, by rfl⟩ : syracuseStep 4045735 = 6068603) B6068603
theorem B16825319 : Blo 1843623 16825319 := bstep (se 1 (by rfl) ⟨12618989, by rfl⟩ : syracuseStep 16825319 = 25237979) B25237979
theorem B22445045 : Blo 1843623 22445045 := bstep (se 5 (by rfl) ⟨1052111, by rfl⟩ : syracuseStep 22445045 = 2104223) B2104223
theorem B9976889 : Blo 1843623 9976889 := bstep (se 2 (by rfl) ⟨3741333, by rfl⟩ : syracuseStep 9976889 = 7482667) B7482667
theorem B4152527 : Blo 1843623 4152527 := bstep (se 1 (by rfl) ⟨3114395, by rfl⟩ : syracuseStep 4152527 = 6228791) B6228791
theorem B6225119 : Blo 1843623 6225119 := bstep (se 1 (by rfl) ⟨4668839, by rfl⟩ : syracuseStep 6225119 = 9337679) B9337679
theorem B10509857 : Blo 1843623 10509857 := bstep (se 2 (by rfl) ⟨3941196, by rfl⟩ : syracuseStep 10509857 = 7882393) B7882393
theorem B9977539 : Blo 1843623 9977539 := bstep (se 1 (by rfl) ⟨7483154, by rfl⟩ : syracuseStep 9977539 = 14966309) B14966309
theorem B17727275 : Blo 1843623 17727275 := bstep (se 1 (by rfl) ⟨13295456, by rfl⟩ : syracuseStep 17727275 = 26590913) B26590913
theorem B22429511 : Blo 1843623 22429511 := bstep (se 1 (by rfl) ⟨16822133, by rfl⟩ : syracuseStep 22429511 = 33644267) B33644267
theorem B6397919 : Blo 1843623 6397919 := bstep (se 1 (by rfl) ⟨4798439, by rfl⟩ : syracuseStep 6397919 = 9596879) B9596879
theorem B4669609 : Blo 1843623 4669609 := bstep (se 2 (by rfl) ⟨1751103, by rfl⟩ : syracuseStep 4669609 = 3502207) B3502207
theorem B21012695 : Blo 1843623 21012695 := bstep (se 1 (by rfl) ⟨15759521, by rfl⟩ : syracuseStep 21012695 = 31519043) B31519043
theorem B4669751 : Blo 1843623 4669751 := bstep (se 1 (by rfl) ⟨3502313, by rfl⟩ : syracuseStep 4669751 = 7004627) B7004627
theorem B11215199 : Blo 1843623 11215199 := bstep (se 1 (by rfl) ⟨8411399, by rfl⟩ : syracuseStep 11215199 = 16822799) B16822799
theorem B5251625 : Blo 1843623 5251625 := bstep (se 2 (by rfl) ⟨1969359, by rfl⟩ : syracuseStep 5251625 = 3938719) B3938719
theorem B1843803 : Blo 1843623 1843803 := bstep (se 1 (by rfl) ⟨1382852, by rfl⟩ : syracuseStep 1843803 = 2765705) B2765705
theorem B57541303 : Blo 1843623 57541303 := bstep (se 1 (by rfl) ⟨43155977, by rfl⟩ : syracuseStep 57541303 = 86311955) B86311955
theorem B1844059 : Blo 1843623 1844059 := bstep (se 1 (by rfl) ⟨1383044, by rfl⟩ : syracuseStep 1844059 = 2766089) B2766089
theorem B1844095 : Blo 1843623 1844095 := bstep (se 1 (by rfl) ⟨1383071, by rfl⟩ : syracuseStep 1844095 = 2766143) B2766143
theorem B9339785 : Blo 1843623 9339785 := bstep (se 2 (by rfl) ⟨3502419, by rfl⟩ : syracuseStep 9339785 = 7004839) B7004839
theorem B1844379 : Blo 1843623 1844379 := bstep (se 1 (by rfl) ⟨1383284, by rfl⟩ : syracuseStep 1844379 = 2766569) B2766569
theorem B1844383 : Blo 1843623 1844383 := bstep (se 1 (by rfl) ⟨1383287, by rfl⟩ : syracuseStep 1844383 = 2766575) B2766575
theorem B6227279 : Blo 1843623 6227279 := bstep (se 1 (by rfl) ⟨4670459, by rfl⟩ : syracuseStep 6227279 = 9340919) B9340919
theorem B11814311 : Blo 1843623 11814311 := bstep (se 1 (by rfl) ⟨8860733, by rfl⟩ : syracuseStep 11814311 = 17721467) B17721467
theorem B1844687 : Blo 1843623 1844687 := bstep (se 1 (by rfl) ⟨1383515, by rfl⟩ : syracuseStep 1844687 = 2767031) B2767031
theorem B1844719 : Blo 1843623 1844719 := bstep (se 1 (by rfl) ⟨1383539, by rfl⟩ : syracuseStep 1844719 = 2767079) B2767079
theorem B17720851 : Blo 1843623 17720851 := bstep (se 1 (by rfl) ⟨13290638, by rfl⟩ : syracuseStep 17720851 = 26581277) B26581277
theorem B4671067 : Blo 1843623 4671067 := bstep (se 1 (by rfl) ⟨3503300, by rfl⟩ : syracuseStep 4671067 = 7006601) B7006601
theorem B9971423 : Blo 1843623 9971423 := bstep (se 1 (by rfl) ⟨7478567, by rfl⟩ : syracuseStep 9971423 = 14957135) B14957135
theorem B1844967 : Blo 1843623 1844967 := bstep (se 1 (by rfl) ⟨1383725, by rfl⟩ : syracuseStep 1844967 = 2767451) B2767451
theorem B1845063 : Blo 1843623 1845063 := bstep (se 1 (by rfl) ⟨1383797, by rfl⟩ : syracuseStep 1845063 = 2767595) B2767595
theorem B2074459 : Blo 1843623 2074459 := bstep (se 1 (by rfl) ⟨1555844, by rfl⟩ : syracuseStep 2074459 = 3111689) B3111689
theorem B1845083 : Blo 1843623 1845083 := bstep (se 1 (by rfl) ⟨1383812, by rfl⟩ : syracuseStep 1845083 = 2767625) B2767625
theorem B11216879 : Blo 1843623 11216879 := bstep (se 1 (by rfl) ⟨8412659, by rfl⟩ : syracuseStep 11216879 = 16825319) B16825319
theorem B3737831 : Blo 1843623 3737831 := bstep (se 1 (by rfl) ⟨2803373, by rfl⟩ : syracuseStep 3737831 = 5606747) B5606747
theorem B7006571 : Blo 1843623 7006571 := bstep (se 1 (by rfl) ⟨5254928, by rfl⟩ : syracuseStep 7006571 = 10509857) B10509857
theorem B21006863 : Blo 1843623 21006863 := bstep (se 1 (by rfl) ⟨15755147, by rfl⟩ : syracuseStep 21006863 = 31510295) B31510295
theorem B14953007 : Blo 1843623 14953007 := bstep (se 1 (by rfl) ⟨11214755, by rfl⟩ : syracuseStep 14953007 = 22429511) B22429511
theorem B17721929 : Blo 1843623 17721929 := bstep (se 2 (by rfl) ⟨6645723, by rfl⟩ : syracuseStep 17721929 = 13291447) B13291447
theorem B35457695 : Blo 1843623 35457695 := bstep (se 1 (by rfl) ⟨26593271, by rfl⟩ : syracuseStep 35457695 = 53186543) B53186543
theorem B11217773 : Blo 1843623 11217773 := bstep (se 3 (by rfl) ⟨2103332, by rfl⟩ : syracuseStep 11217773 = 4206665) B4206665
theorem B2075503 : Blo 1843623 2075503 := bstep (se 1 (by rfl) ⟨1556627, by rfl⟩ : syracuseStep 2075503 = 3113255) B3113255
theorem B9341891 : Blo 1843623 9341891 := bstep (se 1 (by rfl) ⟨7006418, by rfl⟩ : syracuseStep 9341891 = 14012837) B14012837
theorem B54660295 : Blo 1843623 54660295 := bstep (se 1 (by rfl) ⟨40995221, by rfl⟩ : syracuseStep 54660295 = 81990443) B81990443
theorem B5909719 : Blo 1843623 5909719 := bstep (se 1 (by rfl) ⟨4432289, by rfl⟩ : syracuseStep 5909719 = 8864579) B8864579
theorem B10505483 : Blo 1843623 10505483 := bstep (se 1 (by rfl) ⟨7879112, by rfl⟩ : syracuseStep 10505483 = 15758225) B15758225
theorem B2625095 : Blo 1843623 2625095 := bstep (se 1 (by rfl) ⟨1968821, by rfl⟩ : syracuseStep 2625095 = 3937643) B3937643
theorem B14004089 : Blo 1843623 14004089 := bstep (se 2 (by rfl) ⟨5251533, by rfl⟩ : syracuseStep 14004089 = 10503067) B10503067
theorem B5394313 : Blo 1843623 5394313 := bstep (se 2 (by rfl) ⟨2022867, by rfl⟩ : syracuseStep 5394313 = 4045735) B4045735
theorem B17977243 : Blo 1843623 17977243 := bstep (se 1 (by rfl) ⟨13482932, by rfl⟩ : syracuseStep 17977243 = 26965865) B26965865
theorem B21008321 : Blo 1843623 21008321 := bstep (se 2 (by rfl) ⟨7878120, by rfl⟩ : syracuseStep 21008321 = 15756241) B15756241
theorem B5992663 : Blo 1843623 5992663 := bstep (se 1 (by rfl) ⟨4494497, by rfl⟩ : syracuseStep 5992663 = 8988995) B8988995
theorem B6648203 : Blo 1843623 6648203 := bstep (se 1 (by rfl) ⟨4986152, by rfl⟩ : syracuseStep 6648203 = 9972305) B9972305
theorem B5992937 : Blo 1843623 5992937 := bstep (se 2 (by rfl) ⟨2247351, by rfl⟩ : syracuseStep 5992937 = 4494703) B4494703
theorem B1970735 : Blo 1843623 1970735 := bstep (se 1 (by rfl) ⟨1478051, by rfl⟩ : syracuseStep 1970735 = 2956103) B2956103
theorem B14963363 : Blo 1843623 14963363 := bstep (se 1 (by rfl) ⟨11222522, by rfl⟩ : syracuseStep 14963363 = 22445045) B22445045
theorem B2765519 : Blo 1843623 2765519 := bstep (se 1 (by rfl) ⟨2074139, by rfl⟩ : syracuseStep 2765519 = 4148279) B4148279
theorem B4150079 : Blo 1843623 4150079 := bstep (se 1 (by rfl) ⟨3112559, by rfl⟩ : syracuseStep 4150079 = 6225119) B6225119
theorem B19952567 : Blo 1843623 19952567 := bstep (se 1 (by rfl) ⟨14964425, by rfl⟩ : syracuseStep 19952567 = 29928851) B29928851
theorem B23630777 : Blo 1843623 23630777 := bstep (se 2 (by rfl) ⟨8861541, by rfl⟩ : syracuseStep 23630777 = 17723083) B17723083
theorem B2765807 : Blo 1843623 2765807 := bstep (se 1 (by rfl) ⟨2074355, by rfl⟩ : syracuseStep 2765807 = 4148711) B4148711
theorem B2626553 : Blo 1843623 2626553 := bstep (se 2 (by rfl) ⟨984957, by rfl⟩ : syracuseStep 2626553 = 1969915) B1969915
theorem B7877695 : Blo 1843623 7877695 := bstep (se 1 (by rfl) ⟨5908271, by rfl⟩ : syracuseStep 7877695 = 11816543) B11816543
theorem B3503225 : Blo 1843623 3503225 := bstep (se 2 (by rfl) ⟨1313709, by rfl⟩ : syracuseStep 3503225 = 2627419) B2627419
theorem B11818183 : Blo 1843623 11818183 := bstep (se 1 (by rfl) ⟨8863637, by rfl⟩ : syracuseStep 11818183 = 17727275) B17727275
theorem B8860927 : Blo 1843623 8860927 := bstep (se 1 (by rfl) ⟨6645695, by rfl⟩ : syracuseStep 8860927 = 13291391) B13291391
theorem B4265279 : Blo 1843623 4265279 := bstep (se 1 (by rfl) ⟨3198959, by rfl⟩ : syracuseStep 4265279 = 6397919) B6397919
theorem B2766191 : Blo 1843623 2766191 := bstep (se 1 (by rfl) ⟨2074643, by rfl⟩ : syracuseStep 2766191 = 4149287) B4149287
theorem B4666855 : Blo 1843623 4666855 := bstep (se 1 (by rfl) ⟨3500141, by rfl⟩ : syracuseStep 4666855 = 7000283) B7000283
theorem B2766311 : Blo 1843623 2766311 := bstep (se 1 (by rfl) ⟨2074733, by rfl⟩ : syracuseStep 2766311 = 4149467) B4149467
theorem B26605037 : Blo 1843623 26605037 := bstep (se 3 (by rfl) ⟨4988444, by rfl⟩ : syracuseStep 26605037 = 9976889) B9976889
theorem B8861177 : Blo 1843623 8861177 := bstep (se 2 (by rfl) ⟨3322941, by rfl⟩ : syracuseStep 8861177 = 6645883) B6645883
theorem B2766491 : Blo 1843623 2766491 := bstep (se 1 (by rfl) ⟨2074868, by rfl⟩ : syracuseStep 2766491 = 4149737) B4149737
theorem B10507967 : Blo 1843623 10507967 := bstep (se 1 (by rfl) ⟨7880975, by rfl⟩ : syracuseStep 10507967 = 15761951) B15761951
theorem B3323771 : Blo 1843623 3323771 := bstep (se 1 (by rfl) ⟨2492828, by rfl⟩ : syracuseStep 3323771 = 4985657) B4985657
theorem B4667291 : Blo 1843623 4667291 := bstep (se 1 (by rfl) ⟨3500468, by rfl⟩ : syracuseStep 4667291 = 7000937) B7000937
theorem B2766827 : Blo 1843623 2766827 := bstep (se 1 (by rfl) ⟨2075120, by rfl⟩ : syracuseStep 2766827 = 4150241) B4150241
theorem B2955295 : Blo 1843623 2955295 := bstep (se 1 (by rfl) ⟨2216471, by rfl⟩ : syracuseStep 2955295 = 4432943) B4432943
theorem B2766911 : Blo 1843623 2766911 := bstep (se 1 (by rfl) ⟨2075183, by rfl⟩ : syracuseStep 2766911 = 4150367) B4150367
theorem B3938377 : Blo 1843623 3938377 := bstep (se 2 (by rfl) ⟨1476891, by rfl⟩ : syracuseStep 3938377 = 2953783) B2953783
theorem B4151483 : Blo 1843623 4151483 := bstep (se 1 (by rfl) ⟨3113612, by rfl⟩ : syracuseStep 4151483 = 6227225) B6227225
theorem B2767241 : Blo 1843623 2767241 := bstep (se 2 (by rfl) ⟨1037715, by rfl⟩ : syracuseStep 2767241 = 2075431) B2075431
theorem B10508717 : Blo 1843623 10508717 := bstep (se 3 (by rfl) ⟨1970384, by rfl⟩ : syracuseStep 10508717 = 3940769) B3940769
theorem B6224363 : Blo 1843623 6224363 := bstep (se 1 (by rfl) ⟨4668272, by rfl⟩ : syracuseStep 6224363 = 9336545) B9336545
theorem B2767415 : Blo 1843623 2767415 := bstep (se 1 (by rfl) ⟨2075561, by rfl⟩ : syracuseStep 2767415 = 4151123) B4151123
theorem B4152167 : Blo 1843623 4152167 := bstep (se 1 (by rfl) ⟨3114125, by rfl⟩ : syracuseStep 4152167 = 6228251) B6228251
theorem B2767739 : Blo 1843623 2767739 := bstep (se 1 (by rfl) ⟨2075804, by rfl⟩ : syracuseStep 2767739 = 4151609) B4151609
theorem B4152275 : Blo 1843623 4152275 := bstep (se 1 (by rfl) ⟨3114206, by rfl⟩ : syracuseStep 4152275 = 6228413) B6228413
theorem B4152383 : Blo 1843623 4152383 := bstep (se 1 (by rfl) ⟨3114287, by rfl⟩ : syracuseStep 4152383 = 6228575) B6228575
theorem B9338003 : Blo 1843623 9338003 := bstep (se 1 (by rfl) ⟨7003502, by rfl⟩ : syracuseStep 9338003 = 14007005) B14007005
theorem B4152545 : Blo 1843623 4152545 := bstep (se 2 (by rfl) ⟨1557204, by rfl⟩ : syracuseStep 4152545 = 3114409) B3114409
theorem B15760615 : Blo 1843623 15760615 := bstep (se 1 (by rfl) ⟨11820461, by rfl⟩ : syracuseStep 15760615 = 23640923) B23640923
theorem B47291687 : Blo 1843623 47291687 := bstep (se 1 (by rfl) ⟨35468765, by rfl⟩ : syracuseStep 47291687 = 70937531) B70937531
theorem B4431311 : Blo 1843623 4431311 := bstep (se 1 (by rfl) ⟨3323483, by rfl⟩ : syracuseStep 4431311 = 6646967) B6646967
theorem B2768351 : Blo 1843623 2768351 := bstep (se 1 (by rfl) ⟨2076263, by rfl⟩ : syracuseStep 2768351 = 4152527) B4152527
theorem B13303385 : Blo 1843623 13303385 := bstep (se 2 (by rfl) ⟨4988769, by rfl⟩ : syracuseStep 13303385 = 9977539) B9977539
theorem B5251169 : Blo 1843623 5251169 := bstep (se 2 (by rfl) ⟨1969188, by rfl⟩ : syracuseStep 5251169 = 3938377) B3938377
theorem B14008463 : Blo 1843623 14008463 := bstep (se 1 (by rfl) ⟨10506347, by rfl⟩ : syracuseStep 14008463 = 21012695) B21012695
theorem B15761573 : Blo 1843623 15761573 := bstep (se 4 (by rfl) ⟨1477647, by rfl⟩ : syracuseStep 15761573 = 2955295) B2955295
theorem B3113167 : Blo 1843623 3113167 := bstep (se 1 (by rfl) ⟨2334875, by rfl⟩ : syracuseStep 3113167 = 4669751) B4669751
theorem B6226145 : Blo 1843623 6226145 := bstep (se 2 (by rfl) ⟨2334804, by rfl⟩ : syracuseStep 6226145 = 4669609) B4669609
theorem B1843679 : Blo 1843623 1843679 := bstep (se 1 (by rfl) ⟨1382759, by rfl⟩ : syracuseStep 1843679 = 2765519) B2765519
theorem B6226523 : Blo 1843623 6226523 := bstep (se 1 (by rfl) ⟨4669892, by rfl⟩ : syracuseStep 6226523 = 9339785) B9339785
theorem B15753851 : Blo 1843623 15753851 := bstep (se 1 (by rfl) ⟨11815388, by rfl⟩ : syracuseStep 15753851 = 23630777) B23630777
theorem B1843871 : Blo 1843623 1843871 := bstep (se 1 (by rfl) ⟨1382903, by rfl⟩ : syracuseStep 1843871 = 2765807) B2765807
theorem B2335483 : Blo 1843623 2335483 := bstep (se 1 (by rfl) ⟨1751612, by rfl⟩ : syracuseStep 2335483 = 3503225) B3503225
theorem B2843519 : Blo 1843623 2843519 := bstep (se 1 (by rfl) ⟨2132639, by rfl⟩ : syracuseStep 2843519 = 4265279) B4265279
theorem B1844127 : Blo 1843623 1844127 := bstep (se 1 (by rfl) ⟨1383095, by rfl⟩ : syracuseStep 1844127 = 2766191) B2766191
theorem B1844207 : Blo 1843623 1844207 := bstep (se 1 (by rfl) ⟨1383155, by rfl⟩ : syracuseStep 1844207 = 2766311) B2766311
theorem B17736691 : Blo 1843623 17736691 := bstep (se 1 (by rfl) ⟨13302518, by rfl⟩ : syracuseStep 17736691 = 26605037) B26605037
theorem B17728541 : Blo 1843623 17728541 := bstep (se 3 (by rfl) ⟨3324101, by rfl⟩ : syracuseStep 17728541 = 6648203) B6648203
theorem B1844327 : Blo 1843623 1844327 := bstep (se 1 (by rfl) ⟨1383245, by rfl⟩ : syracuseStep 1844327 = 2766491) B2766491
theorem B7005311 : Blo 1843623 7005311 := bstep (se 1 (by rfl) ⟨5253983, by rfl⟩ : syracuseStep 7005311 = 10507967) B10507967
theorem B1844551 : Blo 1843623 1844551 := bstep (se 1 (by rfl) ⟨1383413, by rfl⟩ : syracuseStep 1844551 = 2766827) B2766827
theorem B1844607 : Blo 1843623 1844607 := bstep (se 1 (by rfl) ⟨1383455, by rfl⟩ : syracuseStep 1844607 = 2766911) B2766911
theorem B10503593 : Blo 1843623 10503593 := bstep (se 2 (by rfl) ⟨3938847, by rfl⟩ : syracuseStep 10503593 = 7877695) B7877695
theorem B4671047 : Blo 1843623 4671047 := bstep (se 1 (by rfl) ⟨3503285, by rfl⟩ : syracuseStep 4671047 = 7006571) B7006571
theorem B1844827 : Blo 1843623 1844827 := bstep (se 1 (by rfl) ⟨1383620, by rfl⟩ : syracuseStep 1844827 = 2767241) B2767241
theorem B7005811 : Blo 1843623 7005811 := bstep (se 1 (by rfl) ⟨5254358, by rfl⟩ : syracuseStep 7005811 = 10508717) B10508717
theorem B21014153 : Blo 1843623 21014153 := bstep (se 2 (by rfl) ⟨7880307, by rfl⟩ : syracuseStep 21014153 = 15760615) B15760615
theorem B11814569 : Blo 1843623 11814569 := bstep (se 2 (by rfl) ⟨4430463, by rfl⟩ : syracuseStep 11814569 = 8860927) B8860927
theorem B1844943 : Blo 1843623 1844943 := bstep (se 1 (by rfl) ⟨1383707, by rfl⟩ : syracuseStep 1844943 = 2767415) B2767415
theorem B11814619 : Blo 1843623 11814619 := bstep (se 1 (by rfl) ⟨8860964, by rfl⟩ : syracuseStep 11814619 = 17721929) B17721929
theorem B1845159 : Blo 1843623 1845159 := bstep (se 1 (by rfl) ⟨1383869, by rfl⟩ : syracuseStep 1845159 = 2767739) B2767739
theorem B6227927 : Blo 1843623 6227927 := bstep (se 1 (by rfl) ⟨4670945, by rfl⟩ : syracuseStep 6227927 = 9341891) B9341891
theorem B23627801 : Blo 1843623 23627801 := bstep (se 2 (by rfl) ⟨8860425, by rfl⟩ : syracuseStep 23627801 = 17720851) B17720851
theorem B6228089 : Blo 1843623 6228089 := bstep (se 2 (by rfl) ⟨2335533, by rfl⟩ : syracuseStep 6228089 = 4671067) B4671067
theorem B1845567 : Blo 1843623 1845567 := bstep (se 1 (by rfl) ⟨1384175, by rfl⟩ : syracuseStep 1845567 = 2768351) B2768351
theorem B7990217 : Blo 1843623 7990217 := bstep (se 2 (by rfl) ⟨2996331, by rfl⟩ : syracuseStep 7990217 = 5992663) B5992663
theorem B3501083 : Blo 1843623 3501083 := bstep (se 1 (by rfl) ⟨2625812, by rfl⟩ : syracuseStep 3501083 = 5251625) B5251625
theorem B76721737 : Blo 1843623 76721737 := bstep (se 2 (by rfl) ⟨28770651, by rfl⟩ : syracuseStep 76721737 = 57541303) B57541303
theorem B7876207 : Blo 1843623 7876207 := bstep (se 1 (by rfl) ⟨5907155, by rfl⟩ : syracuseStep 7876207 = 11814311) B11814311
theorem B6647615 : Blo 1843623 6647615 := bstep (se 1 (by rfl) ⟨4985711, by rfl⟩ : syracuseStep 6647615 = 9971423) B9971423
theorem B2215847 : Blo 1843623 2215847 := bstep (se 1 (by rfl) ⟨1661885, by rfl⟩ : syracuseStep 2215847 = 3323771) B3323771
theorem B23629805 : Blo 1843623 23629805 := bstep (se 3 (by rfl) ⟨4430588, by rfl⟩ : syracuseStep 23629805 = 8861177) B8861177
theorem B5255293 : Blo 1843623 5255293 := bstep (se 3 (by rfl) ⟨985367, by rfl⟩ : syracuseStep 5255293 = 1970735) B1970735
theorem B7000253 : Blo 1843623 7000253 := bstep (se 3 (by rfl) ⟨1312547, by rfl⟩ : syracuseStep 7000253 = 2625095) B2625095
theorem B15757577 : Blo 1843623 15757577 := bstep (se 2 (by rfl) ⟨5909091, by rfl⟩ : syracuseStep 15757577 = 11818183) B11818183
theorem B72880393 : Blo 1843623 72880393 := bstep (se 2 (by rfl) ⟨27330147, by rfl⟩ : syracuseStep 72880393 = 54660295) B54660295
theorem B4149575 : Blo 1843623 4149575 := bstep (se 1 (by rfl) ⟨3112181, by rfl⟩ : syracuseStep 4149575 = 6224363) B6224363
theorem B14004575 : Blo 1843623 14004575 := bstep (se 1 (by rfl) ⟨10503431, by rfl⟩ : syracuseStep 14004575 = 21006863) B21006863
theorem B23638463 : Blo 1843623 23638463 := bstep (se 1 (by rfl) ⟨17728847, by rfl⟩ : syracuseStep 23638463 = 35457695) B35457695
theorem B6222473 : Blo 1843623 6222473 := bstep (se 2 (by rfl) ⟨2333427, by rfl⟩ : syracuseStep 6222473 = 4666855) B4666855
theorem B31527791 : Blo 1843623 31527791 := bstep (se 1 (by rfl) ⟨23645843, by rfl⟩ : syracuseStep 31527791 = 47291687) B47291687
theorem B2954207 : Blo 1843623 2954207 := bstep (se 1 (by rfl) ⟨2215655, by rfl⟩ : syracuseStep 2954207 = 4431311) B4431311
theorem B8868923 : Blo 1843623 8868923 := bstep (se 1 (by rfl) ⟨6651692, by rfl⟩ : syracuseStep 8868923 = 13303385) B13303385
theorem B2765945 : Blo 1843623 2765945 := bstep (se 2 (by rfl) ⟨1037229, by rfl⟩ : syracuseStep 2765945 = 2074459) B2074459
theorem B9336059 : Blo 1843623 9336059 := bstep (se 1 (by rfl) ⟨7002044, by rfl⟩ : syracuseStep 9336059 = 14004089) B14004089
theorem B14005547 : Blo 1843623 14005547 := bstep (se 1 (by rfl) ⟨10504160, by rfl⟩ : syracuseStep 14005547 = 21008321) B21008321
theorem B7476799 : Blo 1843623 7476799 := bstep (se 1 (by rfl) ⟨5607599, by rfl⟩ : syracuseStep 7476799 = 11215199) B11215199
theorem B3995291 : Blo 1843623 3995291 := bstep (se 1 (by rfl) ⟨2996468, by rfl⟩ : syracuseStep 3995291 = 5992937) B5992937
theorem B9975575 : Blo 1843623 9975575 := bstep (se 1 (by rfl) ⟨7481681, by rfl⟩ : syracuseStep 9975575 = 14963363) B14963363
theorem B2766719 : Blo 1843623 2766719 := bstep (se 1 (by rfl) ⟨2075039, by rfl⟩ : syracuseStep 2766719 = 4150079) B4150079
theorem B9967549 : Blo 1843623 9967549 := bstep (se 3 (by rfl) ⟨1868915, by rfl⟩ : syracuseStep 9967549 = 3737831) B3737831
theorem B13301711 : Blo 1843623 13301711 := bstep (se 1 (by rfl) ⟨9976283, by rfl⟩ : syracuseStep 13301711 = 19952567) B19952567
theorem B4151519 : Blo 1843623 4151519 := bstep (se 1 (by rfl) ⟨3113639, by rfl⟩ : syracuseStep 4151519 = 6227279) B6227279
theorem B2767337 : Blo 1843623 2767337 := bstep (se 2 (by rfl) ⟨1037751, by rfl⟩ : syracuseStep 2767337 = 2075503) B2075503
theorem B3111527 : Blo 1843623 3111527 := bstep (se 1 (by rfl) ⟨2333645, by rfl⟩ : syracuseStep 3111527 = 4667291) B4667291
theorem B7477919 : Blo 1843623 7477919 := bstep (se 1 (by rfl) ⟨5608439, by rfl⟩ : syracuseStep 7477919 = 11216879) B11216879
theorem B2767655 : Blo 1843623 2767655 := bstep (se 1 (by rfl) ⟨2075741, by rfl⟩ : syracuseStep 2767655 = 4151483) B4151483
theorem B7879625 : Blo 1843623 7879625 := bstep (se 2 (by rfl) ⟨2954859, by rfl⟩ : syracuseStep 7879625 = 5909719) B5909719
theorem B9968671 : Blo 1843623 9968671 := bstep (se 1 (by rfl) ⟨7476503, by rfl⟩ : syracuseStep 9968671 = 14953007) B14953007
theorem B2768111 : Blo 1843623 2768111 := bstep (se 1 (by rfl) ⟨2076083, by rfl⟩ : syracuseStep 2768111 = 4152167) B4152167
theorem B7478515 : Blo 1843623 7478515 := bstep (se 1 (by rfl) ⟨5608886, by rfl⟩ : syracuseStep 7478515 = 11217773) B11217773
theorem B2768183 : Blo 1843623 2768183 := bstep (se 1 (by rfl) ⟨2076137, by rfl⟩ : syracuseStep 2768183 = 4152275) B4152275
theorem B2768255 : Blo 1843623 2768255 := bstep (se 1 (by rfl) ⟨2076191, by rfl⟩ : syracuseStep 2768255 = 4152383) B4152383
theorem B6225335 : Blo 1843623 6225335 := bstep (se 1 (by rfl) ⟨4669001, by rfl⟩ : syracuseStep 6225335 = 9338003) B9338003
theorem B2768363 : Blo 1843623 2768363 := bstep (se 1 (by rfl) ⟨2076272, by rfl⟩ : syracuseStep 2768363 = 4152545) B4152545
theorem B7003655 : Blo 1843623 7003655 := bstep (se 1 (by rfl) ⟨5252741, by rfl⟩ : syracuseStep 7003655 = 10505483) B10505483
theorem B7192417 : Blo 1843623 7192417 := bstep (se 2 (by rfl) ⟨2697156, by rfl⟩ : syracuseStep 7192417 = 5394313) B5394313
theorem B23969657 : Blo 1843623 23969657 := bstep (se 2 (by rfl) ⟨8988621, by rfl⟩ : syracuseStep 23969657 = 17977243) B17977243
theorem B7004141 : Blo 1843623 7004141 := bstep (se 3 (by rfl) ⟨1313276, by rfl⟩ : syracuseStep 7004141 = 2626553) B2626553
theorem B9338975 : Blo 1843623 9338975 := bstep (se 1 (by rfl) ⟨7004231, by rfl⟩ : syracuseStep 9338975 = 14008463) B14008463
theorem B97173857 : Blo 1843623 97173857 := bstep (se 2 (by rfl) ⟨36440196, by rfl⟩ : syracuseStep 97173857 = 72880393) B72880393
theorem B10502567 : Blo 1843623 10502567 := bstep (se 1 (by rfl) ⟨7876925, by rfl⟩ : syracuseStep 10502567 = 15753851) B15753851
theorem B1843963 : Blo 1843623 1843963 := bstep (se 1 (by rfl) ⟨1382972, by rfl⟩ : syracuseStep 1843963 = 2765945) B2765945
theorem B4670207 : Blo 1843623 4670207 := bstep (se 1 (by rfl) ⟨3502655, by rfl⟩ : syracuseStep 4670207 = 7005311) B7005311
theorem B3113977 : Blo 1843623 3113977 := bstep (se 2 (by rfl) ⟨1167741, by rfl⟩ : syracuseStep 3113977 = 2335483) B2335483
theorem B3114031 : Blo 1843623 3114031 := bstep (se 1 (by rfl) ⟨2335523, by rfl⟩ : syracuseStep 3114031 = 4671047) B4671047
theorem B14009435 : Blo 1843623 14009435 := bstep (se 1 (by rfl) ⟨10507076, by rfl⟩ : syracuseStep 14009435 = 21014153) B21014153
theorem B2663527 : Blo 1843623 2663527 := bstep (se 1 (by rfl) ⟨1997645, by rfl⟩ : syracuseStep 2663527 = 3995291) B3995291
theorem B1844479 : Blo 1843623 1844479 := bstep (se 1 (by rfl) ⟨1383359, by rfl⟩ : syracuseStep 1844479 = 2766719) B2766719
theorem B9971353 : Blo 1843623 9971353 := bstep (se 2 (by rfl) ⟨3739257, by rfl⟩ : syracuseStep 9971353 = 7478515) B7478515
theorem B1844891 : Blo 1843623 1844891 := bstep (se 1 (by rfl) ⟨1383668, by rfl⟩ : syracuseStep 1844891 = 2767337) B2767337
theorem B2074351 : Blo 1843623 2074351 := bstep (se 1 (by rfl) ⟨1555763, by rfl⟩ : syracuseStep 2074351 = 3111527) B3111527
theorem B1845103 : Blo 1843623 1845103 := bstep (se 1 (by rfl) ⟨1383827, by rfl⟩ : syracuseStep 1845103 = 2767655) B2767655
theorem B5253083 : Blo 1843623 5253083 := bstep (se 1 (by rfl) ⟨3939812, by rfl⟩ : syracuseStep 5253083 = 7879625) B7879625
theorem B5326811 : Blo 1843623 5326811 := bstep (se 1 (by rfl) ⟨3995108, by rfl⟩ : syracuseStep 5326811 = 7990217) B7990217
theorem B102295649 : Blo 1843623 102295649 := bstep (se 2 (by rfl) ⟨38360868, by rfl⟩ : syracuseStep 102295649 = 76721737) B76721737
theorem B9341081 : Blo 1843623 9341081 := bstep (se 2 (by rfl) ⟨3502905, by rfl⟩ : syracuseStep 9341081 = 7005811) B7005811
theorem B1845407 : Blo 1843623 1845407 := bstep (se 1 (by rfl) ⟨1384055, by rfl⟩ : syracuseStep 1845407 = 2768111) B2768111
theorem B1845455 : Blo 1843623 1845455 := bstep (se 1 (by rfl) ⟨1384091, by rfl⟩ : syracuseStep 1845455 = 2768183) B2768183
theorem B1845503 : Blo 1843623 1845503 := bstep (se 1 (by rfl) ⟨1384127, by rfl⟩ : syracuseStep 1845503 = 2768255) B2768255
theorem B1845575 : Blo 1843623 1845575 := bstep (se 1 (by rfl) ⟨1384181, by rfl⟩ : syracuseStep 1845575 = 2768363) B2768363
theorem B5908925 : Blo 1843623 5908925 := bstep (se 3 (by rfl) ⟨1107923, by rfl⟩ : syracuseStep 5908925 = 2215847) B2215847
theorem B13290065 : Blo 1843623 13290065 := bstep (se 2 (by rfl) ⟨4983774, by rfl⟩ : syracuseStep 13290065 = 9967549) B9967549
theorem B7007057 : Blo 1843623 7007057 := bstep (se 2 (by rfl) ⟨2627646, by rfl⟩ : syracuseStep 7007057 = 5255293) B5255293
theorem B10505051 : Blo 1843623 10505051 := bstep (se 1 (by rfl) ⟨7878788, by rfl⟩ : syracuseStep 10505051 = 15757577) B15757577
theorem B14003117 : Blo 1843623 14003117 := bstep (se 3 (by rfl) ⟨2625584, by rfl⟩ : syracuseStep 14003117 = 5251169) B5251169
theorem B4148315 : Blo 1843623 4148315 := bstep (se 1 (by rfl) ⟨3111236, by rfl⟩ : syracuseStep 4148315 = 6222473) B6222473
theorem B1969471 : Blo 1843623 1969471 := bstep (se 1 (by rfl) ⟨1477103, by rfl⟩ : syracuseStep 1969471 = 2954207) B2954207
theorem B7876379 : Blo 1843623 7876379 := bstep (se 1 (by rfl) ⟨5907284, by rfl⟩ : syracuseStep 7876379 = 11814569) B11814569
theorem B8867807 : Blo 1843623 8867807 := bstep (se 1 (by rfl) ⟨6650855, by rfl⟩ : syracuseStep 8867807 = 13301711) B13301711
theorem B13291561 : Blo 1843623 13291561 := bstep (se 2 (by rfl) ⟨4984335, by rfl⟩ : syracuseStep 13291561 = 9968671) B9968671
theorem B4985279 : Blo 1843623 4985279 := bstep (se 1 (by rfl) ⟨3738959, by rfl⟩ : syracuseStep 4985279 = 7477919) B7477919
theorem B4150223 : Blo 1843623 4150223 := bstep (se 1 (by rfl) ⟨3112667, by rfl⟩ : syracuseStep 4150223 = 6225335) B6225335
theorem B7582717 : Blo 1843623 7582717 := bstep (se 3 (by rfl) ⟨1421759, by rfl⟩ : syracuseStep 7582717 = 2843519) B2843519
theorem B9589889 : Blo 1843623 9589889 := bstep (se 2 (by rfl) ⟨3596208, by rfl⟩ : syracuseStep 9589889 = 7192417) B7192417
theorem B15979771 : Blo 1843623 15979771 := bstep (se 1 (by rfl) ⟨11984828, by rfl⟩ : syracuseStep 15979771 = 23969657) B23969657
theorem B9336221 : Blo 1843623 9336221 := bstep (se 3 (by rfl) ⟨1750541, by rfl⟩ : syracuseStep 9336221 = 3501083) B3501083
theorem B10507715 : Blo 1843623 10507715 := bstep (se 1 (by rfl) ⟨7880786, by rfl⟩ : syracuseStep 10507715 = 15761573) B15761573
theorem B4666835 : Blo 1843623 4666835 := bstep (se 1 (by rfl) ⟨3500126, by rfl⟩ : syracuseStep 4666835 = 7000253) B7000253
theorem B4150763 : Blo 1843623 4150763 := bstep (se 1 (by rfl) ⟨3113072, by rfl⟩ : syracuseStep 4150763 = 6226145) B6226145
theorem B2766383 : Blo 1843623 2766383 := bstep (se 1 (by rfl) ⟨2074787, by rfl⟩ : syracuseStep 2766383 = 4149575) B4149575
theorem B9336383 : Blo 1843623 9336383 := bstep (se 1 (by rfl) ⟨7002287, by rfl⟩ : syracuseStep 9336383 = 14004575) B14004575
theorem B4150889 : Blo 1843623 4150889 := bstep (se 2 (by rfl) ⟨1556583, by rfl⟩ : syracuseStep 4150889 = 3113167) B3113167
theorem B15758975 : Blo 1843623 15758975 := bstep (se 1 (by rfl) ⟨11819231, by rfl⟩ : syracuseStep 15758975 = 23638463) B23638463
theorem B4151015 : Blo 1843623 4151015 := bstep (se 1 (by rfl) ⟨3113261, by rfl⟩ : syracuseStep 4151015 = 6226523) B6226523
theorem B21018527 : Blo 1843623 21018527 := bstep (se 1 (by rfl) ⟨15763895, by rfl⟩ : syracuseStep 21018527 = 31527791) B31527791
theorem B11819027 : Blo 1843623 11819027 := bstep (se 1 (by rfl) ⟨8864270, by rfl⟩ : syracuseStep 11819027 = 17728541) B17728541
theorem B5912615 : Blo 1843623 5912615 := bstep (se 1 (by rfl) ⟨4434461, by rfl⟩ : syracuseStep 5912615 = 8868923) B8868923
theorem B6224039 : Blo 1843623 6224039 := bstep (se 1 (by rfl) ⟨4668029, by rfl⟩ : syracuseStep 6224039 = 9336059) B9336059
theorem B9337031 : Blo 1843623 9337031 := bstep (se 1 (by rfl) ⟨7002773, by rfl⟩ : syracuseStep 9337031 = 14005547) B14005547
theorem B7002395 : Blo 1843623 7002395 := bstep (se 1 (by rfl) ⟨5251796, by rfl⟩ : syracuseStep 7002395 = 10503593) B10503593
theorem B6650383 : Blo 1843623 6650383 := bstep (se 1 (by rfl) ⟨4987787, by rfl⟩ : syracuseStep 6650383 = 9975575) B9975575
theorem B4151951 : Blo 1843623 4151951 := bstep (se 1 (by rfl) ⟨3113963, by rfl⟩ : syracuseStep 4151951 = 6227927) B6227927
theorem B23648921 : Blo 1843623 23648921 := bstep (se 2 (by rfl) ⟨8868345, by rfl⟩ : syracuseStep 23648921 = 17736691) B17736691
theorem B15751867 : Blo 1843623 15751867 := bstep (se 1 (by rfl) ⟨11813900, by rfl⟩ : syracuseStep 15751867 = 23627801) B23627801
theorem B4152059 : Blo 1843623 4152059 := bstep (se 1 (by rfl) ⟨3114044, by rfl⟩ : syracuseStep 4152059 = 6228089) B6228089
theorem B2767679 : Blo 1843623 2767679 := bstep (se 1 (by rfl) ⟨2075759, by rfl⟩ : syracuseStep 2767679 = 4151519) B4151519
theorem B9969065 : Blo 1843623 9969065 := bstep (se 2 (by rfl) ⟨3738399, by rfl⟩ : syracuseStep 9969065 = 7476799) B7476799
theorem B10501609 : Blo 1843623 10501609 := bstep (se 2 (by rfl) ⟨3938103, by rfl⟩ : syracuseStep 10501609 = 7876207) B7876207
theorem B15752825 : Blo 1843623 15752825 := bstep (se 2 (by rfl) ⟨5907309, by rfl⟩ : syracuseStep 15752825 = 11814619) B11814619
theorem B4669103 : Blo 1843623 4669103 := bstep (se 1 (by rfl) ⟨3501827, by rfl⟩ : syracuseStep 4669103 = 7003655) B7003655
theorem B4431743 : Blo 1843623 4431743 := bstep (se 1 (by rfl) ⟨3323807, by rfl⟩ : syracuseStep 4431743 = 6647615) B6647615
theorem B15753203 : Blo 1843623 15753203 := bstep (se 1 (by rfl) ⟨11814902, by rfl⟩ : syracuseStep 15753203 = 23629805) B23629805
theorem B4669427 : Blo 1843623 4669427 := bstep (se 1 (by rfl) ⟨3502070, by rfl⟩ : syracuseStep 4669427 = 7004141) B7004141
theorem B6225983 : Blo 1843623 6225983 := bstep (se 1 (by rfl) ⟨4669487, by rfl⟩ : syracuseStep 6225983 = 9338975) B9338975
theorem B3113471 : Blo 1843623 3113471 := bstep (se 1 (by rfl) ⟨2335103, by rfl⟩ : syracuseStep 3113471 = 4670207) B4670207
theorem B9339623 : Blo 1843623 9339623 := bstep (se 1 (by rfl) ⟨7004717, by rfl⟩ : syracuseStep 9339623 = 14009435) B14009435
theorem B259130285 : Blo 1843623 259130285 := bstep (se 3 (by rfl) ⟨48586928, by rfl⟩ : syracuseStep 259130285 = 97173857) B97173857
theorem B7005143 : Blo 1843623 7005143 := bstep (se 1 (by rfl) ⟨5253857, by rfl⟩ : syracuseStep 7005143 = 10507715) B10507715
theorem B1844255 : Blo 1843623 1844255 := bstep (se 1 (by rfl) ⟨1383191, by rfl⟩ : syracuseStep 1844255 = 2766383) B2766383
theorem B6227387 : Blo 1843623 6227387 := bstep (se 1 (by rfl) ⟨4670540, by rfl⟩ : syracuseStep 6227387 = 9341081) B9341081
theorem B1845119 : Blo 1843623 1845119 := bstep (se 1 (by rfl) ⟨1383839, by rfl⟩ : syracuseStep 1845119 = 2767679) B2767679
theorem B4671371 : Blo 1843623 4671371 := bstep (se 1 (by rfl) ⟨3503528, by rfl⟩ : syracuseStep 4671371 = 7007057) B7007057
theorem B14002145 : Blo 1843623 14002145 := bstep (se 2 (by rfl) ⟨5250804, by rfl⟩ : syracuseStep 14002145 = 10501609) B10501609
theorem B6646043 : Blo 1843623 6646043 := bstep (se 1 (by rfl) ⟨4984532, by rfl⟩ : syracuseStep 6646043 = 9969065) B9969065
theorem B17722081 : Blo 1843623 17722081 := bstep (se 2 (by rfl) ⟨6645780, by rfl⟩ : syracuseStep 17722081 = 13291561) B13291561
theorem B8867177 : Blo 1843623 8867177 := bstep (se 2 (by rfl) ⟨3325191, by rfl⟩ : syracuseStep 8867177 = 6650383) B6650383
theorem B6393259 : Blo 1843623 6393259 := bstep (se 1 (by rfl) ⟨4794944, by rfl⟩ : syracuseStep 6393259 = 9589889) B9589889
theorem B10505983 : Blo 1843623 10505983 := bstep (se 1 (by rfl) ⟨7879487, by rfl⟩ : syracuseStep 10505983 = 15758975) B15758975
theorem B14012351 : Blo 1843623 14012351 := bstep (se 1 (by rfl) ⟨10509263, by rfl⟩ : syracuseStep 14012351 = 21018527) B21018527
theorem B85225445 : Blo 1843623 85225445 := bstep (se 4 (by rfl) ⟨7989885, by rfl⟩ : syracuseStep 85225445 = 15979771) B15979771
theorem B3502055 : Blo 1843623 3502055 := bstep (se 1 (by rfl) ⟨2626541, by rfl⟩ : syracuseStep 3502055 = 5253083) B5253083
theorem B3551207 : Blo 1843623 3551207 := bstep (se 1 (by rfl) ⟨2663405, by rfl⟩ : syracuseStep 3551207 = 5326811) B5326811
theorem B4149359 : Blo 1843623 4149359 := bstep (se 1 (by rfl) ⟨3112019, by rfl⟩ : syracuseStep 4149359 = 6224039) B6224039
theorem B3551369 : Blo 1843623 3551369 := bstep (se 2 (by rfl) ⟨1331763, by rfl⟩ : syracuseStep 3551369 = 2663527) B2663527
theorem B8860043 : Blo 1843623 8860043 := bstep (se 1 (by rfl) ⟨6645032, by rfl⟩ : syracuseStep 8860043 = 13290065) B13290065
theorem B2625961 : Blo 1843623 2625961 := bstep (se 2 (by rfl) ⟨984735, by rfl⟩ : syracuseStep 2625961 = 1969471) B1969471
theorem B15765947 : Blo 1843623 15765947 := bstep (se 1 (by rfl) ⟨11824460, by rfl⟩ : syracuseStep 15765947 = 23648921) B23648921
theorem B9335411 : Blo 1843623 9335411 := bstep (se 1 (by rfl) ⟨7001558, by rfl⟩ : syracuseStep 9335411 = 14003117) B14003117
theorem B2765543 : Blo 1843623 2765543 := bstep (se 1 (by rfl) ⟨2074157, by rfl⟩ : syracuseStep 2765543 = 4148315) B4148315
theorem B2765801 : Blo 1843623 2765801 := bstep (se 2 (by rfl) ⟨1037175, by rfl⟩ : syracuseStep 2765801 = 2074351) B2074351
theorem B2954495 : Blo 1843623 2954495 := bstep (se 1 (by rfl) ⟨2215871, by rfl⟩ : syracuseStep 2954495 = 4431743) B4431743
theorem B5911871 : Blo 1843623 5911871 := bstep (se 1 (by rfl) ⟨4433903, by rfl⟩ : syracuseStep 5911871 = 8867807) B8867807
theorem B40441157 : Blo 1843623 40441157 := bstep (se 4 (by rfl) ⟨3791358, by rfl⟩ : syracuseStep 40441157 = 7582717) B7582717
theorem B15766973 : Blo 1843623 15766973 := bstep (se 3 (by rfl) ⟨2956307, by rfl⟩ : syracuseStep 15766973 = 5912615) B5912615
theorem B7001711 : Blo 1843623 7001711 := bstep (se 1 (by rfl) ⟨5251283, by rfl⟩ : syracuseStep 7001711 = 10502567) B10502567
theorem B3323519 : Blo 1843623 3323519 := bstep (se 1 (by rfl) ⟨2492639, by rfl⟩ : syracuseStep 3323519 = 4985279) B4985279
theorem B2766815 : Blo 1843623 2766815 := bstep (se 1 (by rfl) ⟨2075111, by rfl⟩ : syracuseStep 2766815 = 4150223) B4150223
theorem B53180549 : Blo 1843623 53180549 := bstep (se 4 (by rfl) ⟨4985676, by rfl⟩ : syracuseStep 53180549 = 9971353) B9971353
theorem B21002489 : Blo 1843623 21002489 := bstep (se 2 (by rfl) ⟨7875933, by rfl⟩ : syracuseStep 21002489 = 15751867) B15751867
theorem B6224147 : Blo 1843623 6224147 := bstep (se 1 (by rfl) ⟨4668110, by rfl⟩ : syracuseStep 6224147 = 9336221) B9336221
theorem B3111223 : Blo 1843623 3111223 := bstep (se 1 (by rfl) ⟨2333417, by rfl⟩ : syracuseStep 3111223 = 4666835) B4666835
theorem B2767175 : Blo 1843623 2767175 := bstep (se 1 (by rfl) ⟨2075381, by rfl⟩ : syracuseStep 2767175 = 4150763) B4150763
theorem B6224255 : Blo 1843623 6224255 := bstep (se 1 (by rfl) ⟨4668191, by rfl⟩ : syracuseStep 6224255 = 9336383) B9336383
theorem B2767259 : Blo 1843623 2767259 := bstep (se 1 (by rfl) ⟨2075444, by rfl⟩ : syracuseStep 2767259 = 4150889) B4150889
theorem B2767343 : Blo 1843623 2767343 := bstep (se 1 (by rfl) ⟨2075507, by rfl⟩ : syracuseStep 2767343 = 4151015) B4151015
theorem B4151969 : Blo 1843623 4151969 := bstep (se 2 (by rfl) ⟨1556988, by rfl⟩ : syracuseStep 4151969 = 3113977) B3113977
theorem B7879351 : Blo 1843623 7879351 := bstep (se 1 (by rfl) ⟨5909513, by rfl⟩ : syracuseStep 7879351 = 11819027) B11819027
theorem B4152041 : Blo 1843623 4152041 := bstep (se 2 (by rfl) ⟨1557015, by rfl⟩ : syracuseStep 4152041 = 3114031) B3114031
theorem B68197099 : Blo 1843623 68197099 := bstep (se 1 (by rfl) ⟨51147824, by rfl⟩ : syracuseStep 68197099 = 102295649) B102295649
theorem B6224687 : Blo 1843623 6224687 := bstep (se 1 (by rfl) ⟨4668515, by rfl⟩ : syracuseStep 6224687 = 9337031) B9337031
theorem B4668263 : Blo 1843623 4668263 := bstep (se 1 (by rfl) ⟨3501197, by rfl⟩ : syracuseStep 4668263 = 7002395) B7002395
theorem B3939283 : Blo 1843623 3939283 := bstep (se 1 (by rfl) ⟨2954462, by rfl⟩ : syracuseStep 3939283 = 5908925) B5908925
theorem B3112951 : Blo 1843623 3112951 := bstep (se 1 (by rfl) ⟨2334713, by rfl⟩ : syracuseStep 3112951 = 4669427) B4669427
theorem B2767967 : Blo 1843623 2767967 := bstep (se 1 (by rfl) ⟨2075975, by rfl⟩ : syracuseStep 2767967 = 4151951) B4151951
theorem B2768039 : Blo 1843623 2768039 := bstep (se 1 (by rfl) ⟨2076029, by rfl⟩ : syracuseStep 2768039 = 4152059) B4152059
theorem B7003367 : Blo 1843623 7003367 := bstep (se 1 (by rfl) ⟨5252525, by rfl⟩ : syracuseStep 7003367 = 10505051) B10505051
theorem B10501883 : Blo 1843623 10501883 := bstep (se 1 (by rfl) ⟨7876412, by rfl⟩ : syracuseStep 10501883 = 15752825) B15752825
theorem B3112735 : Blo 1843623 3112735 := bstep (se 1 (by rfl) ⟨2334551, by rfl⟩ : syracuseStep 3112735 = 4669103) B4669103
theorem B5250919 : Blo 1843623 5250919 := bstep (se 1 (by rfl) ⟨3938189, by rfl⟩ : syracuseStep 5250919 = 7876379) B7876379
theorem B10502135 : Blo 1843623 10502135 := bstep (se 1 (by rfl) ⟨7876601, by rfl⟩ : syracuseStep 10502135 = 15753203) B15753203
theorem B5906695 : Blo 1843623 5906695 := bstep (se 1 (by rfl) ⟨4430021, by rfl⟩ : syracuseStep 5906695 = 8860043) B8860043
theorem B10510631 : Blo 1843623 10510631 := bstep (se 1 (by rfl) ⟨7882973, by rfl⟩ : syracuseStep 10510631 = 15765947) B15765947
theorem B1843695 : Blo 1843623 1843695 := bstep (se 1 (by rfl) ⟨1382771, by rfl⟩ : syracuseStep 1843695 = 2765543) B2765543
theorem B6226415 : Blo 1843623 6226415 := bstep (se 1 (by rfl) ⟨4669811, by rfl⟩ : syracuseStep 6226415 = 9339623) B9339623
theorem B172753523 : Blo 1843623 172753523 := bstep (se 1 (by rfl) ⟨129565142, by rfl⟩ : syracuseStep 172753523 = 259130285) B259130285
theorem B4670095 : Blo 1843623 4670095 := bstep (se 1 (by rfl) ⟨3502571, by rfl⟩ : syracuseStep 4670095 = 7005143) B7005143
theorem B1843867 : Blo 1843623 1843867 := bstep (se 1 (by rfl) ⟨1382900, by rfl⟩ : syracuseStep 1843867 = 2765801) B2765801
theorem B26960771 : Blo 1843623 26960771 := bstep (se 1 (by rfl) ⟨20220578, by rfl⟩ : syracuseStep 26960771 = 40441157) B40441157
theorem B10511315 : Blo 1843623 10511315 := bstep (se 1 (by rfl) ⟨7883486, by rfl⟩ : syracuseStep 10511315 = 15766973) B15766973
theorem B3114247 : Blo 1843623 3114247 := bstep (se 1 (by rfl) ⟨2335685, by rfl⟩ : syracuseStep 3114247 = 4671371) B4671371
theorem B5252377 : Blo 1843623 5252377 := bstep (se 2 (by rfl) ⟨1969641, by rfl⟩ : syracuseStep 5252377 = 3939283) B3939283
theorem B1844543 : Blo 1843623 1844543 := bstep (se 1 (by rfl) ⟨1383407, by rfl⟩ : syracuseStep 1844543 = 2766815) B2766815
theorem B37881269 : Blo 1843623 37881269 := bstep (se 5 (by rfl) ⟨1775684, by rfl⟩ : syracuseStep 37881269 = 3551369) B3551369
theorem B14001659 : Blo 1843623 14001659 := bstep (se 1 (by rfl) ⟨10501244, by rfl⟩ : syracuseStep 14001659 = 21002489) B21002489
theorem B1844783 : Blo 1843623 1844783 := bstep (se 1 (by rfl) ⟨1383587, by rfl⟩ : syracuseStep 1844783 = 2767175) B2767175
theorem B1844839 : Blo 1843623 1844839 := bstep (se 1 (by rfl) ⟨1383629, by rfl⟩ : syracuseStep 1844839 = 2767259) B2767259
theorem B1844895 : Blo 1843623 1844895 := bstep (se 1 (by rfl) ⟨1383671, by rfl⟩ : syracuseStep 1844895 = 2767343) B2767343
theorem B1845311 : Blo 1843623 1845311 := bstep (se 1 (by rfl) ⟨1383983, by rfl⟩ : syracuseStep 1845311 = 2767967) B2767967
theorem B1845359 : Blo 1843623 1845359 := bstep (se 1 (by rfl) ⟨1384019, by rfl⟩ : syracuseStep 1845359 = 2768039) B2768039
theorem B34097381 : Blo 1843623 34097381 := bstep (se 4 (by rfl) ⟨3196629, by rfl⟩ : syracuseStep 34097381 = 6393259) B6393259
theorem B9341567 : Blo 1843623 9341567 := bstep (se 1 (by rfl) ⟨7006175, by rfl⟩ : syracuseStep 9341567 = 14012351) B14012351
theorem B2075647 : Blo 1843623 2075647 := bstep (se 1 (by rfl) ⟨1556735, by rfl⟩ : syracuseStep 2075647 = 3113471) B3113471
theorem B4148297 : Blo 1843623 4148297 := bstep (se 2 (by rfl) ⟨1555611, by rfl⟩ : syracuseStep 4148297 = 3111223) B3111223
theorem B3501281 : Blo 1843623 3501281 := bstep (se 2 (by rfl) ⟨1312980, by rfl⟩ : syracuseStep 3501281 = 2625961) B2625961
theorem B15764989 : Blo 1843623 15764989 := bstep (se 3 (by rfl) ⟨2955935, by rfl⟩ : syracuseStep 15764989 = 5911871) B5911871
theorem B10505801 : Blo 1843623 10505801 := bstep (se 2 (by rfl) ⟨3939675, by rfl⟩ : syracuseStep 10505801 = 7879351) B7879351
theorem B23629441 : Blo 1843623 23629441 := bstep (se 2 (by rfl) ⟨8861040, by rfl⟩ : syracuseStep 23629441 = 17722081) B17722081
theorem B2215679 : Blo 1843623 2215679 := bstep (se 1 (by rfl) ⟨1661759, by rfl⟩ : syracuseStep 2215679 = 3323519) B3323519
theorem B9334763 : Blo 1843623 9334763 := bstep (se 1 (by rfl) ⟨7001072, by rfl⟩ : syracuseStep 9334763 = 14002145) B14002145
theorem B4149431 : Blo 1843623 4149431 := bstep (se 1 (by rfl) ⟨3112073, by rfl⟩ : syracuseStep 4149431 = 6224147) B6224147
theorem B4149503 : Blo 1843623 4149503 := bstep (se 1 (by rfl) ⟨3112127, by rfl⟩ : syracuseStep 4149503 = 6224255) B6224255
theorem B4149791 : Blo 1843623 4149791 := bstep (se 1 (by rfl) ⟨3112343, by rfl⟩ : syracuseStep 4149791 = 6224687) B6224687
theorem B5911451 : Blo 1843623 5911451 := bstep (se 1 (by rfl) ⟨4433588, by rfl⟩ : syracuseStep 5911451 = 8867177) B8867177
theorem B4150313 : Blo 1843623 4150313 := bstep (se 2 (by rfl) ⟨1556367, by rfl⟩ : syracuseStep 4150313 = 3112735) B3112735
theorem B7001225 : Blo 1843623 7001225 := bstep (se 2 (by rfl) ⟨2625459, by rfl⟩ : syracuseStep 7001225 = 5250919) B5250919
theorem B7001255 : Blo 1843623 7001255 := bstep (se 1 (by rfl) ⟨5250941, by rfl⟩ : syracuseStep 7001255 = 10501883) B10501883
theorem B56816963 : Blo 1843623 56816963 := bstep (se 1 (by rfl) ⟨42612722, by rfl⟩ : syracuseStep 56816963 = 85225445) B85225445
theorem B4150601 : Blo 1843623 4150601 := bstep (se 2 (by rfl) ⟨1556475, by rfl⟩ : syracuseStep 4150601 = 3112951) B3112951
theorem B7001423 : Blo 1843623 7001423 := bstep (se 1 (by rfl) ⟨5251067, by rfl⟩ : syracuseStep 7001423 = 10502135) B10502135
theorem B4150655 : Blo 1843623 4150655 := bstep (se 1 (by rfl) ⟨3112991, by rfl⟩ : syracuseStep 4150655 = 6225983) B6225983
theorem B2766239 : Blo 1843623 2766239 := bstep (se 1 (by rfl) ⟨2074679, by rfl⟩ : syracuseStep 2766239 = 4149359) B4149359
theorem B6223607 : Blo 1843623 6223607 := bstep (se 1 (by rfl) ⟨4667705, by rfl⟩ : syracuseStep 6223607 = 9335411) B9335411
theorem B7878653 : Blo 1843623 7878653 := bstep (se 3 (by rfl) ⟨1477247, by rfl⟩ : syracuseStep 7878653 = 2954495) B2954495
theorem B4151591 : Blo 1843623 4151591 := bstep (se 1 (by rfl) ⟨3113693, by rfl⟩ : syracuseStep 4151591 = 6227387) B6227387
theorem B90929465 : Blo 1843623 90929465 := bstep (se 2 (by rfl) ⟨34098549, by rfl⟩ : syracuseStep 90929465 = 68197099) B68197099
theorem B4667807 : Blo 1843623 4667807 := bstep (se 1 (by rfl) ⟨3500855, by rfl⟩ : syracuseStep 4667807 = 7001711) B7001711
theorem B35453699 : Blo 1843623 35453699 := bstep (se 1 (by rfl) ⟨26590274, by rfl⟩ : syracuseStep 35453699 = 53180549) B53180549
theorem B4430695 : Blo 1843623 4430695 := bstep (se 1 (by rfl) ⟨3323021, by rfl⟩ : syracuseStep 4430695 = 6646043) B6646043
theorem B2767979 : Blo 1843623 2767979 := bstep (se 1 (by rfl) ⟨2075984, by rfl⟩ : syracuseStep 2767979 = 4151969) B4151969
theorem B2768027 : Blo 1843623 2768027 := bstep (se 1 (by rfl) ⟨2076020, by rfl⟩ : syracuseStep 2768027 = 4152041) B4152041
theorem B3112175 : Blo 1843623 3112175 := bstep (se 1 (by rfl) ⟨2334131, by rfl⟩ : syracuseStep 3112175 = 4668263) B4668263
theorem B4668911 : Blo 1843623 4668911 := bstep (se 1 (by rfl) ⟨3501683, by rfl⟩ : syracuseStep 4668911 = 7003367) B7003367
theorem B14007977 : Blo 1843623 14007977 := bstep (se 2 (by rfl) ⟨5252991, by rfl⟩ : syracuseStep 14007977 = 10505983) B10505983
theorem B9338813 : Blo 1843623 9338813 := bstep (se 3 (by rfl) ⟨1751027, by rfl⟩ : syracuseStep 9338813 = 3502055) B3502055
theorem B9469885 : Blo 1843623 9469885 := bstep (se 3 (by rfl) ⟨1775603, by rfl⟩ : syracuseStep 9469885 = 3551207) B3551207
theorem B17973847 : Blo 1843623 17973847 := bstep (se 1 (by rfl) ⟨13480385, by rfl⟩ : syracuseStep 17973847 = 26960771) B26960771
theorem B3940967 : Blo 1843623 3940967 := bstep (se 1 (by rfl) ⟨2955725, by rfl⟩ : syracuseStep 3940967 = 5911451) B5911451
theorem B6226793 : Blo 1843623 6226793 := bstep (se 2 (by rfl) ⟨2335047, by rfl⟩ : syracuseStep 6226793 = 4670095) B4670095
theorem B1844159 : Blo 1843623 1844159 := bstep (se 1 (by rfl) ⟨1383119, by rfl⟩ : syracuseStep 1844159 = 2766239) B2766239
theorem B5907593 : Blo 1843623 5907593 := bstep (se 2 (by rfl) ⟨2215347, by rfl⟩ : syracuseStep 5907593 = 4430695) B4430695
theorem B5252435 : Blo 1843623 5252435 := bstep (se 1 (by rfl) ⟨3939326, by rfl⟩ : syracuseStep 5252435 = 7878653) B7878653
theorem B6227711 : Blo 1843623 6227711 := bstep (se 1 (by rfl) ⟨4670783, by rfl⟩ : syracuseStep 6227711 = 9341567) B9341567
theorem B23635799 : Blo 1843623 23635799 := bstep (se 1 (by rfl) ⟨17726849, by rfl⟩ : syracuseStep 23635799 = 35453699) B35453699
theorem B5908477 : Blo 1843623 5908477 := bstep (se 3 (by rfl) ⟨1107839, by rfl⟩ : syracuseStep 5908477 = 2215679) B2215679
theorem B1845319 : Blo 1843623 1845319 := bstep (se 1 (by rfl) ⟨1383989, by rfl⟩ : syracuseStep 1845319 = 2767979) B2767979
theorem B1845351 : Blo 1843623 1845351 := bstep (se 1 (by rfl) ⟨1384013, by rfl⟩ : syracuseStep 1845351 = 2768027) B2768027
theorem B2074783 : Blo 1843623 2074783 := bstep (se 1 (by rfl) ⟨1556087, by rfl⟩ : syracuseStep 2074783 = 3112175) B3112175
theorem B12626513 : Blo 1843623 12626513 := bstep (se 2 (by rfl) ⟨4734942, by rfl⟩ : syracuseStep 12626513 = 9469885) B9469885
theorem B7007087 : Blo 1843623 7007087 := bstep (se 1 (by rfl) ⟨5255315, by rfl⟩ : syracuseStep 7007087 = 10510631) B10510631
theorem B7875593 : Blo 1843623 7875593 := bstep (se 2 (by rfl) ⟨2953347, by rfl⟩ : syracuseStep 7875593 = 5906695) B5906695
theorem B7007543 : Blo 1843623 7007543 := bstep (se 1 (by rfl) ⟨5255657, by rfl⟩ : syracuseStep 7007543 = 10511315) B10511315
theorem B9334439 : Blo 1843623 9334439 := bstep (se 1 (by rfl) ⟨7000829, by rfl⟩ : syracuseStep 9334439 = 14001659) B14001659
theorem B4149071 : Blo 1843623 4149071 := bstep (se 1 (by rfl) ⟨3111803, by rfl⟩ : syracuseStep 4149071 = 6223607) B6223607
theorem B2765531 : Blo 1843623 2765531 := bstep (se 1 (by rfl) ⟨2074148, by rfl⟩ : syracuseStep 2765531 = 4148297) B4148297
theorem B6223175 : Blo 1843623 6223175 := bstep (se 1 (by rfl) ⟨4667381, by rfl⟩ : syracuseStep 6223175 = 9334763) B9334763
theorem B2766287 : Blo 1843623 2766287 := bstep (se 1 (by rfl) ⟨2074715, by rfl⟩ : syracuseStep 2766287 = 4149431) B4149431
theorem B2766335 : Blo 1843623 2766335 := bstep (se 1 (by rfl) ⟨2074751, by rfl⟩ : syracuseStep 2766335 = 4149503) B4149503
theorem B4150943 : Blo 1843623 4150943 := bstep (se 1 (by rfl) ⟨3113207, by rfl⟩ : syracuseStep 4150943 = 6226415) B6226415
theorem B2766527 : Blo 1843623 2766527 := bstep (se 1 (by rfl) ⟨2074895, by rfl⟩ : syracuseStep 2766527 = 4149791) B4149791
theorem B115169015 : Blo 1843623 115169015 := bstep (se 1 (by rfl) ⟨86376761, by rfl⟩ : syracuseStep 115169015 = 172753523) B172753523
theorem B2766875 : Blo 1843623 2766875 := bstep (se 1 (by rfl) ⟨2075156, by rfl⟩ : syracuseStep 2766875 = 4150313) B4150313
theorem B4667483 : Blo 1843623 4667483 := bstep (se 1 (by rfl) ⟨3500612, by rfl⟩ : syracuseStep 4667483 = 7001225) B7001225
theorem B4667503 : Blo 1843623 4667503 := bstep (se 1 (by rfl) ⟨3500627, by rfl⟩ : syracuseStep 4667503 = 7001255) B7001255
theorem B37877975 : Blo 1843623 37877975 := bstep (se 1 (by rfl) ⟨28408481, by rfl⟩ : syracuseStep 37877975 = 56816963) B56816963
theorem B2767067 : Blo 1843623 2767067 := bstep (se 1 (by rfl) ⟨2075300, by rfl⟩ : syracuseStep 2767067 = 4150601) B4150601
theorem B4667615 : Blo 1843623 4667615 := bstep (se 1 (by rfl) ⟨3500711, by rfl⟩ : syracuseStep 4667615 = 7001423) B7001423
theorem B2767103 : Blo 1843623 2767103 := bstep (se 1 (by rfl) ⟨2075327, by rfl⟩ : syracuseStep 2767103 = 4150655) B4150655
theorem B25254179 : Blo 1843623 25254179 := bstep (se 1 (by rfl) ⟨18940634, by rfl⟩ : syracuseStep 25254179 = 37881269) B37881269
theorem B2767529 : Blo 1843623 2767529 := bstep (se 2 (by rfl) ⟨1037823, by rfl⟩ : syracuseStep 2767529 = 2075647) B2075647
theorem B22731587 : Blo 1843623 22731587 := bstep (se 1 (by rfl) ⟨17048690, by rfl⟩ : syracuseStep 22731587 = 34097381) B34097381
theorem B2767727 : Blo 1843623 2767727 := bstep (se 1 (by rfl) ⟨2075795, by rfl⟩ : syracuseStep 2767727 = 4151591) B4151591
theorem B60619643 : Blo 1843623 60619643 := bstep (se 1 (by rfl) ⟨45464732, by rfl⟩ : syracuseStep 60619643 = 90929465) B90929465
theorem B3111871 : Blo 1843623 3111871 := bstep (se 1 (by rfl) ⟨2333903, by rfl⟩ : syracuseStep 3111871 = 4667807) B4667807
theorem B4152329 : Blo 1843623 4152329 := bstep (se 2 (by rfl) ⟨1557123, by rfl⟩ : syracuseStep 4152329 = 3114247) B3114247
theorem B7003169 : Blo 1843623 7003169 := bstep (se 2 (by rfl) ⟨2626188, by rfl⟩ : syracuseStep 7003169 = 5252377) B5252377
theorem B21019985 : Blo 1843623 21019985 := bstep (se 2 (by rfl) ⟨7882494, by rfl⟩ : syracuseStep 21019985 = 15764989) B15764989
theorem B2334187 : Blo 1843623 2334187 := bstep (se 1 (by rfl) ⟨1750640, by rfl⟩ : syracuseStep 2334187 = 3501281) B3501281
theorem B31505921 : Blo 1843623 31505921 := bstep (se 2 (by rfl) ⟨11814720, by rfl⟩ : syracuseStep 31505921 = 23629441) B23629441
theorem B3112607 : Blo 1843623 3112607 := bstep (se 1 (by rfl) ⟨2334455, by rfl⟩ : syracuseStep 3112607 = 4668911) B4668911
theorem B7003867 : Blo 1843623 7003867 := bstep (se 1 (by rfl) ⟨5252900, by rfl⟩ : syracuseStep 7003867 = 10505801) B10505801
theorem B9338651 : Blo 1843623 9338651 := bstep (se 1 (by rfl) ⟨7003988, by rfl⟩ : syracuseStep 9338651 = 14007977) B14007977
theorem B6225875 : Blo 1843623 6225875 := bstep (se 1 (by rfl) ⟨4669406, by rfl⟩ : syracuseStep 6225875 = 9338813) B9338813
theorem B1843687 : Blo 1843623 1843687 := bstep (se 1 (by rfl) ⟨1382765, by rfl⟩ : syracuseStep 1843687 = 2765531) B2765531
theorem B1844191 : Blo 1843623 1844191 := bstep (se 1 (by rfl) ⟨1383143, by rfl⟩ : syracuseStep 1844191 = 2766287) B2766287
theorem B1844223 : Blo 1843623 1844223 := bstep (se 1 (by rfl) ⟨1383167, by rfl⟩ : syracuseStep 1844223 = 2766335) B2766335
theorem B1844351 : Blo 1843623 1844351 := bstep (se 1 (by rfl) ⟨1383263, by rfl⟩ : syracuseStep 1844351 = 2766527) B2766527
theorem B1844583 : Blo 1843623 1844583 := bstep (se 1 (by rfl) ⟨1383437, by rfl⟩ : syracuseStep 1844583 = 2766875) B2766875
theorem B1844711 : Blo 1843623 1844711 := bstep (se 1 (by rfl) ⟨1383533, by rfl⟩ : syracuseStep 1844711 = 2767067) B2767067
theorem B1844735 : Blo 1843623 1844735 := bstep (se 1 (by rfl) ⟨1383551, by rfl⟩ : syracuseStep 1844735 = 2767103) B2767103
theorem B16836119 : Blo 1843623 16836119 := bstep (se 1 (by rfl) ⟨12627089, by rfl⟩ : syracuseStep 16836119 = 25254179) B25254179
theorem B1845019 : Blo 1843623 1845019 := bstep (se 1 (by rfl) ⟨1383764, by rfl⟩ : syracuseStep 1845019 = 2767529) B2767529
theorem B1845151 : Blo 1843623 1845151 := bstep (se 1 (by rfl) ⟨1383863, by rfl⟩ : syracuseStep 1845151 = 2767727) B2767727
theorem B4671391 : Blo 1843623 4671391 := bstep (se 1 (by rfl) ⟨3503543, by rfl⟩ : syracuseStep 4671391 = 7007087) B7007087
theorem B40413095 : Blo 1843623 40413095 := bstep (se 1 (by rfl) ⟨30309821, by rfl⟩ : syracuseStep 40413095 = 60619643) B60619643
theorem B4671695 : Blo 1843623 4671695 := bstep (se 1 (by rfl) ⟨3503771, by rfl⟩ : syracuseStep 4671695 = 7007543) B7007543
theorem B2075071 : Blo 1843623 2075071 := bstep (se 1 (by rfl) ⟨1556303, by rfl⟩ : syracuseStep 2075071 = 3112607) B3112607
theorem B23965129 : Blo 1843623 23965129 := bstep (se 2 (by rfl) ⟨8986923, by rfl⟩ : syracuseStep 23965129 = 17973847) B17973847
theorem B4148783 : Blo 1843623 4148783 := bstep (se 1 (by rfl) ⟨3111587, by rfl⟩ : syracuseStep 4148783 = 6223175) B6223175
theorem B3501623 : Blo 1843623 3501623 := bstep (se 1 (by rfl) ⟨2626217, by rfl⟩ : syracuseStep 3501623 = 5252435) B5252435
theorem B76779343 : Blo 1843623 76779343 := bstep (se 1 (by rfl) ⟨57584507, by rfl⟩ : syracuseStep 76779343 = 115169015) B115169015
theorem B15757199 : Blo 1843623 15757199 := bstep (se 1 (by rfl) ⟨11817899, by rfl⟩ : syracuseStep 15757199 = 23635799) B23635799
theorem B4149161 : Blo 1843623 4149161 := bstep (se 2 (by rfl) ⟨1555935, by rfl⟩ : syracuseStep 4149161 = 3111871) B3111871
theorem B25251983 : Blo 1843623 25251983 := bstep (se 1 (by rfl) ⟨18938987, by rfl⟩ : syracuseStep 25251983 = 37877975) B37877975
theorem B8417675 : Blo 1843623 8417675 := bstep (se 1 (by rfl) ⟨6313256, by rfl⟩ : syracuseStep 8417675 = 12626513) B12626513
theorem B14013323 : Blo 1843623 14013323 := bstep (se 1 (by rfl) ⟨10509992, by rfl⟩ : syracuseStep 14013323 = 21019985) B21019985
theorem B6222959 : Blo 1843623 6222959 := bstep (se 1 (by rfl) ⟨4667219, by rfl⟩ : syracuseStep 6222959 = 9334439) B9334439
theorem B2766047 : Blo 1843623 2766047 := bstep (se 1 (by rfl) ⟨2074535, by rfl⟩ : syracuseStep 2766047 = 4149071) B4149071
theorem B4150583 : Blo 1843623 4150583 := bstep (se 1 (by rfl) ⟨3112937, by rfl⟩ : syracuseStep 4150583 = 6225875) B6225875
theorem B7877969 : Blo 1843623 7877969 := bstep (se 2 (by rfl) ⟨2954238, by rfl⟩ : syracuseStep 7877969 = 5908477) B5908477
theorem B6223337 : Blo 1843623 6223337 := bstep (se 2 (by rfl) ⟨2333751, by rfl⟩ : syracuseStep 6223337 = 4667503) B4667503
theorem B2766377 : Blo 1843623 2766377 := bstep (se 2 (by rfl) ⟨1037391, by rfl⟩ : syracuseStep 2766377 = 2074783) B2074783
theorem B2627311 : Blo 1843623 2627311 := bstep (se 1 (by rfl) ⟨1970483, by rfl⟩ : syracuseStep 2627311 = 3940967) B3940967
theorem B4151195 : Blo 1843623 4151195 := bstep (se 1 (by rfl) ⟨3113396, by rfl⟩ : syracuseStep 4151195 = 6226793) B6226793
theorem B3938395 : Blo 1843623 3938395 := bstep (se 1 (by rfl) ⟨2953796, by rfl⟩ : syracuseStep 3938395 = 5907593) B5907593
theorem B2767295 : Blo 1843623 2767295 := bstep (se 1 (by rfl) ⟨2075471, by rfl⟩ : syracuseStep 2767295 = 4150943) B4150943
theorem B4151807 : Blo 1843623 4151807 := bstep (se 1 (by rfl) ⟨3113855, by rfl⟩ : syracuseStep 4151807 = 6227711) B6227711
theorem B3111655 : Blo 1843623 3111655 := bstep (se 1 (by rfl) ⟨2333741, by rfl⟩ : syracuseStep 3111655 = 4667483) B4667483
theorem B3111743 : Blo 1843623 3111743 := bstep (se 1 (by rfl) ⟨2333807, by rfl⟩ : syracuseStep 3111743 = 4667615) B4667615
theorem B15154391 : Blo 1843623 15154391 := bstep (se 1 (by rfl) ⟨11365793, by rfl⟩ : syracuseStep 15154391 = 22731587) B22731587
theorem B3112249 : Blo 1843623 3112249 := bstep (se 2 (by rfl) ⟨1167093, by rfl⟩ : syracuseStep 3112249 = 2334187) B2334187
theorem B5250395 : Blo 1843623 5250395 := bstep (se 1 (by rfl) ⟨3937796, by rfl⟩ : syracuseStep 5250395 = 7875593) B7875593
theorem B2768219 : Blo 1843623 2768219 := bstep (se 1 (by rfl) ⟨2076164, by rfl⟩ : syracuseStep 2768219 = 4152329) B4152329
theorem B4668779 : Blo 1843623 4668779 := bstep (se 1 (by rfl) ⟨3501584, by rfl⟩ : syracuseStep 4668779 = 7003169) B7003169
theorem B9338489 : Blo 1843623 9338489 := bstep (se 2 (by rfl) ⟨3501933, by rfl⟩ : syracuseStep 9338489 = 7003867) B7003867
theorem B21003947 : Blo 1843623 21003947 := bstep (se 1 (by rfl) ⟨15752960, by rfl⟩ : syracuseStep 21003947 = 31505921) B31505921
theorem B6225767 : Blo 1843623 6225767 := bstep (se 1 (by rfl) ⟨4669325, by rfl⟩ : syracuseStep 6225767 = 9338651) B9338651
theorem B16834655 : Blo 1843623 16834655 := bstep (se 1 (by rfl) ⟨12625991, by rfl⟩ : syracuseStep 16834655 = 25251983) B25251983
theorem B5251193 : Blo 1843623 5251193 := bstep (se 2 (by rfl) ⟨1969197, by rfl⟩ : syracuseStep 5251193 = 3938395) B3938395
theorem B5611783 : Blo 1843623 5611783 := bstep (se 1 (by rfl) ⟨4208837, by rfl⟩ : syracuseStep 5611783 = 8417675) B8417675
theorem B1844031 : Blo 1843623 1844031 := bstep (se 1 (by rfl) ⟨1383023, by rfl⟩ : syracuseStep 1844031 = 2766047) B2766047
theorem B5251979 : Blo 1843623 5251979 := bstep (se 1 (by rfl) ⟨3938984, by rfl⟩ : syracuseStep 5251979 = 7877969) B7877969
theorem B11224079 : Blo 1843623 11224079 := bstep (se 1 (by rfl) ⟨8418059, by rfl⟩ : syracuseStep 11224079 = 16836119) B16836119
theorem B1844251 : Blo 1843623 1844251 := bstep (se 1 (by rfl) ⟨1383188, by rfl⟩ : syracuseStep 1844251 = 2766377) B2766377
theorem B3114463 : Blo 1843623 3114463 := bstep (se 1 (by rfl) ⟨2335847, by rfl⟩ : syracuseStep 3114463 = 4671695) B4671695
theorem B1844863 : Blo 1843623 1844863 := bstep (se 1 (by rfl) ⟨1383647, by rfl⟩ : syracuseStep 1844863 = 2767295) B2767295
theorem B2074495 : Blo 1843623 2074495 := bstep (se 1 (by rfl) ⟨1555871, by rfl⟩ : syracuseStep 2074495 = 3111743) B3111743
theorem B10102927 : Blo 1843623 10102927 := bstep (se 1 (by rfl) ⟨7577195, by rfl⟩ : syracuseStep 10102927 = 15154391) B15154391
theorem B3500263 : Blo 1843623 3500263 := bstep (se 1 (by rfl) ⟨2625197, by rfl⟩ : syracuseStep 3500263 = 5250395) B5250395
theorem B1845479 : Blo 1843623 1845479 := bstep (se 1 (by rfl) ⟨1384109, by rfl⟩ : syracuseStep 1845479 = 2768219) B2768219
theorem B127814021 : Blo 1843623 127814021 := bstep (se 4 (by rfl) ⟨11982564, by rfl⟩ : syracuseStep 127814021 = 23965129) B23965129
theorem B14002631 : Blo 1843623 14002631 := bstep (se 1 (by rfl) ⟨10501973, by rfl⟩ : syracuseStep 14002631 = 21003947) B21003947
theorem B6228521 : Blo 1843623 6228521 := bstep (se 2 (by rfl) ⟨2335695, by rfl⟩ : syracuseStep 6228521 = 4671391) B4671391
theorem B10504799 : Blo 1843623 10504799 := bstep (se 1 (by rfl) ⟨7878599, by rfl⟩ : syracuseStep 10504799 = 15757199) B15757199
theorem B9342215 : Blo 1843623 9342215 := bstep (se 1 (by rfl) ⟨7006661, by rfl⟩ : syracuseStep 9342215 = 14013323) B14013323
theorem B4148639 : Blo 1843623 4148639 := bstep (se 1 (by rfl) ⟨3111479, by rfl⟩ : syracuseStep 4148639 = 6222959) B6222959
theorem B4148873 : Blo 1843623 4148873 := bstep (se 2 (by rfl) ⟨1555827, by rfl⟩ : syracuseStep 4148873 = 3111655) B3111655
theorem B4148891 : Blo 1843623 4148891 := bstep (se 1 (by rfl) ⟨3111668, by rfl⟩ : syracuseStep 4148891 = 6223337) B6223337
theorem B4149665 : Blo 1843623 4149665 := bstep (se 2 (by rfl) ⟨1556124, by rfl⟩ : syracuseStep 4149665 = 3112249) B3112249
theorem B3503081 : Blo 1843623 3503081 := bstep (se 2 (by rfl) ⟨1313655, by rfl⟩ : syracuseStep 3503081 = 2627311) B2627311
theorem B2765855 : Blo 1843623 2765855 := bstep (se 1 (by rfl) ⟨2074391, by rfl⟩ : syracuseStep 2765855 = 4148783) B4148783
theorem B102372457 : Blo 1843623 102372457 := bstep (se 2 (by rfl) ⟨38389671, by rfl⟩ : syracuseStep 102372457 = 76779343) B76779343
theorem B4150511 : Blo 1843623 4150511 := bstep (se 1 (by rfl) ⟨3112883, by rfl⟩ : syracuseStep 4150511 = 6225767) B6225767
theorem B2766107 : Blo 1843623 2766107 := bstep (se 1 (by rfl) ⟨2074580, by rfl⟩ : syracuseStep 2766107 = 4149161) B4149161
theorem B2766761 : Blo 1843623 2766761 := bstep (se 2 (by rfl) ⟨1037535, by rfl⟩ : syracuseStep 2766761 = 2075071) B2075071
theorem B2767055 : Blo 1843623 2767055 := bstep (se 1 (by rfl) ⟨2075291, by rfl⟩ : syracuseStep 2767055 = 4150583) B4150583
theorem B2767463 : Blo 1843623 2767463 := bstep (se 1 (by rfl) ⟨2075597, by rfl⟩ : syracuseStep 2767463 = 4151195) B4151195
theorem B26942063 : Blo 1843623 26942063 := bstep (se 1 (by rfl) ⟨20206547, by rfl⟩ : syracuseStep 26942063 = 40413095) B40413095
theorem B2767871 : Blo 1843623 2767871 := bstep (se 1 (by rfl) ⟨2075903, by rfl⟩ : syracuseStep 2767871 = 4151807) B4151807
theorem B3112519 : Blo 1843623 3112519 := bstep (se 1 (by rfl) ⟨2334389, by rfl⟩ : syracuseStep 3112519 = 4668779) B4668779
theorem B2334415 : Blo 1843623 2334415 := bstep (se 1 (by rfl) ⟨1750811, by rfl⟩ : syracuseStep 2334415 = 3501623) B3501623
theorem B6225659 : Blo 1843623 6225659 := bstep (se 1 (by rfl) ⟨4669244, by rfl⟩ : syracuseStep 6225659 = 9338489) B9338489
theorem B44892413 : Blo 1843623 44892413 := bstep (se 3 (by rfl) ⟨8417327, by rfl⟩ : syracuseStep 44892413 = 16834655) B16834655
theorem B2335387 : Blo 1843623 2335387 := bstep (se 1 (by rfl) ⟨1751540, by rfl⟩ : syracuseStep 2335387 = 3503081) B3503081
theorem B1843903 : Blo 1843623 1843903 := bstep (se 1 (by rfl) ⟨1382927, by rfl⟩ : syracuseStep 1843903 = 2765855) B2765855
theorem B1844071 : Blo 1843623 1844071 := bstep (se 1 (by rfl) ⟨1383053, by rfl⟩ : syracuseStep 1844071 = 2766107) B2766107
theorem B1844507 : Blo 1843623 1844507 := bstep (se 1 (by rfl) ⟨1383380, by rfl⟩ : syracuseStep 1844507 = 2766761) B2766761
theorem B1844703 : Blo 1843623 1844703 := bstep (se 1 (by rfl) ⟨1383527, by rfl⟩ : syracuseStep 1844703 = 2767055) B2767055
theorem B136496609 : Blo 1843623 136496609 := bstep (se 2 (by rfl) ⟨51186228, by rfl⟩ : syracuseStep 136496609 = 102372457) B102372457
theorem B1844975 : Blo 1843623 1844975 := bstep (se 1 (by rfl) ⟨1383731, by rfl⟩ : syracuseStep 1844975 = 2767463) B2767463
theorem B1845247 : Blo 1843623 1845247 := bstep (se 1 (by rfl) ⟨1383935, by rfl⟩ : syracuseStep 1845247 = 2767871) B2767871
theorem B6228143 : Blo 1843623 6228143 := bstep (se 1 (by rfl) ⟨4671107, by rfl⟩ : syracuseStep 6228143 = 9342215) B9342215
theorem B3500795 : Blo 1843623 3500795 := bstep (se 1 (by rfl) ⟨2625596, by rfl⟩ : syracuseStep 3500795 = 5251193) B5251193
theorem B13470569 : Blo 1843623 13470569 := bstep (se 2 (by rfl) ⟨5051463, by rfl⟩ : syracuseStep 13470569 = 10102927) B10102927
theorem B7482377 : Blo 1843623 7482377 := bstep (se 2 (by rfl) ⟨2805891, by rfl⟩ : syracuseStep 7482377 = 5611783) B5611783
theorem B3501319 : Blo 1843623 3501319 := bstep (se 1 (by rfl) ⟨2625989, by rfl⟩ : syracuseStep 3501319 = 5251979) B5251979
theorem B7482719 : Blo 1843623 7482719 := bstep (se 1 (by rfl) ⟨5612039, by rfl⟩ : syracuseStep 7482719 = 11224079) B11224079
theorem B85209347 : Blo 1843623 85209347 := bstep (se 1 (by rfl) ⟨63907010, by rfl⟩ : syracuseStep 85209347 = 127814021) B127814021
theorem B9335087 : Blo 1843623 9335087 := bstep (se 1 (by rfl) ⟨7001315, by rfl⟩ : syracuseStep 9335087 = 14002631) B14002631
theorem B4150025 : Blo 1843623 4150025 := bstep (se 2 (by rfl) ⟨1556259, by rfl⟩ : syracuseStep 4150025 = 3112519) B3112519
theorem B2765759 : Blo 1843623 2765759 := bstep (se 1 (by rfl) ⟨2074319, by rfl⟩ : syracuseStep 2765759 = 4148639) B4148639
theorem B2765915 : Blo 1843623 2765915 := bstep (se 1 (by rfl) ⟨2074436, by rfl⟩ : syracuseStep 2765915 = 4148873) B4148873
theorem B2765927 : Blo 1843623 2765927 := bstep (se 1 (by rfl) ⟨2074445, by rfl⟩ : syracuseStep 2765927 = 4148891) B4148891
theorem B4150439 : Blo 1843623 4150439 := bstep (se 1 (by rfl) ⟨3112829, by rfl⟩ : syracuseStep 4150439 = 6225659) B6225659
theorem B2765993 : Blo 1843623 2765993 := bstep (se 2 (by rfl) ⟨1037247, by rfl⟩ : syracuseStep 2765993 = 2074495) B2074495
theorem B2766443 : Blo 1843623 2766443 := bstep (se 1 (by rfl) ⟨2074832, by rfl⟩ : syracuseStep 2766443 = 4149665) B4149665
theorem B4667017 : Blo 1843623 4667017 := bstep (se 2 (by rfl) ⟨1750131, by rfl⟩ : syracuseStep 4667017 = 3500263) B3500263
theorem B2767007 : Blo 1843623 2767007 := bstep (se 1 (by rfl) ⟨2075255, by rfl⟩ : syracuseStep 2767007 = 4150511) B4150511
theorem B287382005 : Blo 1843623 287382005 := bstep (se 5 (by rfl) ⟨13471031, by rfl⟩ : syracuseStep 287382005 = 26942063) B26942063
theorem B4152347 : Blo 1843623 4152347 := bstep (se 1 (by rfl) ⟨3114260, by rfl⟩ : syracuseStep 4152347 = 6228521) B6228521
theorem B7003199 : Blo 1843623 7003199 := bstep (se 1 (by rfl) ⟨5252399, by rfl⟩ : syracuseStep 7003199 = 10504799) B10504799
theorem B4152617 : Blo 1843623 4152617 := bstep (se 2 (by rfl) ⟨1557231, by rfl⟩ : syracuseStep 4152617 = 3114463) B3114463
theorem B3112553 : Blo 1843623 3112553 := bstep (se 2 (by rfl) ⟨1167207, by rfl⟩ : syracuseStep 3112553 = 2334415) B2334415
theorem B1843839 : Blo 1843623 1843839 := bstep (se 1 (by rfl) ⟨1382879, by rfl⟩ : syracuseStep 1843839 = 2765759) B2765759
theorem B1843943 : Blo 1843623 1843943 := bstep (se 1 (by rfl) ⟨1382957, by rfl⟩ : syracuseStep 1843943 = 2765915) B2765915
theorem B1843951 : Blo 1843623 1843951 := bstep (se 1 (by rfl) ⟨1382963, by rfl⟩ : syracuseStep 1843951 = 2765927) B2765927
theorem B1843995 : Blo 1843623 1843995 := bstep (se 1 (by rfl) ⟨1382996, by rfl⟩ : syracuseStep 1843995 = 2765993) B2765993
theorem B3113849 : Blo 1843623 3113849 := bstep (se 2 (by rfl) ⟨1167693, by rfl⟩ : syracuseStep 3113849 = 2335387) B2335387
theorem B90997739 : Blo 1843623 90997739 := bstep (se 1 (by rfl) ⟨68248304, by rfl⟩ : syracuseStep 90997739 = 136496609) B136496609
theorem B1844295 : Blo 1843623 1844295 := bstep (se 1 (by rfl) ⟨1383221, by rfl⟩ : syracuseStep 1844295 = 2766443) B2766443
theorem B1844671 : Blo 1843623 1844671 := bstep (se 1 (by rfl) ⟨1383503, by rfl⟩ : syracuseStep 1844671 = 2767007) B2767007
theorem B191588003 : Blo 1843623 191588003 := bstep (se 1 (by rfl) ⟨143691002, by rfl⟩ : syracuseStep 191588003 = 287382005) B287382005
theorem B8980379 : Blo 1843623 8980379 := bstep (se 1 (by rfl) ⟨6735284, by rfl⟩ : syracuseStep 8980379 = 13470569) B13470569
theorem B2075035 : Blo 1843623 2075035 := bstep (se 1 (by rfl) ⟨1556276, by rfl⟩ : syracuseStep 2075035 = 3112553) B3112553
theorem B29928275 : Blo 1843623 29928275 := bstep (se 1 (by rfl) ⟨22446206, by rfl⟩ : syracuseStep 29928275 = 44892413) B44892413
theorem B56806231 : Blo 1843623 56806231 := bstep (se 1 (by rfl) ⟨42604673, by rfl⟩ : syracuseStep 56806231 = 85209347) B85209347
theorem B6222689 : Blo 1843623 6222689 := bstep (se 2 (by rfl) ⟨2333508, by rfl⟩ : syracuseStep 6222689 = 4667017) B4667017
theorem B6223391 : Blo 1843623 6223391 := bstep (se 1 (by rfl) ⟨4667543, by rfl⟩ : syracuseStep 6223391 = 9335087) B9335087
theorem B2766683 : Blo 1843623 2766683 := bstep (se 1 (by rfl) ⟨2075012, by rfl⟩ : syracuseStep 2766683 = 4150025) B4150025
theorem B2766959 : Blo 1843623 2766959 := bstep (se 1 (by rfl) ⟨2075219, by rfl⟩ : syracuseStep 2766959 = 4150439) B4150439
theorem B4152095 : Blo 1843623 4152095 := bstep (se 1 (by rfl) ⟨3114071, by rfl⟩ : syracuseStep 4152095 = 6228143) B6228143
theorem B4668425 : Blo 1843623 4668425 := bstep (se 2 (by rfl) ⟨1750659, by rfl⟩ : syracuseStep 4668425 = 3501319) B3501319
theorem B2333863 : Blo 1843623 2333863 := bstep (se 1 (by rfl) ⟨1750397, by rfl⟩ : syracuseStep 2333863 = 3500795) B3500795
theorem B4988251 : Blo 1843623 4988251 := bstep (se 1 (by rfl) ⟨3741188, by rfl⟩ : syracuseStep 4988251 = 7482377) B7482377
theorem B2768231 : Blo 1843623 2768231 := bstep (se 1 (by rfl) ⟨2076173, by rfl⟩ : syracuseStep 2768231 = 4152347) B4152347
theorem B4668799 : Blo 1843623 4668799 := bstep (se 1 (by rfl) ⟨3501599, by rfl⟩ : syracuseStep 4668799 = 7003199) B7003199
theorem B2768411 : Blo 1843623 2768411 := bstep (se 1 (by rfl) ⟨2076308, by rfl⟩ : syracuseStep 2768411 = 4152617) B4152617
theorem B4988479 : Blo 1843623 4988479 := bstep (se 1 (by rfl) ⟨3741359, by rfl⟩ : syracuseStep 4988479 = 7482719) B7482719
theorem B1844455 : Blo 1843623 1844455 := bstep (se 1 (by rfl) ⟨1383341, by rfl⟩ : syracuseStep 1844455 = 2766683) B2766683
theorem B1844639 : Blo 1843623 1844639 := bstep (se 1 (by rfl) ⟨1383479, by rfl⟩ : syracuseStep 1844639 = 2766959) B2766959
theorem B1845487 : Blo 1843623 1845487 := bstep (se 1 (by rfl) ⟨1384115, by rfl⟩ : syracuseStep 1845487 = 2768231) B2768231
theorem B1845607 : Blo 1843623 1845607 := bstep (se 1 (by rfl) ⟨1384205, by rfl⟩ : syracuseStep 1845607 = 2768411) B2768411
theorem B4148459 : Blo 1843623 4148459 := bstep (se 1 (by rfl) ⟨3111344, by rfl⟩ : syracuseStep 4148459 = 6222689) B6222689
theorem B2075899 : Blo 1843623 2075899 := bstep (se 1 (by rfl) ⟨1556924, by rfl⟩ : syracuseStep 2075899 = 3113849) B3113849
theorem B60665159 : Blo 1843623 60665159 := bstep (se 1 (by rfl) ⟨45498869, by rfl⟩ : syracuseStep 60665159 = 90997739) B90997739
theorem B4148927 : Blo 1843623 4148927 := bstep (se 1 (by rfl) ⟨3111695, by rfl⟩ : syracuseStep 4148927 = 6223391) B6223391
theorem B127725335 : Blo 1843623 127725335 := bstep (se 1 (by rfl) ⟨95794001, by rfl⟩ : syracuseStep 127725335 = 191588003) B191588003
theorem B19952183 : Blo 1843623 19952183 := bstep (se 1 (by rfl) ⟨14964137, by rfl⟩ : syracuseStep 19952183 = 29928275) B29928275
theorem B2766713 : Blo 1843623 2766713 := bstep (se 2 (by rfl) ⟨1037517, by rfl⟩ : syracuseStep 2766713 = 2075035) B2075035
theorem B75741641 : Blo 1843623 75741641 := bstep (se 2 (by rfl) ⟨28403115, by rfl⟩ : syracuseStep 75741641 = 56806231) B56806231
theorem B5986919 : Blo 1843623 5986919 := bstep (se 1 (by rfl) ⟨4490189, by rfl⟩ : syracuseStep 5986919 = 8980379) B8980379
theorem B3111817 : Blo 1843623 3111817 := bstep (se 2 (by rfl) ⟨1166931, by rfl⟩ : syracuseStep 3111817 = 2333863) B2333863
theorem B6651001 : Blo 1843623 6651001 := bstep (se 2 (by rfl) ⟨2494125, by rfl⟩ : syracuseStep 6651001 = 4988251) B4988251
theorem B6225065 : Blo 1843623 6225065 := bstep (se 2 (by rfl) ⟨2334399, by rfl⟩ : syracuseStep 6225065 = 4668799) B4668799
theorem B2768063 : Blo 1843623 2768063 := bstep (se 1 (by rfl) ⟨2076047, by rfl⟩ : syracuseStep 2768063 = 4152095) B4152095
theorem B3112283 : Blo 1843623 3112283 := bstep (se 1 (by rfl) ⟨2334212, by rfl⟩ : syracuseStep 3112283 = 4668425) B4668425
theorem B6651305 : Blo 1843623 6651305 := bstep (se 2 (by rfl) ⟨2494239, by rfl⟩ : syracuseStep 6651305 = 4988479) B4988479
theorem B1844475 : Blo 1843623 1844475 := bstep (se 1 (by rfl) ⟨1383356, by rfl⟩ : syracuseStep 1844475 = 2766713) B2766713
theorem B3991279 : Blo 1843623 3991279 := bstep (se 1 (by rfl) ⟨2993459, by rfl⟩ : syracuseStep 3991279 = 5986919) B5986919
theorem B1845375 : Blo 1843623 1845375 := bstep (se 1 (by rfl) ⟨1384031, by rfl⟩ : syracuseStep 1845375 = 2768063) B2768063
theorem B2074855 : Blo 1843623 2074855 := bstep (se 1 (by rfl) ⟨1556141, by rfl⟩ : syracuseStep 2074855 = 3112283) B3112283
theorem B4434203 : Blo 1843623 4434203 := bstep (se 1 (by rfl) ⟨3325652, by rfl⟩ : syracuseStep 4434203 = 6651305) B6651305
theorem B85150223 : Blo 1843623 85150223 := bstep (se 1 (by rfl) ⟨63862667, by rfl⟩ : syracuseStep 85150223 = 127725335) B127725335
theorem B4149089 : Blo 1843623 4149089 := bstep (se 2 (by rfl) ⟨1555908, by rfl⟩ : syracuseStep 4149089 = 3111817) B3111817
theorem B8868001 : Blo 1843623 8868001 := bstep (se 2 (by rfl) ⟨3325500, by rfl⟩ : syracuseStep 8868001 = 6651001) B6651001
theorem B4150043 : Blo 1843623 4150043 := bstep (se 1 (by rfl) ⟨3112532, by rfl⟩ : syracuseStep 4150043 = 6225065) B6225065
theorem B2765639 : Blo 1843623 2765639 := bstep (se 1 (by rfl) ⟨2074229, by rfl⟩ : syracuseStep 2765639 = 4148459) B4148459
theorem B2765951 : Blo 1843623 2765951 := bstep (se 1 (by rfl) ⟨2074463, by rfl⟩ : syracuseStep 2765951 = 4148927) B4148927
theorem B13301455 : Blo 1843623 13301455 := bstep (se 1 (by rfl) ⟨9976091, by rfl⟩ : syracuseStep 13301455 = 19952183) B19952183
theorem B161773757 : Blo 1843623 161773757 := bstep (se 3 (by rfl) ⟨30332579, by rfl⟩ : syracuseStep 161773757 = 60665159) B60665159
theorem B50494427 : Blo 1843623 50494427 := bstep (se 1 (by rfl) ⟨37870820, by rfl⟩ : syracuseStep 50494427 = 75741641) B75741641
theorem B2767865 : Blo 1843623 2767865 := bstep (se 2 (by rfl) ⟨1037949, by rfl⟩ : syracuseStep 2767865 = 2075899) B2075899
theorem B1843759 : Blo 1843623 1843759 := bstep (se 1 (by rfl) ⟨1382819, by rfl⟩ : syracuseStep 1843759 = 2765639) B2765639
theorem B1843967 : Blo 1843623 1843967 := bstep (se 1 (by rfl) ⟨1382975, by rfl⟩ : syracuseStep 1843967 = 2765951) B2765951
theorem B107849171 : Blo 1843623 107849171 := bstep (se 1 (by rfl) ⟨80886878, by rfl⟩ : syracuseStep 107849171 = 161773757) B161773757
theorem B33662951 : Blo 1843623 33662951 := bstep (se 1 (by rfl) ⟨25247213, by rfl⟩ : syracuseStep 33662951 = 50494427) B50494427
theorem B1845243 : Blo 1843623 1845243 := bstep (se 1 (by rfl) ⟨1383932, by rfl⟩ : syracuseStep 1845243 = 2767865) B2767865
theorem B11824001 : Blo 1843623 11824001 := bstep (se 2 (by rfl) ⟨4434000, by rfl⟩ : syracuseStep 11824001 = 8868001) B8868001
theorem B11824541 : Blo 1843623 11824541 := bstep (se 3 (by rfl) ⟨2217101, by rfl⟩ : syracuseStep 11824541 = 4434203) B4434203
theorem B56766815 : Blo 1843623 56766815 := bstep (se 1 (by rfl) ⟨42575111, by rfl⟩ : syracuseStep 56766815 = 85150223) B85150223
theorem B5321705 : Blo 1843623 5321705 := bstep (se 2 (by rfl) ⟨1995639, by rfl⟩ : syracuseStep 5321705 = 3991279) B3991279
theorem B2766059 : Blo 1843623 2766059 := bstep (se 1 (by rfl) ⟨2074544, by rfl⟩ : syracuseStep 2766059 = 4149089) B4149089
theorem B2766473 : Blo 1843623 2766473 := bstep (se 2 (by rfl) ⟨1037427, by rfl⟩ : syracuseStep 2766473 = 2074855) B2074855
theorem B2766695 : Blo 1843623 2766695 := bstep (se 1 (by rfl) ⟨2075021, by rfl⟩ : syracuseStep 2766695 = 4150043) B4150043
theorem B17735273 : Blo 1843623 17735273 := bstep (se 2 (by rfl) ⟨6650727, by rfl⟩ : syracuseStep 17735273 = 13301455) B13301455
theorem B1844039 : Blo 1843623 1844039 := bstep (se 1 (by rfl) ⟨1383029, by rfl⟩ : syracuseStep 1844039 = 2766059) B2766059
theorem B1844315 : Blo 1843623 1844315 := bstep (se 1 (by rfl) ⟨1383236, by rfl⟩ : syracuseStep 1844315 = 2766473) B2766473
theorem B1844463 : Blo 1843623 1844463 := bstep (se 1 (by rfl) ⟨1383347, by rfl⟩ : syracuseStep 1844463 = 2766695) B2766695
theorem B7882667 : Blo 1843623 7882667 := bstep (se 1 (by rfl) ⟨5912000, by rfl⟩ : syracuseStep 7882667 = 11824001) B11824001
theorem B7883027 : Blo 1843623 7883027 := bstep (se 1 (by rfl) ⟨5912270, by rfl⟩ : syracuseStep 7883027 = 11824541) B11824541
theorem B11823515 : Blo 1843623 11823515 := bstep (se 1 (by rfl) ⟨8867636, by rfl⟩ : syracuseStep 11823515 = 17735273) B17735273
theorem B14191213 : Blo 1843623 14191213 := bstep (se 3 (by rfl) ⟨2660852, by rfl⟩ : syracuseStep 14191213 = 5321705) B5321705
theorem B22441967 : Blo 1843623 22441967 := bstep (se 1 (by rfl) ⟨16831475, by rfl⟩ : syracuseStep 22441967 = 33662951) B33662951
theorem B37844543 : Blo 1843623 37844543 := bstep (se 1 (by rfl) ⟨28383407, by rfl⟩ : syracuseStep 37844543 = 56766815) B56766815
theorem B71899447 : Blo 1843623 71899447 := bstep (se 1 (by rfl) ⟨53924585, by rfl⟩ : syracuseStep 71899447 = 107849171) B107849171
theorem B100918781 : Blo 1843623 100918781 := bstep (se 3 (by rfl) ⟨18922271, by rfl⟩ : syracuseStep 100918781 = 37844543) B37844543
theorem B7882343 : Blo 1843623 7882343 := bstep (se 1 (by rfl) ⟨5911757, by rfl⟩ : syracuseStep 7882343 = 11823515) B11823515
theorem B14961311 : Blo 1843623 14961311 := bstep (se 1 (by rfl) ⟨11220983, by rfl⟩ : syracuseStep 14961311 = 22441967) B22441967
theorem B95865929 : Blo 1843623 95865929 := bstep (se 2 (by rfl) ⟨35949723, by rfl⟩ : syracuseStep 95865929 = 71899447) B71899447
theorem B5255111 : Blo 1843623 5255111 := bstep (se 1 (by rfl) ⟨3941333, by rfl⟩ : syracuseStep 5255111 = 7882667) B7882667
theorem B5255351 : Blo 1843623 5255351 := bstep (se 1 (by rfl) ⟨3941513, by rfl⟩ : syracuseStep 5255351 = 7883027) B7883027
theorem B18921617 : Blo 1843623 18921617 := bstep (se 2 (by rfl) ⟨7095606, by rfl⟩ : syracuseStep 18921617 = 14191213) B14191213
theorem B5254895 : Blo 1843623 5254895 := bstep (se 1 (by rfl) ⟨3941171, by rfl⟩ : syracuseStep 5254895 = 7882343) B7882343
theorem B9974207 : Blo 1843623 9974207 := bstep (se 1 (by rfl) ⟨7480655, by rfl⟩ : syracuseStep 9974207 = 14961311) B14961311
theorem B63910619 : Blo 1843623 63910619 := bstep (se 1 (by rfl) ⟨47932964, by rfl⟩ : syracuseStep 63910619 = 95865929) B95865929
theorem B3503407 : Blo 1843623 3503407 := bstep (se 1 (by rfl) ⟨2627555, by rfl⟩ : syracuseStep 3503407 = 5255111) B5255111
theorem B3503567 : Blo 1843623 3503567 := bstep (se 1 (by rfl) ⟨2627675, by rfl⟩ : syracuseStep 3503567 = 5255351) B5255351
theorem B67279187 : Blo 1843623 67279187 := bstep (se 1 (by rfl) ⟨50459390, by rfl⟩ : syracuseStep 67279187 = 100918781) B100918781
theorem B12614411 : Blo 1843623 12614411 := bstep (se 1 (by rfl) ⟨9460808, by rfl⟩ : syracuseStep 12614411 = 18921617) B18921617
theorem B42607079 : Blo 1843623 42607079 := bstep (se 1 (by rfl) ⟨31955309, by rfl⟩ : syracuseStep 42607079 = 63910619) B63910619
theorem B2335711 : Blo 1843623 2335711 := bstep (se 1 (by rfl) ⟨1751783, by rfl⟩ : syracuseStep 2335711 = 3503567) B3503567
theorem B44852791 : Blo 1843623 44852791 := bstep (se 1 (by rfl) ⟨33639593, by rfl⟩ : syracuseStep 44852791 = 67279187) B67279187
theorem B4671209 : Blo 1843623 4671209 := bstep (se 2 (by rfl) ⟨1751703, by rfl⟩ : syracuseStep 4671209 = 3503407) B3503407
theorem B33638429 : Blo 1843623 33638429 := bstep (se 3 (by rfl) ⟨6307205, by rfl⟩ : syracuseStep 33638429 = 12614411) B12614411
theorem B3503263 : Blo 1843623 3503263 := bstep (se 1 (by rfl) ⟨2627447, by rfl⟩ : syracuseStep 3503263 = 5254895) B5254895
theorem B6649471 : Blo 1843623 6649471 := bstep (se 1 (by rfl) ⟨4987103, by rfl⟩ : syracuseStep 6649471 = 9974207) B9974207
theorem B35463845 : Blo 1843623 35463845 := bstep (se 4 (by rfl) ⟨3324735, by rfl⟩ : syracuseStep 35463845 = 6649471) B6649471
theorem B3114139 : Blo 1843623 3114139 := bstep (se 1 (by rfl) ⟨2335604, by rfl⟩ : syracuseStep 3114139 = 4671209) B4671209
theorem B3114281 : Blo 1843623 3114281 := bstep (se 2 (by rfl) ⟨1167855, by rfl⟩ : syracuseStep 3114281 = 2335711) B2335711
theorem B4671017 : Blo 1843623 4671017 := bstep (se 2 (by rfl) ⟨1751631, by rfl⟩ : syracuseStep 4671017 = 3503263) B3503263
theorem B59803721 : Blo 1843623 59803721 := bstep (se 2 (by rfl) ⟨22426395, by rfl⟩ : syracuseStep 59803721 = 44852791) B44852791
theorem B28404719 : Blo 1843623 28404719 := bstep (se 1 (by rfl) ⟨21303539, by rfl⟩ : syracuseStep 28404719 = 42607079) B42607079
theorem B22425619 : Blo 1843623 22425619 := bstep (se 1 (by rfl) ⟨16819214, by rfl⟩ : syracuseStep 22425619 = 33638429) B33638429
theorem B29900825 : Blo 1843623 29900825 := bstep (se 2 (by rfl) ⟨11212809, by rfl⟩ : syracuseStep 29900825 = 22425619) B22425619
theorem B23642563 : Blo 1843623 23642563 := bstep (se 1 (by rfl) ⟨17731922, by rfl⟩ : syracuseStep 23642563 = 35463845) B35463845
theorem B3114011 : Blo 1843623 3114011 := bstep (se 1 (by rfl) ⟨2335508, by rfl⟩ : syracuseStep 3114011 = 4671017) B4671017
theorem B2076187 : Blo 1843623 2076187 := bstep (se 1 (by rfl) ⟨1557140, by rfl⟩ : syracuseStep 2076187 = 3114281) B3114281
theorem B18936479 : Blo 1843623 18936479 := bstep (se 1 (by rfl) ⟨14202359, by rfl⟩ : syracuseStep 18936479 = 28404719) B28404719
theorem B39869147 : Blo 1843623 39869147 := bstep (se 1 (by rfl) ⟨29901860, by rfl⟩ : syracuseStep 39869147 = 59803721) B59803721
theorem B4152185 : Blo 1843623 4152185 := bstep (se 2 (by rfl) ⟨1557069, by rfl⟩ : syracuseStep 4152185 = 3114139) B3114139
theorem B12624319 : Blo 1843623 12624319 := bstep (se 1 (by rfl) ⟨9468239, by rfl⟩ : syracuseStep 12624319 = 18936479) B18936479
theorem B31523417 : Blo 1843623 31523417 := bstep (se 2 (by rfl) ⟨11821281, by rfl⟩ : syracuseStep 31523417 = 23642563) B23642563
theorem B19933883 : Blo 1843623 19933883 := bstep (se 1 (by rfl) ⟨14950412, by rfl⟩ : syracuseStep 19933883 = 29900825) B29900825
theorem B2076007 : Blo 1843623 2076007 := bstep (se 1 (by rfl) ⟨1557005, by rfl⟩ : syracuseStep 2076007 = 3114011) B3114011
theorem B26579431 : Blo 1843623 26579431 := bstep (se 1 (by rfl) ⟨19934573, by rfl⟩ : syracuseStep 26579431 = 39869147) B39869147
theorem B2768123 : Blo 1843623 2768123 := bstep (se 1 (by rfl) ⟨2076092, by rfl⟩ : syracuseStep 2768123 = 4152185) B4152185
theorem B2768249 : Blo 1843623 2768249 := bstep (se 2 (by rfl) ⟨1038093, by rfl⟩ : syracuseStep 2768249 = 2076187) B2076187
theorem B35439241 : Blo 1843623 35439241 := bstep (se 2 (by rfl) ⟨13289715, by rfl⟩ : syracuseStep 35439241 = 26579431) B26579431
theorem B13289255 : Blo 1843623 13289255 := bstep (se 1 (by rfl) ⟨9966941, by rfl⟩ : syracuseStep 13289255 = 19933883) B19933883
theorem B1845415 : Blo 1843623 1845415 := bstep (se 1 (by rfl) ⟨1384061, by rfl⟩ : syracuseStep 1845415 = 2768123) B2768123
theorem B1845499 : Blo 1843623 1845499 := bstep (se 1 (by rfl) ⟨1384124, by rfl⟩ : syracuseStep 1845499 = 2768249) B2768249
theorem B21015611 : Blo 1843623 21015611 := bstep (se 1 (by rfl) ⟨15761708, by rfl⟩ : syracuseStep 21015611 = 31523417) B31523417
theorem B2768009 : Blo 1843623 2768009 := bstep (se 2 (by rfl) ⟨1038003, by rfl⟩ : syracuseStep 2768009 = 2076007) B2076007
theorem B67329701 : Blo 1843623 67329701 := bstep (se 4 (by rfl) ⟨6312159, by rfl⟩ : syracuseStep 67329701 = 12624319) B12624319
theorem B47252321 : Blo 1843623 47252321 := bstep (se 2 (by rfl) ⟨17719620, by rfl⟩ : syracuseStep 47252321 = 35439241) B35439241
theorem B14010407 : Blo 1843623 14010407 := bstep (se 1 (by rfl) ⟨10507805, by rfl⟩ : syracuseStep 14010407 = 21015611) B21015611
theorem B1845339 : Blo 1843623 1845339 := bstep (se 1 (by rfl) ⟨1384004, by rfl⟩ : syracuseStep 1845339 = 2768009) B2768009
theorem B44886467 : Blo 1843623 44886467 := bstep (se 1 (by rfl) ⟨33664850, by rfl⟩ : syracuseStep 44886467 = 67329701) B67329701
theorem B8859503 : Blo 1843623 8859503 := bstep (se 1 (by rfl) ⟨6644627, by rfl⟩ : syracuseStep 8859503 = 13289255) B13289255
theorem B9340271 : Blo 1843623 9340271 := bstep (se 1 (by rfl) ⟨7005203, by rfl⟩ : syracuseStep 9340271 = 14010407) B14010407
theorem B31501547 : Blo 1843623 31501547 := bstep (se 1 (by rfl) ⟨23626160, by rfl⟩ : syracuseStep 31501547 = 47252321) B47252321
theorem B29924311 : Blo 1843623 29924311 := bstep (se 1 (by rfl) ⟨22443233, by rfl⟩ : syracuseStep 29924311 = 44886467) B44886467
theorem B23625341 : Blo 1843623 23625341 := bstep (se 3 (by rfl) ⟨4429751, by rfl⟩ : syracuseStep 23625341 = 8859503) B8859503
theorem B6226847 : Blo 1843623 6226847 := bstep (se 1 (by rfl) ⟨4670135, by rfl⟩ : syracuseStep 6226847 = 9340271) B9340271
theorem B39899081 : Blo 1843623 39899081 := bstep (se 2 (by rfl) ⟨14962155, by rfl⟩ : syracuseStep 39899081 = 29924311) B29924311
theorem B21001031 : Blo 1843623 21001031 := bstep (se 1 (by rfl) ⟨15750773, by rfl⟩ : syracuseStep 21001031 = 31501547) B31501547
theorem B15750227 : Blo 1843623 15750227 := bstep (se 1 (by rfl) ⟨11812670, by rfl⟩ : syracuseStep 15750227 = 23625341) B23625341
theorem B14000687 : Blo 1843623 14000687 := bstep (se 1 (by rfl) ⟨10500515, by rfl⟩ : syracuseStep 14000687 = 21001031) B21001031
theorem B4151231 : Blo 1843623 4151231 := bstep (se 1 (by rfl) ⟨3113423, by rfl⟩ : syracuseStep 4151231 = 6226847) B6226847
theorem B10500151 : Blo 1843623 10500151 := bstep (se 1 (by rfl) ⟨7875113, by rfl⟩ : syracuseStep 10500151 = 15750227) B15750227
theorem B26599387 : Blo 1843623 26599387 := bstep (se 1 (by rfl) ⟨19949540, by rfl⟩ : syracuseStep 26599387 = 39899081) B39899081
theorem B14000201 : Blo 1843623 14000201 := bstep (se 2 (by rfl) ⟨5250075, by rfl⟩ : syracuseStep 14000201 = 10500151) B10500151
theorem B35465849 : Blo 1843623 35465849 := bstep (se 2 (by rfl) ⟨13299693, by rfl⟩ : syracuseStep 35465849 = 26599387) B26599387
theorem B9333791 : Blo 1843623 9333791 := bstep (se 1 (by rfl) ⟨7000343, by rfl⟩ : syracuseStep 9333791 = 14000687) B14000687
theorem B2767487 : Blo 1843623 2767487 := bstep (se 1 (by rfl) ⟨2075615, by rfl⟩ : syracuseStep 2767487 = 4151231) B4151231
theorem B23643899 : Blo 1843623 23643899 := bstep (se 1 (by rfl) ⟨17732924, by rfl⟩ : syracuseStep 23643899 = 35465849) B35465849
theorem B1844991 : Blo 1843623 1844991 := bstep (se 1 (by rfl) ⟨1383743, by rfl⟩ : syracuseStep 1844991 = 2767487) B2767487
theorem B9333467 : Blo 1843623 9333467 := bstep (se 1 (by rfl) ⟨7000100, by rfl⟩ : syracuseStep 9333467 = 14000201) B14000201
theorem B6222527 : Blo 1843623 6222527 := bstep (se 1 (by rfl) ⟨4666895, by rfl⟩ : syracuseStep 6222527 = 9333791) B9333791
theorem B15762599 : Blo 1843623 15762599 := bstep (se 1 (by rfl) ⟨11821949, by rfl⟩ : syracuseStep 15762599 = 23643899) B23643899
theorem B4148351 : Blo 1843623 4148351 := bstep (se 1 (by rfl) ⟨3111263, by rfl⟩ : syracuseStep 4148351 = 6222527) B6222527
theorem B6222311 : Blo 1843623 6222311 := bstep (se 1 (by rfl) ⟨4666733, by rfl⟩ : syracuseStep 6222311 = 9333467) B9333467
theorem B4148207 : Blo 1843623 4148207 := bstep (se 1 (by rfl) ⟨3111155, by rfl⟩ : syracuseStep 4148207 = 6222311) B6222311
theorem B2765567 : Blo 1843623 2765567 := bstep (se 1 (by rfl) ⟨2074175, by rfl⟩ : syracuseStep 2765567 = 4148351) B4148351
theorem B10508399 : Blo 1843623 10508399 := bstep (se 1 (by rfl) ⟨7881299, by rfl⟩ : syracuseStep 10508399 = 15762599) B15762599
theorem B1843711 : Blo 1843623 1843711 := bstep (se 1 (by rfl) ⟨1382783, by rfl⟩ : syracuseStep 1843711 = 2765567) B2765567
theorem B7005599 : Blo 1843623 7005599 := bstep (se 1 (by rfl) ⟨5254199, by rfl⟩ : syracuseStep 7005599 = 10508399) B10508399
theorem B2765471 : Blo 1843623 2765471 := bstep (se 1 (by rfl) ⟨2074103, by rfl⟩ : syracuseStep 2765471 = 4148207) B4148207
theorem B1843647 : Blo 1843623 1843647 := bstep (se 1 (by rfl) ⟨1382735, by rfl⟩ : syracuseStep 1843647 = 2765471) B2765471
theorem B4670399 : Blo 1843623 4670399 := bstep (se 1 (by rfl) ⟨3502799, by rfl⟩ : syracuseStep 4670399 = 7005599) B7005599
theorem B3113599 : Blo 1843623 3113599 := bstep (se 1 (by rfl) ⟨2335199, by rfl⟩ : syracuseStep 3113599 = 4670399) B4670399
theorem B4151465 : Blo 1843623 4151465 := bstep (se 2 (by rfl) ⟨1556799, by rfl⟩ : syracuseStep 4151465 = 3113599) B3113599
theorem B2767643 : Blo 1843623 2767643 := bstep (se 1 (by rfl) ⟨2075732, by rfl⟩ : syracuseStep 2767643 = 4151465) B4151465
theorem B1845095 : Blo 1843623 1845095 := bstep (se 1 (by rfl) ⟨1383821, by rfl⟩ : syracuseStep 1845095 = 2767643) B2767643

theorem C0 (j : ℕ) (h1 : 460905 ≤ j) (h2 : j ≤ 461405) : Blo 1843623 (4 * j + 3) := by
  interval_cases j
  · exact B1843623
  · exact B1843627
  · exact B1843631
  · exact B1843635
  · exact B1843639
  · exact B1843643
  · exact B1843647
  · exact B1843651
  · exact B1843655
  · exact B1843659
  · exact B1843663
  · exact B1843667
  · exact B1843671
  · exact B1843675
  · exact B1843679
  · exact B1843683
  · exact B1843687
  · exact B1843691
  · exact B1843695
  · exact B1843699
  · exact B1843703
  · exact B1843707
  · exact B1843711
  · exact B1843715
  · exact B1843719
  · exact B1843723
  · exact B1843727
  · exact B1843731
  · exact B1843735
  · exact B1843739
  · exact B1843743
  · exact B1843747
  · exact B1843751
  · exact B1843755
  · exact B1843759
  · exact B1843763
  · exact B1843767
  · exact B1843771
  · exact B1843775
  · exact B1843779
  · exact B1843783
  · exact B1843787
  · exact B1843791
  · exact B1843795
  · exact B1843799
  · exact B1843803
  · exact B1843807
  · exact B1843811
  · exact B1843815
  · exact B1843819
  · exact B1843823
  · exact B1843827
  · exact B1843831
  · exact B1843835
  · exact B1843839
  · exact B1843843
  · exact B1843847
  · exact B1843851
  · exact B1843855
  · exact B1843859
  · exact B1843863
  · exact B1843867
  · exact B1843871
  · exact B1843875
  · exact B1843879
  · exact B1843883
  · exact B1843887
  · exact B1843891
  · exact B1843895
  · exact B1843899
  · exact B1843903
  · exact B1843907
  · exact B1843911
  · exact B1843915
  · exact B1843919
  · exact B1843923
  · exact B1843927
  · exact B1843931
  · exact B1843935
  · exact B1843939
  · exact B1843943
  · exact B1843947
  · exact B1843951
  · exact B1843955
  · exact B1843959
  · exact B1843963
  · exact B1843967
  · exact B1843971
  · exact B1843975
  · exact B1843979
  · exact B1843983
  · exact B1843987
  · exact B1843991
  · exact B1843995
  · exact B1843999
  · exact B1844003
  · exact B1844007
  · exact B1844011
  · exact B1844015
  · exact B1844019
  · exact B1844023
  · exact B1844027
  · exact B1844031
  · exact B1844035
  · exact B1844039
  · exact B1844043
  · exact B1844047
  · exact B1844051
  · exact B1844055
  · exact B1844059
  · exact B1844063
  · exact B1844067
  · exact B1844071
  · exact B1844075
  · exact B1844079
  · exact B1844083
  · exact B1844087
  · exact B1844091
  · exact B1844095
  · exact B1844099
  · exact B1844103
  · exact B1844107
  · exact B1844111
  · exact B1844115
  · exact B1844119
  · exact B1844123
  · exact B1844127
  · exact B1844131
  · exact B1844135
  · exact B1844139
  · exact B1844143
  · exact B1844147
  · exact B1844151
  · exact B1844155
  · exact B1844159
  · exact B1844163
  · exact B1844167
  · exact B1844171
  · exact B1844175
  · exact B1844179
  · exact B1844183
  · exact B1844187
  · exact B1844191
  · exact B1844195
  · exact B1844199
  · exact B1844203
  · exact B1844207
  · exact B1844211
  · exact B1844215
  · exact B1844219
  · exact B1844223
  · exact B1844227
  · exact B1844231
  · exact B1844235
  · exact B1844239
  · exact B1844243
  · exact B1844247
  · exact B1844251
  · exact B1844255
  · exact B1844259
  · exact B1844263
  · exact B1844267
  · exact B1844271
  · exact B1844275
  · exact B1844279
  · exact B1844283
  · exact B1844287
  · exact B1844291
  · exact B1844295
  · exact B1844299
  · exact B1844303
  · exact B1844307
  · exact B1844311
  · exact B1844315
  · exact B1844319
  · exact B1844323
  · exact B1844327
  · exact B1844331
  · exact B1844335
  · exact B1844339
  · exact B1844343
  · exact B1844347
  · exact B1844351
  · exact B1844355
  · exact B1844359
  · exact B1844363
  · exact B1844367
  · exact B1844371
  · exact B1844375
  · exact B1844379
  · exact B1844383
  · exact B1844387
  · exact B1844391
  · exact B1844395
  · exact B1844399
  · exact B1844403
  · exact B1844407
  · exact B1844411
  · exact B1844415
  · exact B1844419
  · exact B1844423
  · exact B1844427
  · exact B1844431
  · exact B1844435
  · exact B1844439
  · exact B1844443
  · exact B1844447
  · exact B1844451
  · exact B1844455
  · exact B1844459
  · exact B1844463
  · exact B1844467
  · exact B1844471
  · exact B1844475
  · exact B1844479
  · exact B1844483
  · exact B1844487
  · exact B1844491
  · exact B1844495
  · exact B1844499
  · exact B1844503
  · exact B1844507
  · exact B1844511
  · exact B1844515
  · exact B1844519
  · exact B1844523
  · exact B1844527
  · exact B1844531
  · exact B1844535
  · exact B1844539
  · exact B1844543
  · exact B1844547
  · exact B1844551
  · exact B1844555
  · exact B1844559
  · exact B1844563
  · exact B1844567
  · exact B1844571
  · exact B1844575
  · exact B1844579
  · exact B1844583
  · exact B1844587
  · exact B1844591
  · exact B1844595
  · exact B1844599
  · exact B1844603
  · exact B1844607
  · exact B1844611
  · exact B1844615
  · exact B1844619
  · exact B1844623
  · exact B1844627
  · exact B1844631
  · exact B1844635
  · exact B1844639
  · exact B1844643
  · exact B1844647
  · exact B1844651
  · exact B1844655
  · exact B1844659
  · exact B1844663
  · exact B1844667
  · exact B1844671
  · exact B1844675
  · exact B1844679
  · exact B1844683
  · exact B1844687
  · exact B1844691
  · exact B1844695
  · exact B1844699
  · exact B1844703
  · exact B1844707
  · exact B1844711
  · exact B1844715
  · exact B1844719
  · exact B1844723
  · exact B1844727
  · exact B1844731
  · exact B1844735
  · exact B1844739
  · exact B1844743
  · exact B1844747
  · exact B1844751
  · exact B1844755
  · exact B1844759
  · exact B1844763
  · exact B1844767
  · exact B1844771
  · exact B1844775
  · exact B1844779
  · exact B1844783
  · exact B1844787
  · exact B1844791
  · exact B1844795
  · exact B1844799
  · exact B1844803
  · exact B1844807
  · exact B1844811
  · exact B1844815
  · exact B1844819
  · exact B1844823
  · exact B1844827
  · exact B1844831
  · exact B1844835
  · exact B1844839
  · exact B1844843
  · exact B1844847
  · exact B1844851
  · exact B1844855
  · exact B1844859
  · exact B1844863
  · exact B1844867
  · exact B1844871
  · exact B1844875
  · exact B1844879
  · exact B1844883
  · exact B1844887
  · exact B1844891
  · exact B1844895
  · exact B1844899
  · exact B1844903
  · exact B1844907
  · exact B1844911
  · exact B1844915
  · exact B1844919
  · exact B1844923
  · exact B1844927
  · exact B1844931
  · exact B1844935
  · exact B1844939
  · exact B1844943
  · exact B1844947
  · exact B1844951
  · exact B1844955
  · exact B1844959
  · exact B1844963
  · exact B1844967
  · exact B1844971
  · exact B1844975
  · exact B1844979
  · exact B1844983
  · exact B1844987
  · exact B1844991
  · exact B1844995
  · exact B1844999
  · exact B1845003
  · exact B1845007
  · exact B1845011
  · exact B1845015
  · exact B1845019
  · exact B1845023
  · exact B1845027
  · exact B1845031
  · exact B1845035
  · exact B1845039
  · exact B1845043
  · exact B1845047
  · exact B1845051
  · exact B1845055
  · exact B1845059
  · exact B1845063
  · exact B1845067
  · exact B1845071
  · exact B1845075
  · exact B1845079
  · exact B1845083
  · exact B1845087
  · exact B1845091
  · exact B1845095
  · exact B1845099
  · exact B1845103
  · exact B1845107
  · exact B1845111
  · exact B1845115
  · exact B1845119
  · exact B1845123
  · exact B1845127
  · exact B1845131
  · exact B1845135
  · exact B1845139
  · exact B1845143
  · exact B1845147
  · exact B1845151
  · exact B1845155
  · exact B1845159
  · exact B1845163
  · exact B1845167
  · exact B1845171
  · exact B1845175
  · exact B1845179
  · exact B1845183
  · exact B1845187
  · exact B1845191
  · exact B1845195
  · exact B1845199
  · exact B1845203
  · exact B1845207
  · exact B1845211
  · exact B1845215
  · exact B1845219
  · exact B1845223
  · exact B1845227
  · exact B1845231
  · exact B1845235
  · exact B1845239
  · exact B1845243
  · exact B1845247
  · exact B1845251
  · exact B1845255
  · exact B1845259
  · exact B1845263
  · exact B1845267
  · exact B1845271
  · exact B1845275
  · exact B1845279
  · exact B1845283
  · exact B1845287
  · exact B1845291
  · exact B1845295
  · exact B1845299
  · exact B1845303
  · exact B1845307
  · exact B1845311
  · exact B1845315
  · exact B1845319
  · exact B1845323
  · exact B1845327
  · exact B1845331
  · exact B1845335
  · exact B1845339
  · exact B1845343
  · exact B1845347
  · exact B1845351
  · exact B1845355
  · exact B1845359
  · exact B1845363
  · exact B1845367
  · exact B1845371
  · exact B1845375
  · exact B1845379
  · exact B1845383
  · exact B1845387
  · exact B1845391
  · exact B1845395
  · exact B1845399
  · exact B1845403
  · exact B1845407
  · exact B1845411
  · exact B1845415
  · exact B1845419
  · exact B1845423
  · exact B1845427
  · exact B1845431
  · exact B1845435
  · exact B1845439
  · exact B1845443
  · exact B1845447
  · exact B1845451
  · exact B1845455
  · exact B1845459
  · exact B1845463
  · exact B1845467
  · exact B1845471
  · exact B1845475
  · exact B1845479
  · exact B1845483
  · exact B1845487
  · exact B1845491
  · exact B1845495
  · exact B1845499
  · exact B1845503
  · exact B1845507
  · exact B1845511
  · exact B1845515
  · exact B1845519
  · exact B1845523
  · exact B1845527
  · exact B1845531
  · exact B1845535
  · exact B1845539
  · exact B1845543
  · exact B1845547
  · exact B1845551
  · exact B1845555
  · exact B1845559
  · exact B1845563
  · exact B1845567
  · exact B1845571
  · exact B1845575
  · exact B1845579
  · exact B1845583
  · exact B1845587
  · exact B1845591
  · exact B1845595
  · exact B1845599
  · exact B1845603
  · exact B1845607
  · exact B1845611
  · exact B1845615
  · exact B1845619
  · exact B1845623

theorem solution (m : ℕ) (hlo : 1843623 ≤ m) (hhi : m ≤ 1845623) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 460905 ≤ j := by omega
    have hj2 : j ≤ 461405 := by omega
    have hb : Blo 1843623 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
