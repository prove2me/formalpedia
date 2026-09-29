-- Prove2me | solution 1 for mme_stothers_remaining_four_optimizer_certificates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T20:57:57.737773+00:00
-- url     : https://prove2.me/submissions/b1f2910a-f765-4944-b628-f762d3fd9908

import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped Real

set_option autoImplicit false

namespace MME.StothersFourth.RemainingFour

/-! Exact optimizer algebra used in Davie--Stothers Lemma 5.1(ii)--(v).

The finite extraction is the hard combinatorial input.  This file isolates the
calculus-free part of the argument: positive binary and ternary entropy factors
at their normalized weights, the four endpoint identities, and the profile
feasibility inequalities. -/

private theorem binary_optimizer
    (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    (x / (x / (x + y))) ^ (x / (x + y)) *
        (y / (y / (x + y))) ^ (y / (x + y)) =
      x + y := by
  have hs : 0 < x + y := add_pos hx hy
  have hqx : x / (x / (x + y)) = x + y := by
    field_simp
  have hqy : y / (y / (x + y)) = x + y := by
    field_simp
  rw [hqx, hqy, ← Real.rpow_add hs]
  have hsum : x / (x + y) + y / (x + y) = 1 := by
    field_simp
  rw [hsum, Real.rpow_one]

private theorem ternary_optimizer
    (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (x / (x / (x + y + z))) ^ (x / (x + y + z)) *
        (y / (y / (x + y + z))) ^ (y / (x + y + z)) *
        (z / (z / (x + y + z))) ^ (z / (x + y + z)) =
      x + y + z := by
  have hs : 0 < x + y + z := add_pos (add_pos hx hy) hz
  have hqx : x / (x / (x + y + z)) = x + y + z := by
    field_simp
  have hqy : y / (y / (x + y + z)) = x + y + z := by
    field_simp
  have hqz : z / (z / (x + y + z)) = x + y + z := by
    field_simp
  rw [hqx, hqy, hqz, ← Real.rpow_add hs, ← Real.rpow_add hs]
  have hsum :
      x / (x + y + z) + y / (x + y + z) + z / (x + y + z) = 1 := by
    field_simp
  rw [hsum, Real.rpow_one]

/-- At the two independent normalized binary weights used for `phi_125`,
the entropy factors collapse to the exact endpoint in Lemma 5.1(ii). -/
theorem phi125_optimizer_value
    (E H L : ℝ) (hE : 0 < E) (hH : 0 < H) (hL : 0 < L) :
    let a := L / (L + E * H)
    let b := L / (L + 2 * H)
    4 / H *
        ((L / a) ^ a * ((E * H) / (1 - a)) ^ (1 - a)) *
        ((L / b) ^ b * ((2 * H) / (1 - b)) ^ (1 - b)) =
      4 * (L + E * H) * (2 * H + L) / H := by
  dsimp
  have hEH : 0 < E * H := mul_pos hE hH
  have h2H : 0 < 2 * H := mul_pos (by norm_num) hH
  have hA : 0 < L + E * H := add_pos hL hEH
  have hB : 0 < L + 2 * H := add_pos hL h2H
  have hca : 1 - L / (L + E * H) = (E * H) / (L + E * H) := by
    field_simp [ne_of_gt hA]
    ring
  have hcb : 1 - L / (L + 2 * H) = (2 * H) / (L + 2 * H) := by
    field_simp [ne_of_gt hB]
    ring
  rw [hca, hcb]
  rw [binary_optimizer L (E * H) hL hEH]
  rw [binary_optimizer L (2 * H) hL h2H]
  ring

/-- The binary and ternary normalized weights used for `phi_134` give the
exact endpoint in Lemma 5.1(iii). -/
theorem phi134_optimizer_value
    (E H L : ℝ) (hE : 0 < E) (hH : 0 < H) (hL : 0 < L) :
    let sigma := L / (E + L)
    let a := 2 / (2 + 2 * E + H)
    let c := H / (2 + 2 * E + H)
    8 *
        ((L / sigma) ^ sigma *
          (E / (1 - sigma)) ^ (1 - sigma)) *
        ((1 / a) ^ a *
          ((H / 2) / c) ^ c *
          (E / (1 - a - c)) ^ (1 - a - c)) =
      4 * (E + L) * (2 + 2 * E + H) := by
  dsimp
  have hEL : 0 < E + L := add_pos hE hL
  have hD : 0 < 2 + 2 * E + H := by positivity
  have hhalf : 0 < H / 2 := div_pos hH (by norm_num)
  have hcs : 1 - L / (E + L) = E / (E + L) := by
    field_simp [ne_of_gt hEL]
    ring
  have hcar :
      1 - 2 / (2 + 2 * E + H) - H / (2 + 2 * E + H) =
        (2 * E) / (2 + 2 * E + H) := by
    field_simp [ne_of_gt hD]
    ring
  rw [hcs, hcar]
  have hbin :
      (L / (L / (E + L))) ^ (L / (E + L)) *
          (E / (E / (E + L))) ^ (E / (E + L)) = E + L := by
    simpa [add_comm] using binary_optimizer L E hL hE
  rw [hbin]
  have htri := ternary_optimizer (1 : ℝ) (H / 2) E (by norm_num) hhalf hE
  have hsum : (1 : ℝ) + H / 2 + E = (2 + 2 * E + H) / 2 := by ring
  have ha :
      (1 : ℝ) / ((1 : ℝ) + H / 2 + E) =
        2 / (2 + 2 * E + H) := by
    rw [hsum]
    field_simp [ne_of_gt hD]
  have hc :
      (H / 2) / ((1 : ℝ) + H / 2 + E) =
        H / (2 + 2 * E + H) := by
    rw [hsum]
    field_simp [ne_of_gt hD]
  have hr :
      E / ((1 : ℝ) + H / 2 + E) =
        (2 * E) / (2 + 2 * E + H) := by
    rw [hsum]
    field_simp [ne_of_gt hD]
  rw [ha, hc, hr, hsum] at htri
  rw [htri]
  ring

/-- The binary and ternary normalized weights used for `phi_224` give the
exact endpoint in Lemma 5.1(iv). -/
theorem phi224_optimizer_value
    (E H L : ℝ) (hE : 0 < E) (hH : 0 < H) (hL : 0 < L) :
    let sigma := 2 * H / (2 * H + L)
    let a := 2 / (2 + 2 * E + H)
    let b := 2 * E / (2 + 2 * E + H)
    (((2 * H) / sigma) ^ sigma *
        (L / (1 - sigma)) ^ (1 - sigma)) ^ (2 : ℕ) *
      (((2 / H) / a) ^ a *
        ((2 * E / H) / b) ^ b *
        (1 / (1 - a - b)) ^ (1 - a - b)) =
      (2 * H + L) ^ (2 : ℕ) * (2 + 2 * E + H) / H := by
  dsimp
  have h2H : 0 < 2 * H := mul_pos (by norm_num) hH
  have hHL : 0 < 2 * H + L := add_pos h2H hL
  have hD : 0 < 2 + 2 * E + H := by positivity
  have hcs : 1 - (2 * H) / (2 * H + L) = L / (2 * H + L) := by
    field_simp [ne_of_gt hHL]
    ring
  have hcar :
      1 - 2 / (2 + 2 * E + H) - (2 * E) / (2 + 2 * E + H) =
        H / (2 + 2 * E + H) := by
    field_simp [ne_of_gt hD]
    ring
  rw [hcs, hcar]
  rw [binary_optimizer (2 * H) L h2H hL]
  have hx : 0 < 2 / H := div_pos (by norm_num) hH
  have hy : 0 < 2 * E / H := div_pos (mul_pos (by norm_num) hE) hH
  have htri := ternary_optimizer (2 / H) (2 * E / H) 1 hx hy (by norm_num)
  have hsum : 2 / H + 2 * E / H + 1 = (2 + 2 * E + H) / H := by
    field_simp [ne_of_gt hH]
  have ha :
      (2 / H) / (2 / H + 2 * E / H + 1) =
        2 / (2 + 2 * E + H) := by
    rw [hsum]
    field_simp [ne_of_gt hH, ne_of_gt hD]
  have hb :
      (2 * E / H) / (2 / H + 2 * E / H + 1) =
        (2 * E) / (2 + 2 * E + H) := by
    rw [hsum]
    field_simp [ne_of_gt hH, ne_of_gt hD]
  have hr :
      (1 : ℝ) / (2 / H + 2 * E / H + 1) =
        H / (2 + 2 * E + H) := by
    rw [hsum]
    field_simp [ne_of_gt hH, ne_of_gt hD]
  rw [ha, hb, hr, hsum] at htri
  rw [htri]
  field_simp [ne_of_gt hH]

/-- The two binary normalized weights used for `phi_233` give the exact
endpoint in Lemma 5.1(v). -/
theorem phi233_optimizer_value
    (E H L : ℝ) (hE : 0 < E) (hH : 0 < H) (hL : 0 < L) :
    let sigma := (2 * H / L) / (2 * H / L + 1)
    let mu := (E / L) / (E / L + 1)
    4 * L ^ (2 : ℕ) *
        (((2 * H / L) / sigma) ^ sigma *
          (1 / (1 - sigma)) ^ (1 - sigma)) *
        (((E / L) / mu) ^ mu *
          (1 / (1 - mu)) ^ (1 - mu)) ^ (2 : ℕ) =
      4 * (E + L) ^ (2 : ℕ) * (2 * H + L) / L := by
  dsimp
  have hx : 0 < 2 * H / L := div_pos (mul_pos (by norm_num) hH) hL
  have hy : 0 < E / L := div_pos hE hL
  have hsx : 0 < 2 * H / L + 1 := add_pos hx (by norm_num)
  have hsy : 0 < E / L + 1 := add_pos hy (by norm_num)
  have hcx :
      1 - (2 * H / L) / (2 * H / L + 1) =
        1 / (2 * H / L + 1) := by
    field_simp [ne_of_gt hsx, ne_of_gt hL]
    ring
  have hcy :
      1 - (E / L) / (E / L + 1) = 1 / (E / L + 1) := by
    field_simp [ne_of_gt hsy, ne_of_gt hL]
    ring
  rw [hcx, hcy]
  rw [binary_optimizer (2 * H / L) 1 hx (by norm_num)]
  rw [binary_optimizer (E / L) 1 hy (by norm_num)]
  field_simp [ne_of_gt hL]

/-- The selected `phi_125` weights satisfy the simplex constraint under the
paper's coarse inequalities `16 ≤ E < H < L < 4H`. -/
theorem phi125_optimizer_feasible
    (E H L : ℝ) (h16E : 16 ≤ E) (hEH : E < H)
    (hHL : H < L) (hL4H : L < 4 * H) :
    let a := L / (L + E * H)
    let b := L / (L + 2 * H)
    0 < a ∧ 0 < b ∧ a + b ≤ 1 := by
  dsimp
  have hE : 0 < E := lt_of_lt_of_le (by norm_num) h16E
  have hH : 0 < H := lt_trans hE hEH
  have hL : 0 < L := lt_trans hH hHL
  have hEHpos : 0 < E * H := mul_pos hE hH
  have hA : 0 < L + E * H := add_pos hL hEHpos
  have hB : 0 < L + 2 * H := by positivity
  refine ⟨div_pos hL hA, div_pos hL hB, ?_⟩
  have hsq : L ^ (2 : ℕ) ≤ 16 * H ^ (2 : ℕ) := by
    have hplus : 0 ≤ 4 * H + L := by positivity
    have hp := mul_nonneg (sub_nonneg.mpr (le_of_lt hL4H))
      hplus
    nlinarith
  have hscale := mul_nonneg (sub_nonneg.mpr h16E) (sq_nonneg H)
  have hkey : L ^ (2 : ℕ) ≤ 2 * E * H ^ (2 : ℕ) := by
    nlinarith
  have hid :
      L / (L + E * H) + L / (L + 2 * H) =
        (L * (L + 2 * H) + L * (L + E * H)) /
          ((L + E * H) * (L + 2 * H)) := by
    field_simp [ne_of_gt hA, ne_of_gt hB]
  rw [hid]
  apply (div_le_one (mul_pos hA hB)).2
  nlinarith

/-- The selected `phi_134` weights define nonnegative frequencies under
the paper's coarse inequalities. -/
theorem phi134_optimizer_feasible
    (E H L : ℝ) (h16E : 16 ≤ E) (hEH : E < H)
    (hHL : H < L) (hL4H : L < 4 * H) :
    let sigma := L / (E + L)
    let a := 2 / (2 + 2 * E + H)
    let c := H / (2 + 2 * E + H)
    0 < a ∧ 0 < c ∧ c ≤ sigma ∧ sigma + a ≤ 1 := by
  dsimp
  have hE : 0 < E := lt_of_lt_of_le (by norm_num) h16E
  have hH : 0 < H := lt_trans hE hEH
  have hL : 0 < L := lt_trans hH hHL
  have hEL : 0 < E + L := add_pos hE hL
  have hD : 0 < 2 + 2 * E + H := by positivity
  refine ⟨div_pos (by norm_num) hD, div_pos hH hD, ?_, ?_⟩
  · apply (div_le_div_iff₀ hD hEL).2
    have hp := mul_nonneg (le_of_lt hE) (sub_nonneg.mpr (le_of_lt hHL))
    nlinarith
  · have hid :
        L / (E + L) + 2 / (2 + 2 * E + H) =
          (L * (2 + 2 * E + H) + 2 * (E + L)) /
            ((E + L) * (2 + 2 * E + H)) := by
      field_simp [ne_of_gt hEL, ne_of_gt hD]
    rw [hid]
    apply (div_le_one (mul_pos hEL hD)).2
    have hp := mul_nonneg (sub_nonneg.mpr h16E) (le_of_lt hH)
    nlinarith

/-- The selected `phi_224` weights are feasible once the two exact rational
inequalities isolated in Lemma 5.1(iv) hold.  They are stated explicitly
because the first does not follow from the four coarse order inequalities for
arbitrary reals without using the special formulas for `E`, `H`, and `L`. -/
theorem phi224_optimizer_feasible
    (E H L : ℝ) (hE : 0 < E) (hH : 0 < H) (hL : 0 < L)
    (hleft : (2 + E) * L ≤ 2 * H * (E + H))
    (hright : 2 * E * H ≤ L * (2 + E + H)) :
    let sigma := 2 * H / (2 * H + L)
    let a := 2 / (2 + 2 * E + H)
    let b := E / (2 + 2 * E + H)
    0 < a ∧ 0 < b ∧ a + b ≤ sigma ∧ sigma ≤ 1 - b := by
  dsimp
  have hD : 0 < 2 + 2 * E + H := by positivity
  have hS : 0 < 2 * H + L := by positivity
  refine ⟨div_pos (by norm_num) hD, div_pos hE hD, ?_, ?_⟩
  · have hid : 2 / (2 + 2 * E + H) + E / (2 + 2 * E + H) =
        (2 + E) / (2 + 2 * E + H) := by ring
    rw [hid]
    apply (div_le_div_iff₀ hD hS).2
    nlinarith
  · have hcomp : 1 - E / (2 + 2 * E + H) =
        (2 + E + H) / (2 + 2 * E + H) := by
      field_simp [ne_of_gt hD]
      ring
    rw [hcomp]
    apply (div_le_div_iff₀ hS hD).2
    nlinarith

/-- The selected `phi_233` weights satisfy the only required compatibility
condition under the coarse order inequalities. -/
theorem phi233_optimizer_feasible
    (E H L : ℝ) (hE : 0 < E) (hH : 0 < H) (hEL : E < L) :
    let sigma := 2 * H / (2 * H + L)
    let mu := E / (E + L)
    0 < sigma ∧ 0 < mu ∧ sigma + 2 * mu ≤ 2 := by
  dsimp
  have hL : 0 < L := lt_trans hE hEL
  have hS : 0 < 2 * H + L := by positivity
  have hT : 0 < E + L := add_pos hE hL
  refine ⟨div_pos (mul_pos (by norm_num) hH) hS, div_pos hE hT, ?_⟩
  have hkey : E * H ≤ L * (H + L) := by
    have hp := mul_nonneg (sub_nonneg.mpr (le_of_lt hEL)) (le_of_lt hH)
    have hLsq := sq_nonneg L
    nlinarith
  have hid :
      2 * H / (2 * H + L) + 2 * (E / (E + L)) =
        (2 * H * (E + L) + 2 * E * (2 * H + L)) /
          ((2 * H + L) * (E + L)) := by
    field_simp [ne_of_gt hS, ne_of_gt hT]
  rw [hid]
  apply (div_le_iff₀ (mul_pos hS hT)).2
  nlinarith

end MME.StothersFourth.RemainingFour

open MME.StothersFourth.RemainingFour

/-- Public bundle of the exact remaining-four optimizer substitutions and
their feasibility checks. -/
theorem solution
    (E H L : ℝ) (h16E : 16 ≤ E) (hEH : E < H)
    (hHL : H < L) (hL4H : L < 4 * H)
    (h224left : (2 + E) * L ≤ 2 * H * (E + H))
    (h224right : 2 * E * H ≤ L * (2 + E + H)) :
    (let a := L / (L + E * H)
     let b := L / (L + 2 * H)
     0 < a ∧ 0 < b ∧ a + b ≤ 1 ∧
       4 / H *
          ((L / a) ^ a * ((E * H) / (1 - a)) ^ (1 - a)) *
          ((L / b) ^ b * ((2 * H) / (1 - b)) ^ (1 - b)) =
        4 * (L + E * H) * (2 * H + L) / H) ∧
    (let sigma := L / (E + L)
     let a := 2 / (2 + 2 * E + H)
     let c := H / (2 + 2 * E + H)
     0 < a ∧ 0 < c ∧ c ≤ sigma ∧ sigma + a ≤ 1 ∧
       8 *
          ((L / sigma) ^ sigma *
            (E / (1 - sigma)) ^ (1 - sigma)) *
          ((1 / a) ^ a *
            ((H / 2) / c) ^ c *
            (E / (1 - a - c)) ^ (1 - a - c)) =
        4 * (E + L) * (2 + 2 * E + H)) ∧
    (let sigma := 2 * H / (2 * H + L)
     let a := 2 / (2 + 2 * E + H)
     let b := 2 * E / (2 + 2 * E + H)
     0 < a ∧ 0 < b ∧
       a + b / 2 ≤ sigma ∧ sigma ≤ 1 - b / 2 ∧
       (((2 * H) / sigma) ^ sigma *
          (L / (1 - sigma)) ^ (1 - sigma)) ^ (2 : ℕ) *
        (((2 / H) / a) ^ a *
          ((2 * E / H) / b) ^ b *
          (1 / (1 - a - b)) ^ (1 - a - b)) =
        (2 * H + L) ^ (2 : ℕ) * (2 + 2 * E + H) / H) ∧
    (let sigma := (2 * H / L) / (2 * H / L + 1)
     let mu := (E / L) / (E / L + 1)
     0 < sigma ∧ 0 < mu ∧ sigma + 2 * mu ≤ 2 ∧
       4 * L ^ (2 : ℕ) *
          (((2 * H / L) / sigma) ^ sigma *
            (1 / (1 - sigma)) ^ (1 - sigma)) *
          (((E / L) / mu) ^ mu *
            (1 / (1 - mu)) ^ (1 - mu)) ^ (2 : ℕ) =
        4 * (E + L) ^ (2 : ℕ) * (2 * H + L) / L) := by
  have hE : 0 < E := lt_of_lt_of_le (by norm_num) h16E
  have hH : 0 < H := lt_trans hE hEH
  have hL : 0 < L := lt_trans hH hHL
  have hf125 := phi125_optimizer_feasible E H L h16E hEH hHL hL4H
  have hv125 := phi125_optimizer_value E H L hE hH hL
  have hf134 := phi134_optimizer_feasible E H L h16E hEH hHL hL4H
  have hv134 := phi134_optimizer_value E H L hE hH hL
  have hf224 := phi224_optimizer_feasible E H L hE hH hL h224left h224right
  have hv224 := phi224_optimizer_value E H L hE hH hL
  have hf233 := phi233_optimizer_feasible E H L hE hH (lt_trans hEH hHL)
  have hv233 := phi233_optimizer_value E H L hE hH hL
  dsimp at hf125 hv125 hf134 hv134 hf224 hv224 hf233 hv233 ⊢
  have hsigma233 :
      (2 * H / L) / (2 * H / L + 1) = 2 * H / (2 * H + L) := by
    field_simp [ne_of_gt hL]
  have hmu233 : (E / L) / (E / L + 1) = E / (E + L) := by
    field_simp [ne_of_gt hL]
  refine ⟨⟨hf125.1, hf125.2.1, hf125.2.2, hv125⟩,
    ⟨hf134.1, hf134.2.1, hf134.2.2.1, hf134.2.2.2, hv134⟩,
    ?_, ?_⟩
  · have hD : 0 < 2 + 2 * E + H := by positivity
    have hbpos : 0 < 2 * E / (2 + 2 * E + H) :=
      div_pos (mul_pos (by norm_num) hE) hD
    have hbhalf :
        (2 * E / (2 + 2 * E + H)) / 2 = E / (2 + 2 * E + H) := by
      field_simp [ne_of_gt hD]
    exact ⟨hf224.1, hbpos, by simpa only [hbhalf] using hf224.2.2.1,
      by simpa only [hbhalf] using hf224.2.2.2, hv224⟩
  · rw [hsigma233, hmu233]
    exact ⟨hf233.1, hf233.2.1, hf233.2.2, by simpa [hsigma233, hmu233] using hv233⟩
