-- Prove2me | solution 1 for log_pow_sq_lt_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T23:18:59.535687+00:00
-- url     : https://prove2.me/submissions/9fd0eb6b-18bb-41d2-be13-d1c7c6c5704c

import Mathlib

section
-- module Solutions.OAIQ093_PR.Unipotent_GammaN
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Existence of a unipotent `γ_n`

`exists_gamma_n_unipotent_center_N'` and `exists_gamma_n_unipotent_N'`.
-/


set_option linter.style.longLine false
set_option linter.style.commandStart false
set_option linter.style.cdot false

open scoped commutatorElement IsMulCommutative Pointwise

variable {G: Type*} [Group G] [DecidableEq G] (S: Finset G)

/-- Final step of isolating `K`, reducing the `h_poly` log inequality to a statement in `ℕ`.

Splits `Real.log ↑(p * K ^ q)` into `Real.log ↑p + q * Real.log ↑K`, then eliminates the
`Real.log ↑K` using `Real.log_natCast_le_rpow_div` at `ε := 1/4`, which gives
`Real.log K ≤ 4 * K ^ (1/4)`; squaring therefore contributes only a `K ^ (1/2)` term, which
the right-hand `K` dominates.  (At `ε := 1/2` the reduction would be unsound for `q ≥ 1`.)
The hypothesis mentions `K` only on the right, and is an inequality of naturals. -/
theorem log_pow_sq_lt_of_lt_oai (M p q K : ℕ) (hp : 0 < p)
    (h : ⌈4 * ((8 * (q:ℝ) + Real.log p) ^ 2 / (Real.log 2) ^ 2) ^ 2⌉₊ + 2 * M < K) :
    ((4 * (q:ℝ) + Real.log ((p * K ^ q : ℕ) : ℝ)) / Real.log 2) ^ 2 + (M:ℝ) < (K:ℝ) := by
  have hK1 : 1 ≤ K := by omega
  have hpr : ((p : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  have hKr : ((K : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hsplit : Real.log ((p * K ^ q : ℕ) : ℝ) = Real.log p + q * Real.log K := by
    push_cast; rw [Real.log_mul hpr (pow_ne_zero _ hKr), Real.log_pow]
  rw [hsplit]
  have h' : 4 * ((8 * (q:ℝ) + Real.log p) ^ 2 / (Real.log 2) ^ 2) ^ 2 + 2 * (M:ℝ) < (K:ℝ) := by
    have hceil := Nat.le_ceil (4 * ((8 * (q:ℝ) + Real.log p) ^ 2 / (Real.log 2) ^ 2) ^ 2)
    have hcast : ((⌈4 * ((8 * (q:ℝ) + Real.log p) ^ 2 / (Real.log 2) ^ 2) ^ 2⌉₊ + 2 * M : ℕ) : ℝ)
        < (K:ℝ) := by exact_mod_cast h
    push_cast at hcast
    linarith
  have hK0 : (0:ℝ) < (K:ℝ) := by exact_mod_cast hK1
  have hlogK0 : 0 ≤ Real.log (K:ℝ) := Real.log_nonneg (by exact_mod_cast hK1)
  have hlogp0 : 0 ≤ Real.log (p:ℝ) := Real.log_nonneg (by exact_mod_cast hp)
  have hM0 : (0:ℝ) ≤ (M:ℝ) := Nat.cast_nonneg M
  set u : ℝ := (K:ℝ) ^ ((1:ℝ)/4) with hu
  have hu1 : (1:ℝ) ≤ u := by
    rw [hu]; exact Real.one_le_rpow (by exact_mod_cast hK1) (by norm_num)
  have hu4 : u ^ 4 = (K:ℝ) := by
    rw [hu, ← Real.rpow_natCast ((K:ℝ) ^ ((1:ℝ)/4)) 4, ← Real.rpow_mul hK0.le]; norm_num
  have hlogK : Real.log (K:ℝ) ≤ 4 * u := by
    calc Real.log (K:ℝ) ≤ (K:ℝ) ^ ((1:ℝ)/4) / ((1:ℝ)/4) :=
          Real.log_natCast_le_rpow_div K (by norm_num)
      _ = 4 * u := by rw [hu]; ring
  have hnum : 4 * (q:ℝ) + (Real.log p + q * Real.log K) ≤ (8 * (q:ℝ) + Real.log p) * u := by
    nlinarith
  have hsq : ((4 * (q:ℝ) + (Real.log p + q * Real.log K)) / Real.log 2) ^ 2
      ≤ (8 * (q:ℝ) + Real.log p) ^ 2 / (Real.log 2) ^ 2 * u ^ 2 := by
    have hstep : ((4 * (q:ℝ) + (Real.log p + q * Real.log K)) / Real.log 2) ^ 2
        ≤ ((8 * (q:ℝ) + Real.log p) * u / Real.log 2) ^ 2 := by gcongr
    calc _ ≤ ((8 * (q:ℝ) + Real.log p) * u / Real.log 2) ^ 2 := hstep
      _ = (8 * (q:ℝ) + Real.log p) ^ 2 / (Real.log 2) ^ 2 * u ^ 2 := by field_simp
  set D : ℝ := (8 * (q:ℝ) + Real.log p) ^ 2 / (Real.log 2) ^ 2 with hD
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  have hgoal : D * u ^ 2 + (M:ℝ) < (K:ℝ) := by
    nlinarith [sq_nonneg (u ^ 2 - 2 * D), hu1, hD0, hM0, hu4, h']
  linarith [hsq, hgoal]


--   -- simp at ord_fin
--   --rw [Nat.card_prod] at ord_fin
end

theorem solution : type_of% @log_pow_sq_lt_of_lt_oai := @log_pow_sq_lt_of_lt_oai
