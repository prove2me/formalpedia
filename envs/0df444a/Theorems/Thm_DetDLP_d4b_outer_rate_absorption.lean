-- Prove2me | Theorems.Thm_DetDLP_d4b_outer_rate_absorption
-- name    : DetDLP.d4b_outer_rate_absorption
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-24T08:50:22.700402+00:00
-- url     : https://prove2.me/theorems/f5aaca9f-580a-49bf-b0fa-a7c9c18615f5
-- title:
--   Uniform absorption of outer-cursor and scalar exponents
-- statement:
--   For every admissible terminal input and supplied plan, one constant depending only on the input class bounds both the branch-and-digit enumeration exponent and the degree-sensitive scalar exponent by the target terminal contraction rate.
-- source:
--   Estimates for the outer cursor (dc44082d-fc56-402c-8efa-dc7eda4aebd8), using the block and logarithm estimates of accepted submissions 68bba6bc-95cc-4706-8762-1af3f04f70c1 and 923e02d6-1db3-405a-8654-3ee7aafd12a3.

import Definitions.Def_DetDLP_D4Plan
set_option autoImplicit false
open DetDLP DetDLP.D4Plan

theorem DetDLP.d4b_outer_rate_absorption (C c : ℕ) (hC : 0<C) : ∃ A : ℕ, ∀ x : Input C c,
    let L := Nat.clog 2 x.S; let rate := (x.b:ℝ)/x.m+(x.b:ℝ)/Real.sqrt (logSafe x.m)
    ((x.b:ℝ)/(L:ℝ)^(7/40:ℝ) + (L:ℝ)^(13/10:ℝ)) ≤ A*rate ∧
    ∀ (P : Plan x) (u : Fin P.N),
      let Δ := max (P.R u).maxDeg ⌈(x.b:ℝ)^(9/10:ℝ)⌉₊
      let ρ := max 1 ⌊Real.logb 2 ((x.b:ℝ)/Δ)⌋₊
      (x.b:ℝ)/Real.sqrt ρ ≤ A*rate := by sorry
