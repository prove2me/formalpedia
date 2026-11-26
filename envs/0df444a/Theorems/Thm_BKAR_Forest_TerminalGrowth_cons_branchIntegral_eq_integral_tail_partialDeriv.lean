-- Prove2me | Theorems.Thm_BKAR_Forest_TerminalGrowth_cons_branchIntegral_eq_integral_tail_partialDeriv
-- name    : BKAR.Forest.TerminalGrowth.cons_branchIntegral_eq_integral_tail_partialDeriv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:46:09.924989+00:00
-- url     : https://prove2.me/theorems/1e440512-7a60-436d-8bfb-1e57b9195e6a
-- title:
--   Terminal Growth: cons branch Integral eq integral tail partial Deriv
-- statement:
--   Unit-simplex recursive form of
--   `TerminalGrowth.cons_branchIntegralAux_eq_integral_tail_partialDeriv`.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L232-L240
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L232-L240

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Theorems.Thm_BKAR_OrderedSimplexParams_tail

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.TerminalGrowth
variable {F : Forest V}

theorem BKAR.Forest.TerminalGrowth.cons_branchIntegral_eq_integral_tail_partialDeriv
    {e : Edge V} (h : ActiveExtension F e)
    (tail : TerminalGrowth h.forest)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    (cons h tail).branchIntegral u ρ =
      ∫ t in 0..(1 : ℝ),
        tail.branchIntegralAux t (h.extension.extendParam u t)
          (partialDeriv e ρ) := by sorry
