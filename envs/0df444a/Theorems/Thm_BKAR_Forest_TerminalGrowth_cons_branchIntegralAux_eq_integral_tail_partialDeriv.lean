-- Prove2me | Theorems.Thm_BKAR_Forest_TerminalGrowth_cons_branchIntegralAux_eq_integral_tail_partialDeriv
-- name    : BKAR.Forest.TerminalGrowth.cons_branchIntegralAux_eq_integral_tail_partialDeriv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:43:31.479799+00:00
-- url     : https://prove2.me/theorems/5fe1167f-67de-4afd-a0cf-8bf45c60fb92
-- title:
--   Terminal Growth: cons branch Integral Aux eq integral tail partial Deriv
-- statement:
--   The recursive form of a terminal branch obtained by prepending one active
--   extension.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L217-L226
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L217-L226

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

theorem BKAR.Forest.TerminalGrowth.cons_branchIntegralAux_eq_integral_tail_partialDeriv
    {e : Edge V} (h : ActiveExtension F e)
    (tail : TerminalGrowth h.forest) (top : ℝ)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    (cons h tail).branchIntegralAux top u ρ =
      ∫ t in 0..top,
        tail.branchIntegralAux t (h.extension.extendParam u t)
          (partialDeriv e ρ) := by sorry
