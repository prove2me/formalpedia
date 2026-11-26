-- Prove2me | Theorems.Thm_BKAR_partialDeriv_of_hasFDerivAt
-- name    : BKAR.partialDeriv_of_hasFDerivAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:19:52.762314+00:00
-- url     : https://prove2.me/theorems/b54a304a-6f2c-5999-82f2-960333401b75
-- title:
--   BKAR: partial Deriv of has FDeriv At
-- statement:
--   The BKAR construction uses the partial Deriv of has FDeriv At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/PartialDeriv.lean#L83-L97
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/PartialDeriv.lean#L83-L97

import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Pi
import Definitions.Def_BKAR_Interpolation
import Definitions.Def_BKAR_PartialDeriv
set_option autoImplicit false
open BKAR
variable {V : Type*} [DecidableEq V]

theorem BKAR.partialDeriv_of_hasFDerivAt [Fintype V] (e : Edge V)
    {ρ : (Edge V → ℝ) → ℝ} {x : Edge V → ℝ}
    {ρ' : (Edge V → ℝ) →L[ℝ] ℝ}
    (hρ : HasFDerivAt ρ ρ' x) :
    partialDeriv e ρ x = ρ' (edgeBasis e) := by sorry
