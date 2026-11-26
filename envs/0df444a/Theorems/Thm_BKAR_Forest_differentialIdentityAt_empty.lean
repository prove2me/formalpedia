-- Prove2me | Theorems.Thm_BKAR_Forest_differentialIdentityAt_empty
-- name    : BKAR.Forest.differentialIdentityAt_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:22:09.09373+00:00
-- url     : https://prove2.me/theorems/66e386b5-5a25-49ff-858e-dada1c01ba49
-- title:
--   Forest: differential Identity At empty
-- statement:
--   The Forest construction uses the differential Identity At empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Differential.lean#L297-L317
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Differential.lean#L297-L317

import Mathlib.Analysis.Calculus.Deriv.Prod
import Definitions.Def_BKAR_PartialDeriv
import Definitions.Def_BKAR_Differential
set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.differentialIdentityAt_empty
    (u : (Forest.empty V).EdgeParam → ℝ)
    {ρ : (Edge V → ℝ) → ℝ} {t : ℝ}
    (hρ : DifferentiableAt ℝ ρ (constantConfig t)) :
    deriv (fun s : ℝ => ρ (constantConfig s)) t =
      Finset.sum (Finset.univ : Finset (Edge V))
        (fun e => partialDeriv e ρ (constantConfig t)) := by sorry
