-- Prove2me | Theorems.Thm_BKAR_Forest_le_pathMinAux_iff
-- name    : BKAR.Forest.le_pathMinAux_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:17:38.821623+00:00
-- url     : https://prove2.me/theorems/2bb9603f-b4b5-469d-87fd-8a08998e3cf6
-- title:
--   Forest: le path Min Aux iff
-- statement:
--   The Forest construction uses the le path Min Aux iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Threshold.lean#L47-L67
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Threshold.lean#L47-L67

import Definitions.Def_BKAR_Interpolation
import Definitions.Def_BKAR_Threshold
set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable section

theorem BKAR.Forest.le_pathMinAux_iff (F : Forest V) (u : F.EdgeParam → ℝ)
    (s a : ℝ) :
    ∀ γ : List (Edge V),
      s ≤ F.pathMinAux u a γ ↔
        s ≤ a ∧ ∀ e ∈ γ, s ≤ F.paramValue u e
  := by sorry
