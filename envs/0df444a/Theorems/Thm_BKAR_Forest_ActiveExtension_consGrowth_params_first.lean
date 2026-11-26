-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveExtension_consGrowth_params_first
-- name    : BKAR.Forest.ActiveExtension.consGrowth_params_first
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:44:34.074877+00:00
-- url     : https://prove2.me/theorems/86dcc40e-e3a6-5247-b790-d76488bdfad9
-- title:
--   Active Extension: cons Growth params first
-- statement:
--   The Active Extension construction uses the cons Growth params first property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedRecursion.lean#L57-L63
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedRecursion.lean#L57-L63

import Definitions.Def_BKAR_OrderedTerminal
import Definitions.Def_BKAR_OrderedRecursion
import Theorems.Thm_BKAR_Forest_OrderedGrowth_mem_edges_of_mem_order
import Theorems.Thm_BKAR_OrderedSimplexParams_tail

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveExtension
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}

theorem BKAR.Forest.ActiveExtension.consGrowth_params_first (h : ActiveExtension F e)
    (tail : OrderedGrowth h.forest order G)
    (u : F.EdgeParam → ℝ) (t : ℝ) (ts : List ℝ) :
    (h.consGrowth tail).params u (t :: ts)
        ⟨e, (h.consGrowth tail).mem_edges_of_mem_order
          (by rw [List.mem_cons]; exact Or.inl rfl)⟩ = t := by sorry
