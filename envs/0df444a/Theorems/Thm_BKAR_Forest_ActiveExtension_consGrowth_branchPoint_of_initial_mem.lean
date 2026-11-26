-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveExtension_consGrowth_branchPoint_of_initial_mem
-- name    : BKAR.Forest.ActiveExtension.consGrowth_branchPoint_of_initial_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:36:07.663633+00:00
-- url     : https://prove2.me/theorems/228d1b57-f008-4622-9981-fb21198a6473
-- title:
--   Active Extension: cons Growth branch Point of initial mem
-- statement:
--   The Active Extension construction uses the cons Growth branch Point of initial mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedRecursion.lean#L71-L76
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedRecursion.lean#L71-L76

import Definitions.Def_BKAR_OrderedTerminal
import Definitions.Def_BKAR_OrderedRecursion
import Theorems.Thm_BKAR_OrderedSimplexParams_tail

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveExtension
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}

theorem BKAR.Forest.ActiveExtension.consGrowth_branchPoint_of_initial_mem (h : ActiveExtension F e)
    (tail : OrderedGrowth h.forest order G)
    (u : F.EdgeParam → ℝ) (ts : List ℝ) {e' : Edge V}
    (he' : e' ∈ F.edges) :
    (h.consGrowth tail).branchPoint u ts e' = u ⟨e', he'⟩ := by sorry
