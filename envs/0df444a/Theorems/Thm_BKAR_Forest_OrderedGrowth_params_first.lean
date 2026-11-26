-- Prove2me | Theorems.Thm_BKAR_Forest_OrderedGrowth_params_first
-- name    : BKAR.Forest.OrderedGrowth.params_first
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:37:44.564253+00:00
-- url     : https://prove2.me/theorems/c58d218e-bb94-5c37-ace1-900560a4aae2
-- title:
--   Ordered Growth: params first
-- statement:
--   The first simplex parameter is assigned to the first edge of a nonempty growth.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedParams.lean#L164-L176
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedParams.lean#L164-L176

import Definitions.Def_BKAR_OrderedSimplex
import Definitions.Def_BKAR_OrderedParams
import Theorems.Thm_BKAR_Forest_OrderedGrowth_mem_edges_of_mem_order

set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}

theorem BKAR.Forest.OrderedGrowth.params_first (h : OrderedGrowth F (e :: order) G)
    (u : F.EdgeParam → ℝ) (t : ℝ) (ts : List ℝ) :
    h.params u (t :: ts) ⟨e, h.mem_edges_of_mem_order
      (by rw [List.mem_cons]; exact Or.inl rfl)⟩ = t := by sorry
