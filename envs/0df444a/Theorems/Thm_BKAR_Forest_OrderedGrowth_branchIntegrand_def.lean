-- Prove2me | Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegrand_def
-- name    : BKAR.Forest.OrderedGrowth.branchIntegrand_def
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:32:04.792211+00:00
-- url     : https://prove2.me/theorems/433322f9-2d8c-4528-8605-3c55dc7e2eea
-- title:
--   Ordered Growth: branch Integrand def
-- statement:
--   The Ordered Growth construction uses the branch Integrand def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedBranch.lean#L160-L164
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedBranch.lean#L160-L164

import Definitions.Def_BKAR_OrderedParams
import Definitions.Def_BKAR_OrderedBranch
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}

theorem BKAR.Forest.OrderedGrowth.branchIntegrand_def (h : OrderedGrowth F order G)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) (ts : List ℝ) :
    h.branchIntegrand u ρ ts =
      mixedPartialList order.reverse ρ (h.branchPoint u ts) := by sorry
