-- Prove2me | Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegrand_congr_branchPoint
-- name    : BKAR.Forest.OrderedGrowth.branchIntegrand_congr_branchPoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:38:44.846997+00:00
-- url     : https://prove2.me/theorems/f2495783-540b-4144-87a4-84313beb1189
-- title:
--   Ordered Growth: branch Integrand congr branch Point
-- statement:
--   The Ordered Growth construction uses the branch Integrand congr branch Point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedBranch.lean#L172-L177
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedBranch.lean#L172-L177

import Definitions.Def_BKAR_OrderedParams
import Definitions.Def_BKAR_OrderedBranch
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}

theorem BKAR.Forest.OrderedGrowth.branchIntegrand_congr_branchPoint (h : OrderedGrowth F order G)
    (u v : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hpoint : ∀ ts, h.branchPoint u ts = h.branchPoint v ts) :
    h.branchIntegrand u ρ = h.branchIntegrand v ρ := by sorry
