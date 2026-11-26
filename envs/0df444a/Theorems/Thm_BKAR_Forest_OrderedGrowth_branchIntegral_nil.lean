-- Prove2me | Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegral_nil
-- name    : BKAR.Forest.OrderedGrowth.branchIntegral_nil
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:39:10.64209+00:00
-- url     : https://prove2.me/theorems/fe9d9439-2991-593a-96d2-f0cca77b03ac
-- title:
--   Ordered Growth: branch Integral nil
-- statement:
--   The Ordered Growth construction uses the branch Integral nil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedBranch.lean#L193-L196
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedBranch.lean#L193-L196

import Definitions.Def_BKAR_OrderedParams
import Definitions.Def_BKAR_OrderedBranch
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}

theorem BKAR.Forest.OrderedGrowth.branchIntegral_nil (F : Forest V)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    (OrderedGrowth.nil F).branchIntegral u ρ = ρ (F.standardInterp u) := by sorry

attribute [defeq] BKAR.Forest.OrderedGrowth.branchIntegral_nil
