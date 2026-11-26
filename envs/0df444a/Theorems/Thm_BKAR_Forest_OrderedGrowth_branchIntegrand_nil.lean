-- Prove2me | Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegrand_nil
-- name    : BKAR.Forest.OrderedGrowth.branchIntegrand_nil
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:39:09.344804+00:00
-- url     : https://prove2.me/theorems/01645ff4-290c-52c2-ac43-dc7d4ba2ea05
-- title:
--   Ordered Growth: branch Integrand nil
-- statement:
--   The Ordered Growth construction uses the branch Integrand nil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedBranch.lean#L187-L190
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedBranch.lean#L187-L190

import Definitions.Def_BKAR_OrderedParams
import Definitions.Def_BKAR_OrderedBranch
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}

theorem BKAR.Forest.OrderedGrowth.branchIntegrand_nil (F : Forest V)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) (ts : List ℝ) :
    (OrderedGrowth.nil F).branchIntegrand u ρ ts = ρ (F.standardInterp u) := by sorry

attribute [defeq] BKAR.Forest.OrderedGrowth.branchIntegrand_nil
