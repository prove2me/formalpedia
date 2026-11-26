-- Prove2me | Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegral_congr_branchPoint
-- name    : BKAR.Forest.OrderedGrowth.branchIntegral_congr_branchPoint
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:39:43.499369+00:00
-- url     : https://prove2.me/theorems/9a94c985-37ee-5ec7-b642-4361cda93120
-- title:
--   Ordered Growth: branch Integral congr branch Point
-- statement:
--   The Ordered Growth construction uses the branch Integral congr branch Point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedBranch.lean#L258-L263
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedBranch.lean#L258-L263

import Definitions.Def_BKAR_OrderedParams
import Definitions.Def_BKAR_OrderedBranch
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}

theorem BKAR.Forest.OrderedGrowth.branchIntegral_congr_branchPoint (h : OrderedGrowth F order G)
    (u v : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hpoint : ∀ ts, h.branchPoint u ts = h.branchPoint v ts) :
    h.branchIntegral u ρ = h.branchIntegral v ρ := by sorry
