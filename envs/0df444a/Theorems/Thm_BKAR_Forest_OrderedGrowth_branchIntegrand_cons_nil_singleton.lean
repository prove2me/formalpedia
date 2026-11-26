-- Prove2me | Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegrand_cons_nil_singleton
-- name    : BKAR.Forest.OrderedGrowth.branchIntegrand_cons_nil_singleton
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:39:19.08626+00:00
-- url     : https://prove2.me/theorems/de469070-436b-5af6-b9e2-bd1eb732a9fc
-- title:
--   Ordered Growth: branch Integrand cons nil singleton
-- statement:
--   The Ordered Growth construction uses the branch Integrand cons nil singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedBranch.lean#L218-L224
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedBranch.lean#L218-L224

import Definitions.Def_BKAR_OrderedParams
import Definitions.Def_BKAR_OrderedBranch
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}

theorem BKAR.Forest.OrderedGrowth.branchIntegrand_cons_nil_singleton {F F' : Forest V} {e : Edge V}
    (step : EdgeExtension F F' e) (u : F.EdgeParam → ℝ)
    (ρ : (Edge V → ℝ) → ℝ) (t : ℝ) :
    (OrderedGrowth.cons step (OrderedGrowth.nil F')).branchIntegrand u ρ [t] =
      partialDeriv e ρ (F'.standardInterp (step.extendParam u t)) := by sorry
