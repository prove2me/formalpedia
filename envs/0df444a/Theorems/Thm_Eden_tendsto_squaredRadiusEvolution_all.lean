-- Prove2me | Theorems.Thm_Eden_tendsto_squaredRadiusEvolution_all
-- name    : Eden.tendsto_squaredRadiusEvolution_all
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:17:56.834251+00:00
-- url     : https://prove2.me/theorems/8bbc5af2-8b97-535f-a295-ca55e9e502e3
-- title:
--   Eden: tendsto squared Radius Evolution all
-- statement:
--   The Eden construction uses the tendsto squared Radius Evolution all property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FactorLimits.lean#L25-L32
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FactorLimits.lean#L25-L32

import Definitions.Def_Eden_RealTimeAverages
import Definitions.Def_Eden_GrowthRates
import Definitions.Def_Eden_InvariantSets
import Definitions.Def_Eden_DerivativeDecomposition
import Definitions.Def_Eden_FactorLimits
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden

theorem Eden.tendsto_squaredRadiusEvolution_all (s : ℝ) :
    Tendsto (fun t => squaredRadiusEvolution t s) atTop (𝓝 (limitingSquaredRadius s)) := by sorry
