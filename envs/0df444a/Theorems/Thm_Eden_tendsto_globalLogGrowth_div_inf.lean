-- Prove2me | Theorems.Thm_Eden_tendsto_globalLogGrowth_div_inf
-- name    : Eden.tendsto_globalLogGrowth_div_inf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:39:35.092069+00:00
-- url     : https://prove2.me/theorems/0a562cdd-347d-592b-935a-5da99667bc5e
-- title:
--   Eden: tendsto global Log Growth div inf
-- statement:
--   The Eden construction uses the tendsto global Log Growth div inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/GlobalGrowthLimits.lean#L19-L25
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/GlobalGrowthLimits.lean#L19-L25

import Definitions.Def_Eden_RealSubadditive
import Definitions.Def_Eden_GlobalGrowthLimits
set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden

theorem Eden.tendsto_globalLogGrowth_div_inf {k : ℕ} (hk : k ≤ 5) {c : ℝ}
    (hc : 4 ≤ c) :
    Tendsto (fun t : ℝ => globalLogGrowth c k t / t) atTop
      (𝓝 (sInf ((fun T : ℝ => globalLogGrowth c k T / T) '' Ioi 0))) := by sorry
