-- Prove2me | Theorems.Thm_Eden_tendsto_radiusEvolution_one_iff
-- name    : Eden.tendsto_radiusEvolution_one_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:29:16.367597+00:00
-- url     : https://prove2.me/theorems/0d898c19-8e17-5765-b275-bb7300c5a022
-- title:
--   Eden: tendsto radius Evolution one iff
-- statement:
--   The Eden construction uses the tendsto radius Evolution one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/RadialQualitative.lean#L51-L63
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/RadialQualitative.lean#L51-L63

import Definitions.Def_Eden_PhysicalRadius
import Definitions.Def_Eden_Uniqueness
import Definitions.Def_Eden_RadialQualitative
set_option autoImplicit true
noncomputable section
open Filter Set
open scoped Topology
open Eden

theorem Eden.tendsto_radiusEvolution_one_iff {r : ℝ} (hr : 0 ≤ r) :
    Tendsto (fun t => radiusEvolution t r) atTop (𝓝 1) ↔ r = 1 := by sorry
