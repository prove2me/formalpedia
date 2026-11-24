-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z0_SGA_InJ_mul
-- name    : Formalism.L2.SG.Pf.LatDictZ.Z0.SGA.InJ.mul
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T15:20:25.40759+00:00
-- url     : https://prove2.me/theorems/42813613-62b6-486e-ba9c-f6e01aaa1f88
-- title:
--   In J: mul
-- statement:
--   The In J construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SelfDualUnimodular/LocalLatticeDictionary/ExistsUnitNorm.lean#L74-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SelfDualUnimodular/LocalLatticeDictionary/ExistsUnitNorm.lean#L74-L92

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZAbs
import Definitions.Def_Formalism_SelfDualUnimodular_LocalLatticeDictionary_ExistsUnitNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatDictZ Formalism.L2.SG.Pf.LatDictZ.Z0 Formalism.L2.SG.Pf.LatDictZ.Z0.SGA
open ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem Formalism.L2.SG.Pf.LatDictZ.Z0.SGA.InJ.mul {p : Ideal (𝓞 K)} (hp : p.IsPrime) {κ a : K} (hκ : κ ∈ locRing p) (ha : InJ p a) :
    InJ p (κ * a) := by sorry
