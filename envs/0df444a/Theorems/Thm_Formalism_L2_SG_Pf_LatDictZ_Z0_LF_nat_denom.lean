-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z0_LF_nat_denom
-- name    : Formalism.L2.SG.Pf.LatDictZ.Z0.LF.nat_denom
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:51:42.078573+00:00
-- url     : https://prove2.me/theorems/41335b25-0871-46e0-91d0-3352ddb9f205
-- title:
--   LF: nat denom
-- statement:
--   The LF construction uses the nat denom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SelfDualUnimodular/LocalLatticeDictionary/LocFin.lean#L15-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SelfDualUnimodular/LocalLatticeDictionary/LocFin.lean#L15-L31

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZAbs
import Definitions.Def_Lemmata_Denominators_Denom
import Definitions.Def_Formalism_SelfDualUnimodular_LocalLatticeDictionary_LocFin
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
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatDictZ Formalism.L2.SG.Pf.LatDictZ.Z0 Formalism.L2.SG.Pf.LatDictZ.Z0.LF
open ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA
variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

theorem Formalism.L2.SG.Pf.LatDictZ.Z0.LF.nat_denom (e : E) : ∃ m : ℕ, 0 < m ∧ ∃ r : 𝓞 E, (m : E) * e = algebraMap (𝓞 E) E r := by sorry
