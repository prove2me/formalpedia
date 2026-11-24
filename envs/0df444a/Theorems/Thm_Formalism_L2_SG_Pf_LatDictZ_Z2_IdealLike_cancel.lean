-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z2_IdealLike_cancel
-- name    : Formalism.L2.SG.Pf.LatDictZ.Z2.IdealLike.cancel
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T15:37:55.979898+00:00
-- url     : https://prove2.me/theorems/772a7892-9ef8-4d5b-8126-fbbbc5179157
-- title:
--   Ideal Like: cancel
-- statement:
--   The Ideal Like construction uses the cancel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/LatDictZPlane.lean#L25-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/LatDictZPlane.lean#L25-L28

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZPlane
import Theorems.Thm_PIW_AdelClassFin_DictRing_cancel

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
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatDictZ Formalism.L2.SG.Pf.LatDictZ.Z2
open ReciprocityTheory.ChartRestriction.L3.WA
variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]

theorem Formalism.L2.SG.Pf.LatDictZ.Z2.IdealLike.cancel {S : Subring K} {P : K → Prop} (hP : IdealLike S P) {μ a : K}
    (hμ : IsUnitIn S μ) (h : P (μ * a)) : P a := by sorry
