-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z2_IdealLike_not_one_add
-- name    : Formalism.L2.SG.Pf.LatDictZ.Z2.IdealLike.not_one_add
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T16:57:34.909438+00:00
-- url     : https://prove2.me/theorems/5d8cebfb-e6ef-4ca9-9820-cfacb71866c6
-- title:
--   Ideal Like: not one add
-- statement:
--   The Ideal Like construction uses the not one add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/LatDictZPlane.lean#L30-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/LatDictZPlane.lean#L30-L38

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZPlane
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

theorem Formalism.L2.SG.Pf.LatDictZ.Z2.IdealLike.not_one_add {S : Subring K} {P : K → Prop} (hP : IdealLike S P) {ε η : K}
    (hε : P ε) (hη : P η) {x y : K} (hx : x ∈ S) (hy : y ∈ S) {v : K} (hv : v = 1 + x * ε + y * η) :
    ¬ P v := by sorry
