-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z2_plane_unit
-- name    : Formalism.L2.SG.Pf.LatDictZ.Z2.plane_unit
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T16:57:37.034256+00:00
-- url     : https://prove2.me/theorems/91898d86-d96b-4d8f-a287-5feee6fd1c4c
-- title:
--   Z2: plane unit
-- statement:
--   The Z2 construction uses the plane unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/LatDictZPlane.lean#L254-L258
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/LatDictZPlane.lean#L254-L258

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
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem Formalism.L2.SG.Pf.LatDictZ.Z2.plane_unit {p : Ideal (𝓞 K)} (hp : p.IsPrime) {a : K} (ha : a ∈ locRing p)
    (h1 : ¬ InI p p a) (h2 : ¬ InI p (Formalism.HermitianLatticesTheory.conjIdeal (K := K) p) a) : IsUnitIn (locRing p) a := by sorry
