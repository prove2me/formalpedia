-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z2_plane_idealLike
-- name    : Formalism.L2.SG.Pf.LatDictZ.Z2.plane_idealLike
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T16:57:32.690639+00:00
-- url     : https://prove2.me/theorems/3d82bfb9-54b3-4751-9023-7dfead05f0b6
-- title:
--   Z2: plane ideal Like
-- statement:
--   The Z2 construction uses the plane ideal Like property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/LatDictZPlane.lean#L234-L252
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/LatDictZPlane.lean#L234-L252

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

theorem Formalism.L2.SG.Pf.LatDictZ.Z2.plane_idealLike {p : Ideal (𝓞 K)} (hp : p.IsPrime) (I : Ideal (𝓞 K))
    (hI : ∀ s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p, s ∉ I) : IdealLike (locRing p) (InI p I) := by sorry
