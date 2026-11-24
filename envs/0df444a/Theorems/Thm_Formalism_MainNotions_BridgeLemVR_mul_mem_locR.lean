-- Prove2me | Theorems.Thm_Formalism_MainNotions_BridgeLemVR_mul_mem_locR
-- name    : Formalism.MainNotions.BridgeLemVR.mul_mem_locR
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T09:56:08.650147+00:00
-- url     : https://prove2.me/theorems/187a952f-2bc1-43be-b61a-c6cecc5987dc
-- title:
--   Bridge Lem VR: mul mem loc R
-- statement:
--   The Bridge Lem VR construction uses the mul mem loc R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/BridgeLemVR.lean#L29-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/BridgeLemVR.lean#L29-L38

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMassConstOne
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandA
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLemVR
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_SplitA_mul_mem_locR

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLemVR
open NumberField Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.RankOne nonZeroDivisors
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem Formalism.MainNotions.BridgeLemVR.mul_mem_locR {p : Ideal (𝓞 K)} {x y : K} (hx : x ∈ locR (K := K) p) (hy : y ∈ locR (K := K) p) :
    x * y ∈ locR (K := K) p := by sorry
