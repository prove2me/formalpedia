-- Prove2me | Theorems.Thm_Formalism_MainNotions_BridgeLemVR_mem_locR_iff
-- name    : Formalism.MainNotions.BridgeLemVR.mem_locR_iff
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:54:57.268701+00:00
-- url     : https://prove2.me/theorems/baa940f0-2d64-53e2-ab69-1904544a88c1
-- title:
--   Bridge Lem VR: mem loc R iff
-- statement:
--   The Bridge Lem VR construction uses the mem loc R iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/BridgeLemVR.lean#L15-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/BridgeLemVR.lean#L15-L16

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMassConstOne
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandA
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLemVR
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_mem_locR_iff

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

theorem Formalism.MainNotions.BridgeLemVR.mem_locR_iff (p : Ideal (𝓞 K)) (x : K) :
    x ∈ locR (K := K) p ↔ ∃ s ∈ hcompl (K := K) p, s • x ∈ (1 : Submodule (𝓞 K) K) := by sorry
