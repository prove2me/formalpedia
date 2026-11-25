-- Prove2me | Theorems.Thm_Formalism_MainNotions_BridgeLemVR_mem_loc_iff
-- name    : Formalism.MainNotions.BridgeLemVR.mem_loc_iff
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:52:50.482075+00:00
-- url     : https://prove2.me/theorems/315f096b-e82a-528a-8d4d-66988fad240b
-- title:
--   Bridge Lem VR: mem loc iff
-- statement:
--   The Bridge Lem VR construction uses the mem loc iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/BridgeLemVR.lean#L12-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/BridgeLemVR.lean#L12-L13

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMassConstOne
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandA
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLemVR
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

theorem Formalism.MainNotions.BridgeLemVR.mem_loc_iff (p : Ideal (𝓞 K)) (N : Submodule (𝓞 K) K) (x : K) :
    x ∈ loc (K := K) p N ↔ ∃ s ∈ hcompl (K := K) p, s • x ∈ N := by sorry
