-- Prove2me | Theorems.Thm_Formalism_MainNotions_BridgeLemVR_conjO_mem_hcompl
-- name    : Formalism.MainNotions.BridgeLemVR.conjO_mem_hcompl
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T09:55:44.828695+00:00
-- url     : https://prove2.me/theorems/4c66cb70-a0de-49b2-b8fd-6d24e8c1b3bc
-- title:
--   Bridge Lem VR: conj O mem hcompl
-- statement:
--   The Bridge Lem VR construction uses the conj O mem hcompl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/BridgeLemVR.lean#L40-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/BridgeLemVR.lean#L40-L56

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMassConstOne
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandA
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLemVR
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_SplitA_conjO_mem_hcompl
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_conjO_mem_hcompl

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

theorem Formalism.MainNotions.BridgeLemVR.conjO_mem_hcompl {p : Ideal (𝓞 K)} {s : 𝓞 K} (hs : s ∈ hcompl (K := K) p) :
    conjO K s ∈ hcompl (K := K) p := by sorry
