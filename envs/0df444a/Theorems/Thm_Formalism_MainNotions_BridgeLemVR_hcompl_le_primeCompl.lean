-- Prove2me | Theorems.Thm_Formalism_MainNotions_BridgeLemVR_hcompl_le_primeCompl
-- name    : Formalism.MainNotions.BridgeLemVR.hcompl_le_primeCompl
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T09:55:06.385055+00:00
-- url     : https://prove2.me/theorems/ca7bca18-0f77-4638-962a-d06f51f3085d
-- title:
--   Bridge Lem VR: hcompl le prime Compl
-- statement:
--   The Bridge Lem VR construction uses the hcompl le prime Compl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/BridgeLemVR.lean#L18-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/BridgeLemVR.lean#L18-L24

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

theorem Formalism.MainNotions.BridgeLemVR.hcompl_le_primeCompl {p : Ideal (𝓞 K)} (hp : p.IsMaximal) :
    hcompl (K := K) p ≤ p.primeCompl := by sorry
