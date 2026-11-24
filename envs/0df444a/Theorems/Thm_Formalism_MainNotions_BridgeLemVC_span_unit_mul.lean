-- Prove2me | Theorems.Thm_Formalism_MainNotions_BridgeLemVC_span_unit_mul
-- name    : Formalism.MainNotions.BridgeLemVC.span_unit_mul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T09:55:20.956485+00:00
-- url     : https://prove2.me/theorems/bcf7ca1f-837a-4083-9b97-28b0a95b20ee
-- title:
--   Bridge Lem VC: span unit mul
-- statement:
--   The Bridge Lem VC construction uses the span unit mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/BridgeLemVC.lean#L101-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/BridgeLemVC.lean#L101-L111

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLemVR
import Definitions.Def_Formalism_FlagUnipotentLattices_ArithmeticIdentityEntries
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_DifferentIdealEqTop
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLemVC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLemVC
open NumberField Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.RankOne Formalism.MainNotions.BridgeLemVR nonZeroDivisors
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem Formalism.MainNotions.BridgeLemVC.span_unit_mul (w : (𝓞 K)ˣ) (N : Submodule (𝓞 K) K) :
    Submodule.span (𝓞 K) {algebraMap (𝓞 K) K (w : 𝓞 K)} * N = N := by sorry
