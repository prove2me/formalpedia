-- Prove2me | Theorems.Thm_Formalism_MainNotions_BridgeLemVC_iota_apply
-- name    : Formalism.MainNotions.BridgeLemVC.iota_apply
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:09:09.573447+00:00
-- url     : https://prove2.me/theorems/1b049407-6aa1-5383-9e9a-b72e30d60b09
-- title:
--   Bridge Lem VC: iota apply
-- statement:
--   The Bridge Lem VC construction uses the iota apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/BridgeLemVC.lean#L78-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/BridgeLemVC.lean#L78-L78

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

theorem Formalism.MainNotions.BridgeLemVC.iota_apply (t : (𝓞 (cmF K))ˣ) : iota K t = (((t : 𝓞 (cmF K)) : cmF K) : K) := by sorry
