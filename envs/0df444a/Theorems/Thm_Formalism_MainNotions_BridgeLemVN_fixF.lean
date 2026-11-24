-- Prove2me | Theorems.Thm_Formalism_MainNotions_BridgeLemVN_fixF
-- name    : Formalism.MainNotions.BridgeLemVN.fixF
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T09:43:46.66293+00:00
-- url     : https://prove2.me/theorems/98f2e3f4-de1f-4d6c-8dec-f3ae4bcc2e7a
-- title:
--   Bridge Lem VN: fix F
-- statement:
--   The Bridge Lem VN construction uses the fix F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/BridgeLemVN.lean#L12-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/BridgeLemVN.lean#L12-L19

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLemVC
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLemVN
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLemVN
open NumberField Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.RankOne Formalism.MainNotions.BridgeLemVR
  Formalism.MainNotions.BridgeLemVC
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem Formalism.MainNotions.BridgeLemVN.fixF (K : Type) [Field K] [NumberField K] [StarRing K] :
    ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap (cmF K) K) := by sorry
