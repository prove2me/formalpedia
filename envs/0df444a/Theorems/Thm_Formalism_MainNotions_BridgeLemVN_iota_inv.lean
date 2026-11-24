-- Prove2me | Theorems.Thm_Formalism_MainNotions_BridgeLemVN_iota_inv
-- name    : Formalism.MainNotions.BridgeLemVN.iota_inv
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T09:55:38.528584+00:00
-- url     : https://prove2.me/theorems/1f279d97-cc05-4cd0-9eaa-50abb29ea23f
-- title:
--   Bridge Lem VN: iota inv
-- statement:
--   The Bridge Lem VN construction uses the iota inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/BridgeLemVN.lean#L30-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/BridgeLemVN.lean#L30-L31

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

theorem Formalism.MainNotions.BridgeLemVN.iota_inv (x : (𝓞 (cmF K))ˣ) : iota K x⁻¹ = (iota K x)⁻¹ := by sorry
