-- Prove2me | Theorems.Thm_Formalism_MainNotions_BridgeLemVN_span_mul_span1
-- name    : Formalism.MainNotions.BridgeLemVN.span_mul_span1
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T09:56:18.646282+00:00
-- url     : https://prove2.me/theorems/ec3f7421-efce-448e-8ca6-8665bbbfc7a6
-- title:
--   Bridge Lem VN: span mul span1
-- statement:
--   The Bridge Lem VN construction uses the span mul span1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/BridgeLemVN.lean#L26-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/BridgeLemVN.lean#L26-L28

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

theorem Formalism.MainNotions.BridgeLemVN.span_mul_span1 (x y : K) :
    Submodule.span (𝓞 K) {x} * Submodule.span (𝓞 K) {y} = Submodule.span (𝓞 K) {x * y} := by sorry
