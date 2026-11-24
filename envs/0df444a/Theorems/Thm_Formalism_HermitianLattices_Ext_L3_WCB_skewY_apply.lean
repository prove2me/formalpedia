-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCB_skewY_apply
-- name    : Formalism.HermitianLattices.Ext.L3.WCB.skewY_apply
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T09:29:26.539724+00:00
-- url     : https://prove2.me/theorems/25f9a43d-d93d-49b7-b95e-39654c868c03
-- title:
--   WCB: skew Y apply
-- statement:
--   The WCB construction uses the skew Y apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/LaurentAdjoinEqOfImageEq.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/LaurentAdjoinEqOfImageEq.lean#L16-L18

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_InLZeroIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LaurentAdjoinEqOfImageEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.WCB
variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]

theorem Formalism.HermitianLattices.Ext.L3.WCB.skewY_apply (h : V →ₗ⋆[K] V →ₗ[K] K) (u w : V) (θ : K) (z : V) :
    skewY h u w θ z = (θ * h u z - h w z) • u + h u z • w := by sorry
