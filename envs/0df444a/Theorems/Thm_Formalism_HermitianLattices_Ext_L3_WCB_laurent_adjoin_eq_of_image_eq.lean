-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCB_laurent_adjoin_eq_of_image_eq
-- name    : Formalism.HermitianLattices.Ext.L3.WCB.laurent_adjoin_eq_of_image_eq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T09:48:29.748599+00:00
-- url     : https://prove2.me/theorems/c93f2503-21c6-4061-857c-8ab5e22a7b20
-- title:
--   WCB: laurent adjoin eq of image eq
-- statement:
--   The WCB construction uses the laurent adjoin eq of image eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/LaurentAdjoinEqOfImageEq.lean#L29-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/LaurentAdjoinEqOfImageEq.lean#L29-L42

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

theorem Formalism.HermitianLattices.Ext.L3.WCB.laurent_adjoin_eq_of_image_eq {h : V →ₗ⋆[K] V →ₗ[K] K} (han : ∀ x, h x x = 0 → x = 0) {Y : V →ₗ[K] V}
    (hY : ∀ a b, h (Y a) b + h a (Y b) = 0) {l m : K} (hm : star m = l) (hl : l + m = 1) {z : V}
    (hz : z = m • Y z) : z = 0 := by sorry
