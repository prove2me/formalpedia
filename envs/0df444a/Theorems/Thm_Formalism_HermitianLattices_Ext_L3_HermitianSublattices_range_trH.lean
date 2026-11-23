-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HermitianSublattices_range_trH
-- name    : Formalism.HermitianLattices.Ext.L3.HermitianSublattices.range_trH
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:06:45.559405+00:00
-- url     : https://prove2.me/theorems/c0cccb93-89ff-46c9-b858-e697e64dc60c
-- title:
--   Hermitian Sublattices: range tr H
-- statement:
--   The Hermitian Sublattices construction uses the range tr H property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardLiftMatrix.lean#L166-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardLiftMatrix.lean#L166-L189

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardFiberMulCardRange
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardLiftMatrix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HermitianSublattices
open Matrix
variable {A A' : Type*} [CommRing A] [StarRing A] [CommRing A'] [StarRing A']
variable {m r : Type*} [Fintype m] [Fintype r] [DecidableEq m] [DecidableEq r]

theorem Formalism.HermitianLattices.Ext.L3.HermitianSublattices.range_trH {J : Ideal A} (hJ : ∀ a ∈ J, star a ∈ J) {θ e : A}
    (he : (θ - star θ) * e = 1) : (trH r J).range = hermSub r J := by sorry
