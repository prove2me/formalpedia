-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormLifting_conjO_conjO
-- name    : Formalism.HermitianLattices.Ext.L3.NormLifting.conjO_conjO
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:47:12.618236+00:00
-- url     : https://prove2.me/theorems/12c27460-5e8a-41f6-9eb0-fc73b9246ae6
-- title:
--   Norm Lifting: conj O conj O
-- statement:
--   The Norm Lifting construction uses the conj O conj O property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/NormRepCountPowSuccInert.lean#L12-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/NormRepCountPowSuccInert.lean#L12-L16

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardFiberMulCardRange
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountPowSuccInert
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_conjO_conjO

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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.NormLifting
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem Formalism.HermitianLattices.Ext.L3.NormLifting.conjO_conjO (x : 𝓞 K) : conjO K (conjO K x) = x := by sorry
