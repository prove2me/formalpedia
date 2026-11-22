-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormLifting_conjQ_mk
-- name    : Formalism.HermitianLattices.Ext.L3.NormLifting.conjQ_mk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:46:02.880412+00:00
-- url     : https://prove2.me/theorems/0f358e8c-ede2-4bd1-8860-be919a9ee2be
-- title:
--   Norm Lifting: conj Q mk
-- statement:
--   The Norm Lifting construction uses the conj Q mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/NormRepCountPowSuccInert.lean#L31-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/NormRepCountPowSuccInert.lean#L31-L36

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardFiberMulCardRange
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountPowSuccInert
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

theorem Formalism.HermitianLattices.Ext.L3.NormLifting.conjQ_mk (J : Ideal (𝓞 K)) (hJ : ∀ a ∈ J, conjO K a ∈ J) (a : 𝓞 K) :
    conjQ J hJ (Ideal.Quotient.mk J a) = Ideal.Quotient.mk J (conjO K a) := by sorry
