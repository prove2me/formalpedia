-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormLifting_stable_pow
-- name    : Formalism.HermitianLattices.Ext.L3.NormLifting.stable_pow
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:52:45.316253+00:00
-- url     : https://prove2.me/theorems/5dce6906-717a-42cb-8c4a-f5e288e1df2c
-- title:
--   Norm Lifting: stable pow
-- statement:
--   The Norm Lifting construction uses the stable pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/NormRepCountPowSuccInert.lean#L69-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/NormRepCountPowSuccInert.lean#L69-L73

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

theorem Formalism.HermitianLattices.Ext.L3.NormLifting.stable_pow {Q : Ideal (𝓞 K)} (hQ : Q.map (conjO K) = Q) (k : ℕ) :
    ∀ a ∈ Q ^ k, conjO K a ∈ Q ^ k := by sorry
