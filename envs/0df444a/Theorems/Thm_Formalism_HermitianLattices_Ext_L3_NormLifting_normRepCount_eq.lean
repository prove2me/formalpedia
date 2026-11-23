-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormLifting_normRepCount_eq
-- name    : Formalism.HermitianLattices.Ext.L3.NormLifting.normRepCount_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:13:32.696278+00:00
-- url     : https://prove2.me/theorems/673d1ed2-f60d-4858-95ce-e394bf3f548a
-- title:
--   Norm Lifting: norm Rep Count eq
-- statement:
--   The Norm Lifting construction uses the norm Rep Count eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/NormRepCountPowSuccInert.lean#L38-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/NormRepCountPowSuccInert.lean#L38-L57

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

theorem Formalism.HermitianLattices.Ext.L3.NormLifting.normRepCount_eq (J : Ideal (𝓞 K)) (hJ : ∀ a ∈ J, conjO K a ∈ J) (M : ℕ) (n : 𝓞 K) :
    normRepCount K J M n =
      Nat.card {x : Fin M → 𝓞 K ⧸ J // ∑ i, conjQ J hJ (x i) * x i = Ideal.Quotient.mk J n} := by sorry
