-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormLifting_normRepCount_pow_succ_of
-- name    : Formalism.HermitianLattices.Ext.L3.NormLifting.normRepCount_pow_succ_of
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:13:04.923654+00:00
-- url     : https://prove2.me/theorems/6579ce83-0386-4102-81a4-d8bcc5cad057
-- title:
--   Norm Lifting: norm Rep Count pow succ of
-- statement:
--   The Norm Lifting construction uses the norm Rep Count pow succ of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/NormRepCountPowSuccInert.lean#L75-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/NormRepCountPowSuccInert.lean#L75-L112

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

theorem Formalism.HermitianLattices.Ext.L3.NormLifting.normRepCount_pow_succ_of {Q : Ideal (𝓞 K)} (hQ0 : Q ≠ ⊥) (hQ : Q.map (conjO K) = Q)
    (θ n : 𝓞 K) (hθ : IsCoprime (Ideal.span {θ - conjO K θ}) Q)
    (hnQ : IsCoprime (Ideal.span {n}) Q) (hn : conjO K n = n) (q : ℕ)
    (hq : Ideal.absNorm Q = q ^ 2) (M k : ℕ) (hM : 1 ≤ M) (hk : 1 ≤ k) :
    normRepCount K (Q ^ (k + 1)) M n = q ^ (2 * M - 1) * normRepCount K (Q ^ k) M n := by sorry
