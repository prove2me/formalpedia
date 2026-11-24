-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_normRepCount_eq_eulerFac_inert
-- name    : Formalism.HermitianLattices.Ext.L3.normRepCount_eq_eulerFac_inert
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:56:04.697247+00:00
-- url     : https://prove2.me/theorems/f7f05173-ba71-487b-bbb9-d1bc330f8ea4
-- title:
--   L3: norm Rep Count eq euler Fac inert
-- statement:
--   The L3 construction uses the norm Rep Count eq euler Fac inert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/NormRepCountEqEulerFacInert.lean#L92-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/NormRepCountEqEulerFacInert.lean#L92-L97

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountSplitOne
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountPowSuccInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_EulerFacMulConjInvSplit
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountEqEulerFacInert
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem Formalism.HermitianLattices.Ext.L3.normRepCount_eq_eulerFac_inert (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {P : Ideal (𝓞 K)}
    (hP : P.IsMaximal) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P) (M k : ℕ) (hM : 1 ≤ M)
    (hk : 1 ≤ k) (n : 𝓞 K) (hn : conjO K n = n) (hnP : n ∉ P) :
    (normRepCount K (P ^ k) M n : ℝ) =
      Real.sqrt (Ideal.absNorm P : ℝ) ^ ((2 * M - 1) * k) * (Formalism.HermitianLatticesTheory.eulerFac K M P)⁻¹ := by sorry
