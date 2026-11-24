-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_normRepCount_inert_one
-- name    : Formalism.HermitianLattices.Ext.L3.normRepCount_inert_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:51.864016+00:00
-- url     : https://prove2.me/theorems/f60342fa-e9a7-4ae5-a34e-fb1654f9b50d
-- title:
--   L3: norm Rep Count inert one
-- statement:
--   The L3 construction uses the norm Rep Count inert one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/NormRepCountSplitOne.lean#L67-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/NormRepCountSplitOne.lean#L67-L103

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardSumNormFibres
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountSplitOne
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
open NormResidues

theorem Formalism.HermitianLattices.Ext.L3.normRepCount_inert_one (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {P : Ideal (𝓞 K)} (hP : P.IsMaximal)
    (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P) (M : ℕ) (hM : 1 ≤ M) (n : 𝓞 K) (hn : conjO K n = n)
    (hnP : n ∉ P) (q : ℕ) (hq : Ideal.absNorm P = q ^ 2) :
    (normRepCount K P M n : ℤ) = (q : ℤ) ^ (M - 1) * ((q : ℤ) ^ M - (-1) ^ M) := by sorry
