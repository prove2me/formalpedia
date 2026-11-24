-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormResidues_norm_cond_iff
-- name    : Formalism.HermitianLattices.Ext.L3.NormResidues.norm_cond_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:49:22.718797+00:00
-- url     : https://prove2.me/theorems/bc80c162-b78b-45b7-8d74-600140046cf6
-- title:
--   Norm Residues: norm cond iff
-- statement:
--   The Norm Residues construction uses the norm cond iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/NormRepCountSplitOne.lean#L188-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/NormRepCountSplitOne.lean#L188-L196

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
open Formalism.HermitianLattices.Ext.L3.NormResidues

theorem Formalism.HermitianLattices.Ext.L3.NormResidues.norm_cond_iff {P : Ideal (𝓞 K)} (hP : P.IsMaximal) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≠ P)
    (M : ℕ) (n : 𝓞 K) (hn : conjO K n = n) (y : Fin M → 𝓞 K) :
    Ideal.Quotient.mk (P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) (∑ i, conjO K (y i) * y i) =
        Ideal.Quotient.mk (P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P) n ↔
      ∑ i, Ideal.Quotient.mk P (conjO K (y i)) * Ideal.Quotient.mk P (y i) =
        Ideal.Quotient.mk P n := by sorry
