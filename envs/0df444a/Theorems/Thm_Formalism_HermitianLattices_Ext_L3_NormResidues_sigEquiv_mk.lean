-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormResidues_sigEquiv_mk
-- name    : Formalism.HermitianLattices.Ext.L3.NormResidues.sigEquiv_mk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:13:00.374387+00:00
-- url     : https://prove2.me/theorems/52ee0e8d-c18b-4cdb-973b-73fdd1ba24df
-- title:
--   Norm Residues: sig Equiv mk
-- statement:
--   The Norm Residues construction uses the sig Equiv mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/NormRepCountSplitOne.lean#L60-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/NormRepCountSplitOne.lean#L60-L61

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
open Formalism.HermitianLattices.Ext.L3.NormResidues

theorem Formalism.HermitianLattices.Ext.L3.NormResidues.sigEquiv_mk (P : Ideal (𝓞 K)) (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P) (x : 𝓞 K) :
    sigEquiv P hc (Ideal.Quotient.mk P x) = Ideal.Quotient.mk P (conjO K x) := by sorry
