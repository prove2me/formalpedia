-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormResidues_conjO_sum_norm
-- name    : Formalism.HermitianLattices.Ext.L3.NormResidues.conjO_sum_norm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:50:12.059881+00:00
-- url     : https://prove2.me/theorems/f814df5c-1b21-484c-8875-03d2fc75d428
-- title:
--   Norm Residues: conj O sum norm
-- statement:
--   The Norm Residues construction uses the conj O sum norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/NormRepCountSplitOne.lean#L24-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/NormRepCountSplitOne.lean#L24-L28

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

theorem Formalism.HermitianLattices.Ext.L3.NormResidues.conjO_sum_norm {M : ℕ} (y : Fin M → 𝓞 K) :
    conjO K (∑ i, conjO K (y i) * y i) = ∑ i, conjO K (y i) * y i := by sorry
