-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormResidues_finite_quot
-- name    : Formalism.HermitianLattices.Ext.L3.NormResidues.finite_quot
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:46:37.866934+00:00
-- url     : https://prove2.me/theorems/5c05a71f-90b7-490f-8b1f-00d6131cc15e
-- title:
--   Norm Residues: finite quot
-- statement:
--   The Norm Residues construction uses the finite quot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/NormRepCountSplitOne.lean#L30-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/NormRepCountSplitOne.lean#L30-L37

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

theorem Formalism.HermitianLattices.Ext.L3.NormResidues.finite_quot {P : Ideal (𝓞 K)} (hP : P.IsMaximal) : Finite (𝓞 K ⧸ P) := by sorry
