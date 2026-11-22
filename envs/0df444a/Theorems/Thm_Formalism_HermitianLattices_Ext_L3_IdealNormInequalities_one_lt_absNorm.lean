-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_IdealNormInequalities_one_lt_absNorm
-- name    : Formalism.HermitianLattices.Ext.L3.IdealNormInequalities.one_lt_absNorm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:33:09.984633+00:00
-- url     : https://prove2.me/theorems/86e52c6c-7703-47ce-b499-f504d5450bfc
-- title:
--   Ideal Norm Inequalities: one lt abs Norm
-- statement:
--   The Ideal Norm Inequalities construction uses the one lt abs Norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/EulerFacMulConjInvSplit.lean#L28-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/EulerFacMulConjInvSplit.lean#L28-L29

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardFilterResCharLe
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_EulerFacMulConjInvSplit
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
open Formalism.HermitianLattices.Ext.L3.IdealNormInequalities

theorem Formalism.HermitianLattices.Ext.L3.IdealNormInequalities.one_lt_absNorm {P : Ideal (𝓞 K)} (hP : P.IsMaximal) : (1 : ℝ) < (Ideal.absNorm P : ℝ) := by sorry
