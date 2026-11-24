-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_IdealNormInequalities_one_lt_sqrt_absNorm
-- name    : Formalism.HermitianLattices.Ext.L3.IdealNormInequalities.one_lt_sqrt_absNorm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:49:10.953634+00:00
-- url     : https://prove2.me/theorems/b89a94d7-075d-4276-ac76-b7cd3f534233
-- title:
--   Ideal Norm Inequalities: one lt sqrt abs Norm
-- statement:
--   The Ideal Norm Inequalities construction uses the one lt sqrt abs Norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/EulerFacMulConjInvSplit.lean#L31-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/EulerFacMulConjInvSplit.lean#L31-L34

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

theorem Formalism.HermitianLattices.Ext.L3.IdealNormInequalities.one_lt_sqrt_absNorm {P : Ideal (𝓞 K)} (hP : P.IsMaximal) :
    (1 : ℝ) < Real.sqrt (Ideal.absNorm P : ℝ) := by sorry
