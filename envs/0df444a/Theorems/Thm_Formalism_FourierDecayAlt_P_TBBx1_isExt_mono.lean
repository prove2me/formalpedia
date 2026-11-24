-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx1_isExt_mono
-- name    : Formalism.FourierDecayAlt.P.TBBx1.isExt_mono
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T17:56:35.263179+00:00
-- url     : https://prove2.me/theorems/4ed7c3fa-3f50-4557-bf85-e83914c9b3fd
-- title:
--   TBBx1: is Ext mono
-- statement:
--   The TBBx1 construction uses the is Ext mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MinLeTruncatedExponential.lean#L45-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MinLeTruncatedExponential.lean#L45-L48

import Definitions.Def_Formalism_HermitianCurvature_StatementTBB
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegrableOnIoiTruncatedPowerMoment
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MinLeTruncatedExponential
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TBBx1
open Finset Filter Topology MeasureTheory Real
open Formalism.FourierDecayAlt.TBB
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
variable {P : M.Par} {l0 : ℕ} {Y : Finset ℝ} {N : ℕ}

theorem Formalism.FourierDecayAlt.P.TBBx1.isExt_mono {m m' : ℕ} {w w' : List C.Letter} (h : IsExt P l0 Y N m w w') (hm : m ≤ m') :
    IsExt P l0 Y N m' w w' := by sorry
