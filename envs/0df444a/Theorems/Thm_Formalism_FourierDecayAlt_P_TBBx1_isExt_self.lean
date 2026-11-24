-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx1_isExt_self
-- name    : Formalism.FourierDecayAlt.P.TBBx1.isExt_self
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T17:55:59.612709+00:00
-- url     : https://prove2.me/theorems/c9e72f92-99ff-4cb1-9a6f-cac347b0ac01
-- title:
--   TBBx1: is Ext self
-- statement:
--   The TBBx1 construction uses the is Ext self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MinLeTruncatedExponential.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MinLeTruncatedExponential.lean#L17-L19

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

theorem Formalism.FourierDecayAlt.P.TBBx1.isExt_self {m : ℕ} {w : List C.Letter} (hw : AdmW P l0 Y w) (hl : w.length ≤ N) :
    IsExt P l0 Y N m w w := by sorry
