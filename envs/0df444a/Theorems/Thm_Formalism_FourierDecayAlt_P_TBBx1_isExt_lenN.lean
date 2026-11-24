-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx1_isExt_lenN
-- name    : Formalism.FourierDecayAlt.P.TBBx1.isExt_lenN
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T17:57:51.867655+00:00
-- url     : https://prove2.me/theorems/41e20c9e-16bb-4478-8dd5-f0879bfd244e
-- title:
--   TBBx1: is Ext len N
-- statement:
--   The TBBx1 construction uses the is Ext len N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MinLeTruncatedExponential.lean#L34-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MinLeTruncatedExponential.lean#L34-L34

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

theorem Formalism.FourierDecayAlt.P.TBBx1.isExt_lenN {m : ℕ} {w w' : List C.Letter} (h : IsExt P l0 Y N m w w') : w'.length ≤ N := by sorry
