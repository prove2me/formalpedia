-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx1_admissible_word_of_extension
-- name    : Formalism.FourierDecayAlt.P.TBBx1.admissible_word_of_extension
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T17:55:51.713676+00:00
-- url     : https://prove2.me/theorems/84c1b673-8113-4f37-80f6-43166a85cbfe
-- title:
--   TBBx1: admissible word of extension
-- statement:
--   The TBBx1 construction uses the admissible word of extension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MinLeTruncatedExponential.lean#L21-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MinLeTruncatedExponential.lean#L21-L27

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

theorem Formalism.FourierDecayAlt.P.TBBx1.admissible_word_of_extension {m : ℕ} {w w' : List C.Letter} (hw : AdmW P l0 Y w) (h : IsExt P l0 Y N m w w') :
    AdmW P l0 Y w' := by sorry
