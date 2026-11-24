-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx1_exists_max_ext
-- name    : Formalism.FourierDecayAlt.P.TBBx1.exists_max_ext
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T17:55:29.682023+00:00
-- url     : https://prove2.me/theorems/07008ecb-44e2-4aaf-8ffc-9e698ecbd0e2
-- title:
--   TBBx1: exists max ext
-- statement:
--   The TBBx1 construction uses the exists max ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MinLeTruncatedExponential.lean#L66-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MinLeTruncatedExponential.lean#L66-L69

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

theorem Formalism.FourierDecayAlt.P.TBBx1.exists_max_ext (m : ℕ) (w : List C.Letter) (f : List C.Letter → ℝ) (hw : IsExt P l0 Y N m w w) :
    ∃ w', IsExt P l0 Y N m w w' ∧ ∀ w'', IsExt P l0 Y N m w w'' → f w'' ≤ f w' := by sorry
