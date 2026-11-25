-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_En_wq_pos
-- name    : Formalism.FourierDecayAlt.P.CutMP.En.wq_pos
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:12:54.07922+00:00
-- url     : https://prove2.me/theorems/794cc0ff-0cc8-522b-80a8-3f38573063b4
-- title:
--   En: wq pos
-- statement:
--   The En construction uses the wq pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutEnTrSmooth.lean#L36-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutEnTrSmooth.lean#L36-L43

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutEnFibMem
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellOpenDomain
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NFRadRedLocSec
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointLeibnizExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutEnTrSmooth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt MeasureTheory
open Formalism.REAL Formalism.QuantumDeterminants
open NumberField
open scoped ContDiff
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.En
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem Formalism.FourierDecayAlt.P.CutMP.En.wq_pos {k r : ℕ} {TT : ℝ} {x : MA.E r} (hx : x ∈ MA.Qset r TT) : 0 < MA.wq k x TT := by sorry
