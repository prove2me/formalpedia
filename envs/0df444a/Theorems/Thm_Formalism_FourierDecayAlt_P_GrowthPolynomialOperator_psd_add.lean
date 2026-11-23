-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_GrowthPolynomialOperator_psd_add
-- name    : Formalism.FourierDecayAlt.P.GrowthPolynomialOperator.psd_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:08:38.827592+00:00
-- url     : https://prove2.me/theorems/1f2b169f-90c0-4611-be24-10855f35538a
-- title:
--   Growth Polynomial Operator: psd add
-- statement:
--   The Growth Polynomial Operator construction uses the psd add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GrowthOfBasic.lean#L803-L811
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GrowthOfBasic.lean#L803-L811

import Definitions.Def_Formalism_HermitianCurvature_StatementPB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PullLatticeTypedUnit
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PeriodLatticeFactsSplitOfGeneral
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationScaledIdealMemIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwistedIsRealOrderLattice
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GrowthOfBasic
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_psd_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx9_psd_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GrowthPolynomialOperator
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PB
open scoped ComplexOrder ComplexConjugate
open Classical

theorem Formalism.FourierDecayAlt.P.GrowthPolynomialOperator.psd_add {α : Type} {Y : Finset α} {k k' : α → α → ℂ}
    (hk : TB.PSDOn Y k) (hk' : TB.PSDOn Y k') : TB.PSDOn Y (fun x y => k x y + k' x y) := by sorry
