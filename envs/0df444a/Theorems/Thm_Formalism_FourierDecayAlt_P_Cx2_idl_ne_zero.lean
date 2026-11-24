-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Cx2_idl_ne_zero
-- name    : Formalism.FourierDecayAlt.P.Cx2.idl_ne_zero
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T15:26:37.076928+00:00
-- url     : https://prove2.me/theorems/0519c771-2c86-4859-a8db-b56d37b2d09a
-- title:
--   Cx2: idl ne zero
-- statement:
--   The Cx2 construction uses the idl ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstNormRealNonneg.lean#L19-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstNormRealNonneg.lean#L19-L26

import Definitions.Def_Formalism_HermitianCurvature_StatementC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelZeroEstimateProduct
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PeriodLatticeFactsSplitOfGeneral
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationScaledIdealMemIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwistedIsRealOrderLattice
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstNormRealNonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_idl_ne_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x2_idl_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset Filter Topology Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C NumberField MeasureTheory
open scoped ComplexOrder ComplexConjugate RealInnerProductSpace
noncomputable section
open Formalism.FourierDecayAlt.P.Cx2
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem Formalism.FourierDecayAlt.P.Cx2.idl_ne_zero (g : ℕ) (hg : 0 < g) (k ν : ℤ) : S6.idl E g k ν ≠ 0 := by sorry
