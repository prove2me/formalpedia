-- Prove2me | Theorems.Thm_Formalism_FG_FormalGroupCoefficients_cc_pderiv
-- name    : Formalism.FG.FormalGroupCoefficients.cc_pderiv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:37:10.395805+00:00
-- url     : https://prove2.me/theorems/4258bd9a-88b1-47b1-8bef-8a9c089a9189
-- title:
--   Formal Group Coefficients: cc pderiv
-- statement:
--   The Formal Group Coefficients construction uses the cc pderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/GroupV.lean#L29-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/GroupV.lean#L29-L32

import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FunctionalEquationHomVector
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_EqSingleOfDegreeEqOne
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_GroupV
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v
open Formalism Formalism.FG Formalism.FG.FormalGroupCoefficients
open MvPowerSeries Formalism.G Formalism.LT
variable {R : Type u} [CommRing R]

theorem Formalism.FG.FormalGroupCoefficients.cc_pderiv {σ : Type*} (g : MvPowerSeries σ R) (i : σ) :
    constantCoeff (pderiv R i g) = coeff (Finsupp.single i 1) g := by sorry
