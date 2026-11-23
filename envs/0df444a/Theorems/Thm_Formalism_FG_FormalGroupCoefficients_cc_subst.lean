-- Prove2me | Theorems.Thm_Formalism_FG_FormalGroupCoefficients_cc_subst
-- name    : Formalism.FG.FormalGroupCoefficients.cc_subst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:37:06.850925+00:00
-- url     : https://prove2.me/theorems/2d6f751b-6f2a-4865-8a43-b499551979fa
-- title:
--   Formal Group Coefficients: cc subst
-- statement:
--   The Formal Group Coefficients construction uses the cc subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/GroupV.lean#L22-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/GroupV.lean#L22-L25

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

theorem Formalism.FG.FormalGroupCoefficients.cc_subst {σ τ : Type*} [Finite σ] {a : σ → MvPowerSeries τ R}
    (ha : ∀ i, constantCoeff (a i) = 0) {g : MvPowerSeries σ R} (hg : constantCoeff g = 0) :
    constantCoeff (subst a g) = 0 := by sorry
