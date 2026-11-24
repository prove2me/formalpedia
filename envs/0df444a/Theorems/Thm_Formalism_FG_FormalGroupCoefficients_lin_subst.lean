-- Prove2me | Theorems.Thm_Formalism_FG_FormalGroupCoefficients_lin_subst
-- name    : Formalism.FG.FormalGroupCoefficients.lin_subst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:37:14.468933+00:00
-- url     : https://prove2.me/theorems/c798359a-d62e-4f31-9e21-8d809475b247
-- title:
--   Formal Group Coefficients: lin subst
-- statement:
--   The Formal Group Coefficients construction uses the lin subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/GroupV.lean#L43-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/GroupV.lean#L43-L49

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

theorem Formalism.FG.FormalGroupCoefficients.lin_subst {σ τ : Type*} [Fintype σ] [Finite τ] {a : σ → MvPowerSeries τ R}
    (ha : ∀ j, constantCoeff (a j) = 0) (g : MvPowerSeries σ R) (i : τ) :
    coeff (Finsupp.single i 1) (g.subst a) =
      ∑ j, coeff (Finsupp.single j 1) g * coeff (Finsupp.single i 1) (a j) := by sorry
