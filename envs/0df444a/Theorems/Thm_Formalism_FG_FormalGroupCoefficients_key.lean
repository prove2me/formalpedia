-- Prove2me | Theorems.Thm_Formalism_FG_FormalGroupCoefficients_key
-- name    : Formalism.FG.FormalGroupCoefficients.key
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T21:20:42.702532+00:00
-- url     : https://prove2.me/theorems/ed1e366c-8f8a-4939-833a-e76e681a4ace
-- title:
--   Formal Group Coefficients: key
-- statement:
--   The Formal Group Coefficients construction uses the key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/GroupV.lean#L70-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/GroupV.lean#L70-L77

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
variable {R : Type u} [CommRing R] {ι : Type v} [Fintype ι] [DecidableEq ι]
variable {f : ι → MvPowerSeries ι R} {F : ι → MvPowerSeries (Fin 2 × ι) R}

theorem Formalism.FG.FormalGroupCoefficients.key (hF0 : ∀ i, constantCoeff (F i) = 0)
    (hFG : ∀ j, subst F (f j) = atXv (f j) + atYv (f j)) {τ : Type*}
    (b : Fin 2 × ι → MvPowerSeries τ R) (hb : ∀ x, constantCoeff (b x) = 0) (j : ι) :
    subst (fun i => subst b (F i)) (f j) =
      subst (fun i => b ((0 : Fin 2), i)) (f j) + subst (fun i => b ((1 : Fin 2), i)) (f j) := by sorry
