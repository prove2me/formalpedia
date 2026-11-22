-- Prove2me | Theorems.Thm_Formalism_FG_FormalGroupCoefficients_inj
-- name    : Formalism.FG.FormalGroupCoefficients.inj
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T21:53:08.137305+00:00
-- url     : https://prove2.me/theorems/d36eb3e5-1694-47f1-b465-7633f0fb4987
-- title:
--   Formal Group Coefficients: inj
-- statement:
--   The Formal Group Coefficients construction uses the inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/GroupV.lean#L63-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/GroupV.lean#L63-L66

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

theorem Formalism.FG.FormalGroupCoefficients.inj {f : ι → MvPowerSeries ι R} (hf : IsIdMod2 f) {τ : Type v} [Finite τ]
    {a b : ι → MvPowerSeries τ R} (ha : ∀ i, constantCoeff (a i) = 0)
    (hb : ∀ i, constantCoeff (b i) = 0) (h : ∀ j, subst a (f j) = subst b (f j)) : a = b := by sorry
