-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Jx3_idl_zero_eq
-- name    : Formalism.FourierDecayAlt.P.Jx3.idl_zero_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:47:47.731298+00:00
-- url     : https://prove2.me/theorems/871eabf5-5389-424a-8a8e-841c39ceb71c
-- title:
--   Jx3: idl zero eq
-- statement:
--   The Jx3 construction uses the idl zero eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DualCovolumeChangeOfVariables.lean#L197-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DualCovolumeChangeOfVariables.lean#L197-L203

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Lemmata_FiberEquations_FiberEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualCovolumeChangeOfVariables
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J Module
open scoped ComplexConjugate nonZeroDivisors
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx3

theorem Formalism.FourierDecayAlt.P.Jx3.idl_zero_eq (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (ν : ℤ) (hg : 0 < g) :
    S6.idl E g 0 (-(ν + 1)) = S6.dualIdl E g ν * FractionalIdeal.spanSingleton _ (g : E) := by sorry
