-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S6x5_finrank_eq
-- name    : Formalism.FourierDecayAlt.P.S6x5.finrank_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:20:13.649867+00:00
-- url     : https://prove2.me/theorems/48e6cdb6-ba08-4df4-8982-491adeb9b59b
-- title:
--   S6x5: finrank eq
-- statement:
--   The S6x5 construction uses the finrank eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TwistedIsRealOrderLattice.lean#L141-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TwistedIsRealOrderLattice.lean#L141-L146

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwistedIsRealOrderLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S6x5
open Formalism.FourierDecayAlt.S6
open NumberField NumberField.IsCMField Module MeasureTheory
open scoped nonZeroDivisors

theorem Formalism.FourierDecayAlt.P.S6x5.finrank_eq (E : Type) [Field E] [NumberField E] [IsCMField E] :
    finrank ℚ E = 2 * deg E := by sorry
