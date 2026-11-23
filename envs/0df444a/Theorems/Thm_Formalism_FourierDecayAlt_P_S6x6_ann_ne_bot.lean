-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S6x6_ann_ne_bot
-- name    : Formalism.FourierDecayAlt.P.S6x6.ann_ne_bot
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:20:44.869096+00:00
-- url     : https://prove2.me/theorems/a1a9250e-7831-4489-a792-1c69933603e3
-- title:
--   S6x6: ann ne bot
-- statement:
--   The S6x6 construction uses the ann ne bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LocalisationTypedIndependentExponent.lean#L125-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LocalisationTypedIndependentExponent.lean#L125-L132

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationTypedIndependentExponent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S6x6
open NumberField NumberField.IsCMField Module Formalism.FourierDecayAlt.S6
open scoped nonZeroDivisors
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
variable {E}

theorem Formalism.FourierDecayAlt.P.S6x6.ann_ne_bot {L : Submodule ℤ E} (hL : IsFLattice E L) (t : E) : ann hL t ≠ ⊥ := by sorry
