-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S6x3_tw_eq
-- name    : Formalism.FourierDecayAlt.P.S6x3.tw_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:20:25.729931+00:00
-- url     : https://prove2.me/theorems/1c12a3e2-8234-4244-a9af-9c61da71c1c7
-- title:
--   S6x3: tw eq
-- statement:
--   The S6x3 construction uses the tw eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FinrankLeOfMapLe.lean#L149-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FinrankLeOfMapLe.lean#L149-L185

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FinrankLeOfMapLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S6x3
open Formalism.FourierDecayAlt.S6
open NumberField NumberField.IsCMField Module
open scoped nonZeroDivisors
variable (E : Type) [Field E] [NumberField E] [IsCMField E]

theorem Formalism.FourierDecayAlt.P.S6x3.tw_eq (A : FI E) (g s : ℕ) (hA : ConjStable E A) (hg : 0 < g) (hU : UnramAbove E g) :
    twLat E A (A * FractionalIdeal.spanSingleton _ (g : E)) s
      = eig E A s ⊔ zsub E (A * FractionalIdeal.spanSingleton _ (g : E)) := by sorry
