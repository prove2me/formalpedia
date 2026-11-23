-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S6x3_gA_eq_map
-- name    : Formalism.FourierDecayAlt.P.S6x3.gA_eq_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:20:22.0233+00:00
-- url     : https://prove2.me/theorems/b7fdd5bc-b267-4c8e-84d8-11d4c9261a33
-- title:
--   S6x3: g A eq map
-- statement:
--   The S6x3 construction uses the g A eq map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FinrankLeOfMapLe.lean#L326-L336
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FinrankLeOfMapLe.lean#L326-L336

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

theorem Formalism.FourierDecayAlt.P.S6x3.gA_eq_map (A : FI E) (g : ℕ) :
    (zsub E (A * FractionalIdeal.spanSingleton _ (g : E))).toAddSubgroup
      = (zsub E A).toAddSubgroup.map (nsmulAddMonoidHom (α := E) g) := by sorry
