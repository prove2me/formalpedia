-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S6x3_inf_eq_map
-- name    : Formalism.FourierDecayAlt.P.S6x3.inf_eq_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:20:33.81967+00:00
-- url     : https://prove2.me/theorems/b024dc06-5b8a-405b-82ce-e333e743f671
-- title:
--   S6x3: inf eq map
-- statement:
--   The S6x3 construction uses the inf eq map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FinrankLeOfMapLe.lean#L338-L360
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FinrankLeOfMapLe.lean#L338-L360

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

theorem Formalism.FourierDecayAlt.P.S6x3.inf_eq_map (A : FI E) (g s : ℕ) (hg : 0 < g) :
    (zsub E (A * FractionalIdeal.spanSingleton _ (g : E))).toAddSubgroup ⊓
        (eig E A s).toAddSubgroup
      = (eig E A s).toAddSubgroup.map (nsmulAddMonoidHom (α := E) g) := by sorry
