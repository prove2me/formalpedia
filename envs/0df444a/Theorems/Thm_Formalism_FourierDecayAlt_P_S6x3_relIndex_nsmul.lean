-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S6x3_relIndex_nsmul
-- name    : Formalism.FourierDecayAlt.P.S6x3.relIndex_nsmul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:20:22.709976+00:00
-- url     : https://prove2.me/theorems/d07d30a9-14eb-43b7-99fb-76fafeeb7280
-- title:
--   S6x3: rel Index nsmul
-- statement:
--   The S6x3 construction uses the rel Index nsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FinrankLeOfMapLe.lean#L211-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FinrankLeOfMapLe.lean#L211-L217

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

theorem Formalism.FourierDecayAlt.P.S6x3.relIndex_nsmul (N : Submodule ℤ E) [Module.Finite ℤ N] (g : ℕ) :
    (N.toAddSubgroup.map (nsmulAddMonoidHom (α := E) g)).relIndex N.toAddSubgroup
      = g ^ finrank ℤ N := by sorry
