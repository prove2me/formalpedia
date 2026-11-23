-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S6x3_finrank_le_of_map_le
-- name    : Formalism.FourierDecayAlt.P.S6x3.finrank_le_of_map_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:28:06.216507+00:00
-- url     : https://prove2.me/theorems/4952238d-e199-49e0-8784-2e39899c1156
-- title:
--   S6x3: finrank le of map le
-- statement:
--   The S6x3 construction uses the finrank le of map le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FinrankLeOfMapLe.lean#L206-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FinrankLeOfMapLe.lean#L206-L209

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

theorem Formalism.FourierDecayAlt.P.S6x3.finrank_le_of_map_le (f : E →ₗ[ℤ] E) (hf : Function.Injective f) (N N' : Submodule ℤ E)
    [Module.Finite ℤ N'] (h : N.map f ≤ N') : finrank ℤ N ≤ finrank ℤ N' := by sorry
