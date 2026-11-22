-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S6x3_mem_gA
-- name    : Formalism.FourierDecayAlt.P.S6x3.mem_gA
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:47:39.546793+00:00
-- url     : https://prove2.me/theorems/716f9349-4378-439b-bdd9-cc20281b2061
-- title:
--   S6x3: mem g A
-- statement:
--   The S6x3 construction uses the mem g A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FinrankLeOfMapLe.lean#L139-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FinrankLeOfMapLe.lean#L139-L141

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

theorem Formalism.FourierDecayAlt.P.S6x3.mem_gA (A : FI E) (g : ℕ) (x : E) :
    x ∈ A * FractionalIdeal.spanSingleton (𝓞 E)⁰ (g : E) ↔ ∃ a ∈ A, x = (g : E) * a := by sorry
