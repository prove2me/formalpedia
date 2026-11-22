-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S6x3_mem_eig
-- name    : Formalism.FourierDecayAlt.P.S6x3.mem_eig
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:42:05.41161+00:00
-- url     : https://prove2.me/theorems/90aaf847-7547-44bf-8f3e-80f3668c67e0
-- title:
--   S6x3: mem eig
-- statement:
--   The S6x3 construction uses the mem eig property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FinrankLeOfMapLe.lean#L116-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FinrankLeOfMapLe.lean#L116-L125

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

theorem Formalism.FourierDecayAlt.P.S6x3.mem_eig (A : FI E) (s : ℕ) (t : E) :
    t ∈ eig E A s ↔ t ∈ A ∧ t - (-1) ^ s * complexConj E t = 0 := by sorry
