-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_GLRed_red_val
-- name    : Formalism.DoubleCosetMeasures.P.GLRed.red_val
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T00:43:57.381883+00:00
-- url     : https://prove2.me/theorems/b06f7445-1154-49fa-9204-1750e6b03cdc
-- title:
--   GLRed: red val
-- statement:
--   The GLRed construction uses the red val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/RelIndexMulMeasure.lean#L55-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/RelIndexMulMeasure.lean#L55-L58

import Definitions.Def_Formalism_DoubleCosetMeasures_StatementV
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_RelIndexMulMeasure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Set Pointwise
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P Formalism.DoubleCosetMeasures.P.GLRed
variable {F : Type} [Field F] (O : Subring F) {a : ℕ}
variable (a)
variable (ϖ : F) (hϖ : ϖ ∈ O)

theorem Formalism.DoubleCosetMeasures.P.GLRed.red_val (g : GLint O a) (i j : Fin a) :
    ((red O a ϖ hϖ g : GL (Fin a) (kF O ϖ hϖ)) : Matrix (Fin a) (Fin a) (kF O ϖ hϖ)) i j =
      Ideal.Quotient.mk _ ⟨((g : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) i j, g.2.1 i j⟩ := by sorry
