-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_GLRed_ker_red
-- name    : Formalism.DoubleCosetMeasures.P.GLRed.ker_red
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:56:16.282746+00:00
-- url     : https://prove2.me/theorems/d7a5b2db-474c-4bd0-b84a-aff338c3214f
-- title:
--   GLRed: ker red
-- statement:
--   The GLRed construction uses the ker red property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/RelIndexMulMeasure.lean#L82-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/RelIndexMulMeasure.lean#L82-L99

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
variable {a}

theorem Formalism.DoubleCosetMeasures.P.GLRed.ker_red (hϖ0 : ϖ ≠ 0) :
    (red O a ϖ hϖ).ker = (congSub O ϖ a).subgroupOf (GLint O a) := by sorry
