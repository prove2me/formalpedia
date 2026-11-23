-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_GLRed_nontriv
-- name    : Formalism.DoubleCosetMeasures.P.GLRed.nontriv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:22.645883+00:00
-- url     : https://prove2.me/theorems/13da91b7-e060-4032-a885-4d5781cf78dd
-- title:
--   GLRed: nontriv
-- statement:
--   The GLRed construction uses the nontriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/RelIndexMulMeasure.lean#L101-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/RelIndexMulMeasure.lean#L101-L107

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

theorem Formalism.DoubleCosetMeasures.P.GLRed.nontriv (hloc : IsLocalAt O ϖ) : Nontrivial (kF O ϖ hϖ) := by sorry
