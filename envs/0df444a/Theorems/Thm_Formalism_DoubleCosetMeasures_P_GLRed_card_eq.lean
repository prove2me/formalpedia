-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_GLRed_card_eq
-- name    : Formalism.DoubleCosetMeasures.P.GLRed.card_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:43:36.024188+00:00
-- url     : https://prove2.me/theorems/5aebfcb0-95d7-4f75-b17c-e8975226c016
-- title:
--   GLRed: card eq
-- statement:
--   The GLRed construction uses the card eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/RelIndexMulMeasure.lean#L143-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/RelIndexMulMeasure.lean#L143-L147

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
variable (a)

theorem Formalism.DoubleCosetMeasures.P.GLRed.card_eq (hϖ0 : ϖ ≠ 0) (hloc : IsLocalAt O ϖ) :
    Nat.card ((GLint O a) ⧸ (congSub O ϖ a).subgroupOf (GLint O a)) =
      Nat.card (GL (Fin a) (kF O ϖ hϖ)) := by sorry
