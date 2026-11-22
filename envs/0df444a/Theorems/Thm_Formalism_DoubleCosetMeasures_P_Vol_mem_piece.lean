-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_Vol_mem_piece
-- name    : Formalism.DoubleCosetMeasures.P.Vol.mem_piece
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:20:32.508589+00:00
-- url     : https://prove2.me/theorems/492c49d1-7bd7-46ab-a1c6-fdc18a60c49c
-- title:
--   Vol: mem piece
-- statement:
--   The Vol construction uses the mem piece property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/MeasureUniformizerMatrixSetMulCard.lean#L21-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/MeasureUniformizerMatrixSetMulCard.lean#L21-L24

import Definitions.Def_Formalism_DoubleCosetMeasures_StatementV
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MeasureUniformizerMatrixSetMulCard
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Matrix
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P Formalism.DoubleCosetMeasures.P.Vol
variable {F : Type} [Field F]

theorem Formalism.DoubleCosetMeasures.P.Vol.mem_piece {O : Subring F} {ϖ : F} {n a : ℕ} {r y : Matrix (Fin n) (Fin a) F} :
    y ∈ piece O ϖ r ↔ ∀ i j, ∃ o ∈ O, y i j - r i j = ϖ * o := by sorry
