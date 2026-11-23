-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_Vol_mul_cong_mem_piece
-- name    : Formalism.DoubleCosetMeasures.P.Vol.mul_cong_mem_piece
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:51:36.499861+00:00
-- url     : https://prove2.me/theorems/34640bd4-9193-4897-bdc1-13977ace7447
-- title:
--   Vol: mul cong mem piece
-- statement:
--   The Vol construction uses the mul cong mem piece property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/MeasureUniformizerMatrixSetMulCard.lean#L120-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/MeasureUniformizerMatrixSetMulCard.lean#L120-L135

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

theorem Formalism.DoubleCosetMeasures.P.Vol.mul_cong_mem_piece (O : Subring F) (ϖ : F) (hϖ0 : ϖ ≠ 0) {a : ℕ} {g k : GL (Fin a) F}
    (hg : g ∈ GLint O a) (hk : k ∈ congSub O ϖ a) :
    (((g * k : GL (Fin a) F)) : Matrix (Fin a) (Fin a) F) ∈
      piece O ϖ (g : Matrix (Fin a) (Fin a) F) := by sorry
