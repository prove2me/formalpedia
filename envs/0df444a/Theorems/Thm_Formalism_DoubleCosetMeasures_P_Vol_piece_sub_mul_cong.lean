-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_Vol_piece_sub_mul_cong
-- name    : Formalism.DoubleCosetMeasures.P.Vol.piece_sub_mul_cong
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:54:33.357931+00:00
-- url     : https://prove2.me/theorems/832dda1b-ce5a-4d11-a97c-3b7cc157bd79
-- title:
--   Vol: piece sub mul cong
-- statement:
--   The Vol construction uses the piece sub mul cong property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/MeasureUniformizerMatrixSetMulCard.lean#L137-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/MeasureUniformizerMatrixSetMulCard.lean#L137-L151

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

theorem Formalism.DoubleCosetMeasures.P.Vol.piece_sub_mul_cong (O : Subring F) (ϖ : F) (hϖ : ϖ ∈ O) (hϖ0 : ϖ ≠ 0)
    (hloc : IsLocalAt O ϖ) {a : ℕ} {g : GL (Fin a) F} (hg : g ∈ GLint O a)
    {m : Matrix (Fin a) (Fin a) F} (hm : m ∈ piece O ϖ (g : Matrix (Fin a) (Fin a) F)) :
    ∃ k ∈ congSub O ϖ a, (((g * k : GL (Fin a) F)) : Matrix (Fin a) (Fin a) F) = m := by sorry
