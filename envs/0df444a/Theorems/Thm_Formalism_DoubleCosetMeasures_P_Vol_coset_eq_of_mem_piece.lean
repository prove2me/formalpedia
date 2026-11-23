-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_Vol_coset_eq_of_mem_piece
-- name    : Formalism.DoubleCosetMeasures.P.Vol.coset_eq_of_mem_piece
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:51:53.050806+00:00
-- url     : https://prove2.me/theorems/40ee60e3-10ba-46e7-bf2d-add0dfca2a3f
-- title:
--   Vol: coset eq of mem piece
-- statement:
--   The Vol construction uses the coset eq of mem piece property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/MeasureUniformizerMatrixSetMulCard.lean#L257-L268
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/MeasureUniformizerMatrixSetMulCard.lean#L257-L268

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

theorem Formalism.DoubleCosetMeasures.P.Vol.coset_eq_of_mem_piece (O : Subring F) (ϖ : F) (hϖ : ϖ ∈ O) (hϖ0 : ϖ ≠ 0)
    (hloc : IsLocalAt O ϖ) {a : ℕ} {J' : Subgroup (GL (Fin a) F)} (hJ : J' ≤ GLint O a)
    (u v : J')
    (h : ((v : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) ∈
      piece O ϖ ((u : GL (Fin a) F) : Matrix (Fin a) (Fin a) F)) :
    (u : J' ⧸ (congSub O ϖ a).subgroupOf J') = (v : J' ⧸ (congSub O ϖ a).subgroupOf J') := by sorry
