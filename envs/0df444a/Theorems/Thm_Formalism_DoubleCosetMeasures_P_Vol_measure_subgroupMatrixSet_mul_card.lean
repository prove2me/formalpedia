-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_Vol_measure_subgroupMatrixSet_mul_card
-- name    : Formalism.DoubleCosetMeasures.P.Vol.measure_subgroupMatrixSet_mul_card
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:51:47.057878+00:00
-- url     : https://prove2.me/theorems/52a8e36d-8ec9-4e90-831a-e9b1bf43ce4f
-- title:
--   Vol: measure subgroup Matrix Set mul card
-- statement:
--   The Vol construction uses the measure subgroup Matrix Set mul card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/MeasureUniformizerMatrixSetMulCard.lean#L272-L338
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/MeasureUniformizerMatrixSetMulCard.lean#L272-L338

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
variable [TopologicalSpace F] [IsTopologicalRing F] [MeasurableSpace F] [BorelSpace F]

theorem Formalism.DoubleCosetMeasures.P.Vol.measure_subgroupMatrixSet_mul_card (O : Subring F) (hO : IsOpen (O : Set F)) (ϖ : F) (hϖ : ϖ ∈ O)
    (hϖ0 : ϖ ≠ 0) (hloc : IsLocalAt O ϖ) [Finite (kF O ϖ hϖ)] (a : ℕ)
    (ν : Measure (Matrix (Fin a) (Fin a) F)) [ν.IsAddLeftInvariant]
    (J' : Subgroup (GL (Fin a) F)) (hK : congSub O ϖ a ≤ J') (hJ : J' ≤ GLint O a) :
    ν (Jset J') * (Nat.card (kF O ϖ hϖ) : ENNReal) ^ (a * a) =
      (Nat.card (J' ⧸ (congSub O ϖ a).subgroupOf J') : ENNReal) * ν (intMat O a a) := by sorry
