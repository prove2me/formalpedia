-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_Vol_iiset_eq
-- name    : Formalism.DoubleCosetMeasures.P.Vol.iiset_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:51:55.533729+00:00
-- url     : https://prove2.me/theorems/1aa00641-51dc-40a6-862c-dc3b4b65824e
-- title:
--   Vol: iiset eq
-- statement:
--   The Vol construction uses the iiset eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/MeasureUniformizerMatrixSetMulCard.lean#L26-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/MeasureUniformizerMatrixSetMulCard.lean#L26-L34

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

theorem Formalism.DoubleCosetMeasures.P.Vol.iiset_eq (O : Subring F) (ϖ : F) (hϖ0 : ϖ ≠ 0) {n a : ℕ} :
    (IIset O ϖ : Set (Matrix (Fin n) (Fin a) F)) = {y | ∀ i j, ϖ⁻¹ * y i j ∈ O} := by sorry
