-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_GLRed_mem_span_iff
-- name    : Formalism.DoubleCosetMeasures.P.GLRed.mem_span_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:50:18.587618+00:00
-- url     : https://prove2.me/theorems/440c67d4-c9b5-4c80-b999-826778b2ab8c
-- title:
--   GLRed: mem span iff
-- statement:
--   The GLRed construction uses the mem span iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/RelIndexMulMeasure.lean#L62-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/RelIndexMulMeasure.lean#L62-L72

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

theorem Formalism.DoubleCosetMeasures.P.GLRed.mem_span_iff (hϖ0 : ϖ ≠ 0) (x : O) :
    x ∈ Ideal.span {(⟨ϖ, hϖ⟩ : O)} ↔ ϖ⁻¹ * (x : F) ∈ O := by sorry
