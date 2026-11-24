-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_C2x7_one_mem_UW
-- name    : Formalism.FourierDecayAlt.P.C2x7.one_mem_UW
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T16:08:37.614486+00:00
-- url     : https://prove2.me/theorems/7e93c5c6-0285-4a1c-9953-b22a9eee71c4
-- title:
--   C2x7: one mem UW
-- statement:
--   The C2x7 construction uses the one mem UW property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LinearChangeOfVariablesBis.lean#L12-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LinearChangeOfVariablesBis.lean#L12-L13

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MajorantEstimate
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LinearChangeOfVariablesBis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants MeasureTheory
open scoped ComplexConjugate ENNReal
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.C2x7
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.C2x7.one_mem_UW (z : Fin (2 * r + k + 1) → ℂ) : (1 : B.Mat k r) ∈ UWset k r z := by sorry
