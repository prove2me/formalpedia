-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_C2x7_UW_sub_S
-- name    : Formalism.FourierDecayAlt.P.C2x7.UW_sub_S
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T16:08:40.634516+00:00
-- url     : https://prove2.me/theorems/61361abe-5932-43f4-86c9-fe57f6595b6d
-- title:
--   C2x7: UW sub S
-- statement:
--   The C2x7 construction uses the UW sub S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LinearChangeOfVariablesBis.lean#L18-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LinearChangeOfVariablesBis.lean#L18-L19

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

theorem Formalism.FourierDecayAlt.P.C2x7.UW_sub_S {z : Fin (2 * r + k + 1) → ℂ} {h : B.Mat k r} (hh : h ∈ UWset k r z) : h ∈ Sset k r z := by sorry
