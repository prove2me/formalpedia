-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_C2x7_fix_inv
-- name    : Formalism.FourierDecayAlt.P.C2x7.fix_inv
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T16:12:48.869897+00:00
-- url     : https://prove2.me/theorems/a880a9ed-d686-4407-9c54-fcaffb6f54a3
-- title:
--   C2x7: fix inv
-- statement:
--   The C2x7 construction uses the fix inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LinearChangeOfVariablesBis.lean#L21-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LinearChangeOfVariablesBis.lean#L21-L26

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

theorem Formalism.FourierDecayAlt.P.C2x7.fix_inv {z : Fin (2 * r + k + 1) → ℂ} {g : B.Mat k r} (hg : g ∈ C2.FixSet k r z) :
    g⁻¹ ∈ C2.FixSet k r z := by sorry
