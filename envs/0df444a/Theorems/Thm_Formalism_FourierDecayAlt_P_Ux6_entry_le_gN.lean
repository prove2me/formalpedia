-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_entry_le_gN
-- name    : Formalism.FourierDecayAlt.P.Ux6.entry_le_gN
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T14:50:39.575165+00:00
-- url     : https://prove2.me/theorems/92d89b77-5bb1-4fdd-9739-4329f706f9a1
-- title:
--   Ux6: entry le g N
-- statement:
--   The Ux6 construction uses the entry le g N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CoordinateSizesOfHypotheses.lean#L163-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CoordinateSizesOfHypotheses.lean#L163-L174

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSizesOfHypotheses
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux6
variable {k j ρ : ℕ}

theorem Formalism.FourierDecayAlt.P.Ux6.entry_le_gN {r : ℕ} (M : B.Mat k r) (i l : Fin (2 * r + k + 1)) : ‖M i l‖ ≤ B.gN M := by sorry
