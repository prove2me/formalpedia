-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_Rn_23
-- name    : Formalism.FourierDecayAlt.P.Ux6.Rn_23
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T16:30:43.552087+00:00
-- url     : https://prove2.me/theorems/51ab6430-4050-436a-975b-8b2f479ad7d7
-- title:
--   Ux6: Rn 23
-- statement:
--   The Ux6 construction uses the Rn 23 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CoordinateSizesOfHypotheses.lean#L180-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CoordinateSizesOfHypotheses.lean#L180-L182

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

theorem Formalism.FourierDecayAlt.P.Ux6.Rn_23 (x : RC k j ρ) (i : Fin (2 * ρ + k + 1)) (b : Fin j) :
    Rn k j ρ x (eB k j ρ (Sum.inl (Sum.inr i))) (eB k j ρ (Sum.inr b)) = x.1 i b := by sorry
