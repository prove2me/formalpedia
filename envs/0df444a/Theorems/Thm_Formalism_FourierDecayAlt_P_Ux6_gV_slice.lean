-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_gV_slice
-- name    : Formalism.FourierDecayAlt.P.Ux6.gV_slice
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T16:29:13.882608+00:00
-- url     : https://prove2.me/theorems/925e5ea7-13b0-4313-9a88-d689d2ac63c6
-- title:
--   Ux6: g V slice
-- statement:
--   The Ux6 construction uses the g V slice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CoordinateSizesOfHypotheses.lean#L301-L309
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CoordinateSizesOfHypotheses.lean#L301-L309

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

theorem Formalism.FourierDecayAlt.P.Ux6.gV_slice {k j ρ : ℕ} (x x' : RC k j ρ) (M : B.Mat k (j + ρ)) (hM : M ∈ B.GV k (j + ρ)) :
    (Rn k j ρ x)⁻¹ * M * Rn k j ρ x' ∈ B.GV k (j + ρ) := by sorry
