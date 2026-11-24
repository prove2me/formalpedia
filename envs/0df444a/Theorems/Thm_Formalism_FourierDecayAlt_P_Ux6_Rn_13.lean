-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_Rn_13
-- name    : Formalism.FourierDecayAlt.P.Ux6.Rn_13
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T16:29:47.15796+00:00
-- url     : https://prove2.me/theorems/ca1d7577-c118-4dc5-9c17-c4c74608fb95
-- title:
--   Ux6: Rn 13
-- statement:
--   The Ux6 construction uses the Rn 13 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CoordinateSizesOfHypotheses.lean#L184-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CoordinateSizesOfHypotheses.lean#L184-L187

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

theorem Formalism.FourierDecayAlt.P.Ux6.Rn_13 (x : RC k j ρ) (a b : Fin j) :
    Rn k j ρ x (eB k j ρ (Sum.inl (Sum.inl a))) (eB k j ρ (Sum.inr b)) =
      (G.wMat j * ((-(1 / 2 : ℂ)) • ((Matrix.of x.1)ᴴ * Hpk k ρ * Matrix.of x.1) + skewOf x.2)) a b := by sorry
