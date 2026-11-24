-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux6_skewOf_conjTranspose
-- name    : Formalism.FourierDecayAlt.P.Ux6.skewOf_conjTranspose
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T15:22:48.932263+00:00
-- url     : https://prove2.me/theorems/0b081414-bda3-4d73-9596-8e628fc11b22
-- title:
--   Ux6: skew Of conj Transpose
-- statement:
--   The Ux6 construction uses the skew Of conj Transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CoordinateSizesOfHypotheses.lean#L133-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CoordinateSizesOfHypotheses.lean#L133-L141

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

theorem Formalism.FourierDecayAlt.P.Ux6.skewOf_conjTranspose (q : (G.UT j → ℂ) × (Fin j → ℝ)) : (skewOf q)ᴴ = -skewOf q := by sorry
