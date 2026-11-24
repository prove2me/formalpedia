-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_adjointness_of_bessel_transform
-- name    : Formalism.FourierDecayAlt.P.adjointness_of_bessel_transform
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T14:36:19.994441+00:00
-- url     : https://prove2.me/theorems/829193bf-19bc-4954-875c-4806e22b933f
-- title:
--   P: adjointness of bessel transform
-- statement:
--   The P construction uses the adjointness of bessel transform property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdjointnessPolynomiallyBounded.lean#L40-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdjointnessPolynomiallyBounded.lean#L40-L48

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B

theorem Formalism.FourierDecayAlt.P.adjointness_of_bessel_transform : Formalism.FourierDecayAlt.B.AssembleAdj := by sorry
