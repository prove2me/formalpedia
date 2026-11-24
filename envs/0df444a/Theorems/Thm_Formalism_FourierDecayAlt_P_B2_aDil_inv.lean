-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2_aDil_inv
-- name    : Formalism.FourierDecayAlt.P.B2.aDil_inv
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T14:26:26.533099+00:00
-- url     : https://prove2.me/theorems/3a348012-d5ea-40bc-a5d7-5aea48ad11f3
-- title:
--   B2: a Dil inv
-- statement:
--   The B2 construction uses the a Dil inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdjointnessPolynomiallyBounded.lean#L16-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdjointnessPolynomiallyBounded.lean#L16-L26

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
open Formalism.FourierDecayAlt.P.B2

theorem Formalism.FourierDecayAlt.P.B2.aDil_inv (k r : ℕ) (t : ℝ) (ht : t ≠ 0) : (aDil k r t)⁻¹ = aDil k r t⁻¹ := by sorry
