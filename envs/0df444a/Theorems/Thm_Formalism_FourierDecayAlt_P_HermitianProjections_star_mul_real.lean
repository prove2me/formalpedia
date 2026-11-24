-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianProjections_star_mul_real
-- name    : Formalism.FourierDecayAlt.P.HermitianProjections.star_mul_real
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T15:19:31.499502+00:00
-- url     : https://prove2.me/theorems/bd9cac9d-66dc-48a1-9444-cc2c62f76f57
-- title:
--   Hermitian Projections: star mul real
-- statement:
--   The Hermitian Projections construction uses the star mul real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormBasics.lean#L166-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormBasics.lean#L166-L168

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormBasics
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianProjections

theorem Formalism.FourierDecayAlt.P.HermitianProjections.star_mul_real (a : ℝ) (x : ℂ) : (star x * ((a : ℂ) * x)).re = a * Complex.normSq x := by sorry
