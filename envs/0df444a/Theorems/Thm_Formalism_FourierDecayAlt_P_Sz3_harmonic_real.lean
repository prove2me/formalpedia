-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz3_harmonic_real
-- name    : Formalism.FourierDecayAlt.P.Sz3.harmonic_real
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:35:51.095884+00:00
-- url     : https://prove2.me/theorems/ddd05eb7-16c8-42f7-856b-657bed8d534c
-- title:
--   Sz3: harmonic real
-- statement:
--   The Sz3 construction uses the harmonic real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/VandermondeRatioHarmonic.lean#L203-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/VandermondeRatioHarmonic.lean#L203-L206

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_VandermondeRatioHarmonic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz3
open Finset Formalism.FourierDecayAlt.Sz

theorem Formalism.FourierDecayAlt.P.Sz3.harmonic_real (n : ℕ) : ((harmonic n : ℚ) : ℝ) = ∑ d ∈ Icc 1 n, 1 / (d : ℝ) := by sorry
