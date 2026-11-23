-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G7_ae_cof_ne
-- name    : Formalism.FourierDecayAlt.P.G7.ae_cof_ne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:00:00.520985+00:00
-- url     : https://prove2.me/theorems/5706a7f7-f229-4a12-a76a-635d1bf7a2d9
-- title:
--   G7: ae cof ne
-- statement:
--   The G7 construction uses the ae cof ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralConvergesAbs.lean#L285-L295
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralConvergesAbs.lean#L285-L295

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G7
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G2

theorem Formalism.FourierDecayAlt.P.G7.ae_cof_ne (β t : ℂ) (ht : t ≠ 0) {m : ℕ} (X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    (hX : IsStrictUpper X) : ∀ᵐ B ∂(muPi β (Fin (m + 1))), Cof X B t ≠ 0 := by sorry
