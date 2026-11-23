-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G7_signature_first_coordinate
-- name    : Formalism.FourierDecayAlt.P.G7.signature_first_coordinate
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:00:21.6412+00:00
-- url     : https://prove2.me/theorems/fe130aef-a5e7-4d50-bc49-998b5912548c
-- title:
--   G7: signature first coordinate
-- statement:
--   The G7 construction uses the signature first coordinate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralConvergesAbs.lean#L198-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralConvergesAbs.lean#L198-L203

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

theorem Formalism.FourierDecayAlt.P.G7.signature_first_coordinate {m : ℕ} (D t σ : ℂ) (ht : t ≠ 0) (ρ' : Fin m → ℂ) (X : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
    (B : Fin (m + 1) → ℂ) (hC : Cof X B t ≠ 0) :
    sig D t (Fin.cons (rho1 D σ ρ' X B t) ρ') X B = σ := by sorry
