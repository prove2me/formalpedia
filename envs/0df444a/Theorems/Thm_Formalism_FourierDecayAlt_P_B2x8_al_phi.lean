-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_al_phi
-- name    : Formalism.FourierDecayAlt.P.B2x8.al_phi
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T15:57:42.704418+00:00
-- url     : https://prove2.me/theorems/940f6eb5-5b75-4eb4-b28f-39a13351419d
-- title:
--   B2x8: al phi
-- statement:
--   The B2x8 construction uses the al phi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L1143-L1148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L1143-L1148

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}

theorem Formalism.FourierDecayAlt.P.B2x8.al_phi (g : Mat k (1 + r')) (w : Fin (2 * (1 + r') + k + 1) → ℂ) (a b : ℂ) (y : Fin (2 * r' + k + 1) → ℂ) :
    herm (Hpk k (1 + r')) (g *ᵥ mk3 k r' a y b) w =
      a * herm (Hpk k (1 + r')) (g *ᵥ e0 k r') w + herm (Hpk k (1 + r')) (g *ᵥ mk3 k r' 0 y 0) w +
        b * herm (Hpk k (1 + r')) (g *ᵥ es0 k r') w := by sorry
