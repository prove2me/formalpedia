-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_tk_herm_conjTranspose
-- name    : Formalism.FourierDecayAlt.P.B2x8.tk_herm_conjTranspose
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T15:02:09.248893+00:00
-- url     : https://prove2.me/theorems/628e9f13-41c5-4b54-96b1-69f59aa8e39d
-- title:
--   B2x8: tk herm conj Transpose
-- statement:
--   The B2x8 construction uses the tk herm conj Transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L34-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L34-L38

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
variable {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ)

theorem Formalism.FourierDecayAlt.P.B2x8.tk_herm_conjTranspose [DecidableEq ι] (g : Matrix ι ι ℂ) (u v : ι → ℂ) :
    herm H (g *ᵥ u) (g *ᵥ v) = herm (gᴴ * H * g) u v := by sorry
