-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_cf_inv_of
-- name    : Formalism.FourierDecayAlt.P.B2x8.cf_inv_of
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T15:57:54.130794+00:00
-- url     : https://prove2.me/theorems/3eaa0570-39ce-4ab1-814a-9e11735bdecc
-- title:
--   B2x8: cf inv of
-- statement:
--   The B2x8 construction uses the cf inv of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L1284-L1290
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CmHalfIntegralGeneratorMemAlgebraicClosure.lean#L1284-L1290

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

theorem Formalism.FourierDecayAlt.P.B2x8.cf_inv_of (g : Mat k (1 + r')) (T : ℂ × HPar k r' → ℂ × HPar k r')
    (hT : MeasurePreserving T (μx.prod (volume : Measure (HPar k r'))) (μx.prod (volume : Measure (HPar k r'))))
    (h : ∀ᵐ p ∂(μx.prod (volume : Measure (HPar k r'))), g *ᵥ Ψt k r' p = Ψt k r' (T p)) :
    (coneMeas k r').map (fun x => g *ᵥ x) = coneMeas k r' := by sorry
