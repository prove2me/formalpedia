-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_inner_eq
-- name    : Formalism.FourierDecayAlt.P.B2x9.inner_eq
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T15:59:46.927803+00:00
-- url     : https://prove2.me/theorems/465cfe1d-3d2a-4ef7-9c46-4c4d2a854e8c
-- title:
--   B2x9: inner eq
-- statement:
--   The B2x9 construction uses the inner eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianLeviVectorBaseOrthogonal.lean#L554-L593
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianLeviVectorBaseOrthogonal.lean#L554-L593

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x9
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}

theorem Formalism.FourierDecayAlt.P.B2x9.inner_eq (HIv : HaarInv) (hG : ClosedG) (HI : HeisInv) (μG₁ : Measure (Mt k r')) (h₁ : IsHaarOn (GV k r') μG₁)
    (hP : IsClosedSubgroup (P1set k r')) (hμP : IsHaarOn (P1set k r') (muP μG₁)) (f : Mt k (1 + r') → ℝ≥0∞) (hf : Measurable f)
    (c : ℂ) :
    ∫⁻ p : (HPar k r' × HPar k r') × Mt k r', f (Psi k r' (c, p))
          ∂((volume : Measure (HPar k r' × HPar k r')).prod μG₁) = ∫⁻ x : HPar k r', Ff (muP μG₁) f (tau k r' (c, x)) := by sorry
