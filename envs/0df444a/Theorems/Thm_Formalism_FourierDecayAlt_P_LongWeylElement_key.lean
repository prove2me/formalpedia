-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_key
-- name    : Formalism.FourierDecayAlt.P.LongWeylElement.key
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T19:39:35.331633+00:00
-- url     : https://prove2.me/theorems/b977a0d6-0cc0-4882-9bbc-1162db891394
-- title:
--   Long Weyl Element: key
-- statement:
--   The Long Weyl Element construction uses the key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LongWeylElement.lean#L882-L942
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LongWeylElement.lean#L882-L942

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LongWeylElement
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_key

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
open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.REAL
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LongWeylElement
variable {k r r' : ℕ}
attribute [local instance] sfHeis

theorem Formalism.FourierDecayAlt.P.LongWeylElement.key (hN : ClosedN) (μN' μb' : Measure (Mt k r')) (hμN' : IsHaarOn (Nset k r') μN') [SigmaFinite μb']
    (f : Mt k (1 + r') → ℝ≥0∞) (hf : Measurable f) (c : ℂ) (B : Mat k r') :
    ∫⁻ X : HPar k r' × HPar k r', ∫⁻ q : (Mt k r' × Mt k r') × Mt k r',
        f (oneStep k r' X.1 c ((Matrix.of q.1.1)⁻¹ * B * Matrix.of q.2 * Matrix.of q.1.2) X.2)
          ∂((μN'.prod μN').prod μb') =
      ∫⁻ p : (Mt k (1 + r') × Mt k (1 + r')) × Mt k (1 + r'),
        f ((Matrix.of p.1.1)⁻¹ * (w0 k r' c * ιLev k 1 r' B) * Matrix.of p.2 * Matrix.of p.1.2)
          ∂(((((volume : Measure (HPar k r')).prod μN').map (thetaF k r')).prod
            (((volume : Measure (HPar k r')).prod μN').map (thetaF k r'))).prod (μb'.map (levM k r'))) := by sorry
