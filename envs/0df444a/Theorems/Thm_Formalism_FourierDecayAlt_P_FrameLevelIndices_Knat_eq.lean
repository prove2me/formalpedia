-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FrameLevelIndices_Knat_eq
-- name    : Formalism.FourierDecayAlt.P.FrameLevelIndices.Knat_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:59:06.462435+00:00
-- url     : https://prove2.me/theorems/47a9ad0f-ed18-4a78-be5d-5387fcb276c2
-- title:
--   Frame Level Indices: Knat eq
-- statement:
--   The Frame Level Indices construction uses the Knat eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FrameLevelIndices.lean#L46-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FrameLevelIndices.lean#L46-L51

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PointwiseStabiliserParametrisationBijective
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ReductionSurjective
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MemIntegralGlOfMiddleBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LduDecompositionExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameLevelIndices
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_Knat_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FrameLevelIndices
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni upUniG isUpUni_one)
open Formalism.FourierDecayAlt.S3
variable {o : Type} [CommRing o] [IsLocalRing o] {r k : ℕ}

theorem Formalism.FourierDecayAlt.P.FrameLevelIndices.Knat_eq (L : Levels o r k) :
    L.Knat = (S3x1.parG (r := r) (S3x1.gpUnit (A := IsLocalRing.ResidueField o) (k := k))).comap
      (red o (Idx r k)) := by sorry
