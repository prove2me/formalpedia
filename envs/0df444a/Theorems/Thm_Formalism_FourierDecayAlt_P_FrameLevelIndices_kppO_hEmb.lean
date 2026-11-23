-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_FrameLevelIndices_kppO_hEmb
-- name    : Formalism.FourierDecayAlt.P.FrameLevelIndices.kppO_hEmb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:59:16.093634+00:00
-- url     : https://prove2.me/theorems/c2d32fcb-6fdb-4b44-9b87-008599f34242
-- title:
--   Frame Level Indices: kpp O h Emb
-- statement:
--   The Frame Level Indices construction uses the kpp O h Emb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FrameLevelIndices.lean#L123-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FrameLevelIndices.lean#L123-L127

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PointwiseStabiliserParametrisationBijective
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ReductionSurjective
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MemIntegralGlOfMiddleBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LduDecompositionExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameLevelIndices
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

theorem Formalism.FourierDecayAlt.P.FrameLevelIndices.kppO_hEmb {h : Matrix (Fin k) (Fin k) o} (hd : IsUnit h.det)
    (hu : IsUpUni (h.map (IsLocalRing.residue o))) : KppO (hEmb r h) := by sorry
