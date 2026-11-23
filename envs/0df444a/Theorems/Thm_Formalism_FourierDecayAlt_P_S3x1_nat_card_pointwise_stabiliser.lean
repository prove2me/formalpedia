-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x1_nat_card_pointwise_stabiliser
-- name    : Formalism.FourierDecayAlt.P.S3x1.nat_card_pointwise_stabiliser
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:42:20.858912+00:00
-- url     : https://prove2.me/theorems/3ad09d4e-9fed-4ab6-a4a4-6415dedae618
-- title:
--   S3x1: nat card pointwise stabiliser
-- statement:
--   The S3x1 construction uses the nat card pointwise stabiliser property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PointwiseStabiliserParametrisationBijective.lean#L640-L649
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PointwiseStabiliserParametrisationBijective.lean#L640-L649

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PointwiseStabiliserParametrisationBijective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x1
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni upUniG isUpUni_mul isUpUni_inv isUpUni_one isUpUni_det)
open Formalism.FourierDecayAlt.S3
variable {A : Type} [CommRing A] {r k : ℕ}

theorem Formalism.FourierDecayAlt.P.S3x1.nat_card_pointwise_stabiliser (K : Type) [Field K] [Fintype K] (r k : ℕ) :
    Nat.card {x : Matrix (Idx r k) (Idx r k) K // IsInertiaInfiniteCyclotomic x} =
      Nat.card {h : Matrix (Fin k) (Fin k) K // IsUnit h.det} *
        Fintype.card K ^ (r * k + r * r + k * r) := by sorry
