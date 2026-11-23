-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x1_par_subgroupSet
-- name    : Formalism.FourierDecayAlt.P.S3x1.par_subgroupSet
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:41:56.422472+00:00
-- url     : https://prove2.me/theorems/15b17808-bfe4-4d3b-832d-5dd0df47d09c
-- title:
--   S3x1: par subgroup Set
-- statement:
--   The S3x1 construction uses the par subgroup Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PointwiseStabiliserParametrisationBijective.lean#L270-L273
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PointwiseStabiliserParametrisationBijective.lean#L270-L273

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
variable {A : Type} {r k : ℕ}
variable [CommRing A]
variable {P : Matrix (Fin k) (Fin k) A → Prop}

theorem Formalism.FourierDecayAlt.P.S3x1.par_subgroupSet (hP : GP P) : IsSubgroupSet (Par (r := r) P) := by sorry
