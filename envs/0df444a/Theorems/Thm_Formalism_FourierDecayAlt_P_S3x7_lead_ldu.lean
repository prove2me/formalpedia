-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_lead_ldu
-- name    : Formalism.FourierDecayAlt.P.S3x7.lead_ldu
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:25:10.765513+00:00
-- url     : https://prove2.me/theorems/c8e785c0-2635-4b04-8aac-bdf25b5a4201
-- title:
--   S3x7: lead ldu
-- statement:
--   The S3x7 construction uses the lead ldu property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LduDecompositionExists.lean#L111-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LduDecompositionExists.lean#L111-L114

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LduDecompositionExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x7
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni IsLowUni isUpUni_mul isLowUni_mul isUpUni_inv isLowUni_inv isUpUni_one isLowUni_one
  isUpUni_det isLowUni_det)
open Formalism.FourierDecayAlt.S3
variable {A : Type} [CommRing A]

theorem Formalism.FourierDecayAlt.P.S3x7.lead_ldu {r : ℕ} {L U : Matrix (Fin r) (Fin r) A} (d : Fin r → A) (hL : IsLowUni L)
    (hU : IsUpUni U) (l : ℕ) (hl : l ≤ r) :
    lead (L * Matrix.diagonal d * U) l hl = ∏ i : Fin l, d (Fin.castLE hl i) := by sorry
