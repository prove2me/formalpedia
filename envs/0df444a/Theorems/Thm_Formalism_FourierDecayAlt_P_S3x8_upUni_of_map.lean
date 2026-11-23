-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_upUni_of_map
-- name    : Formalism.FourierDecayAlt.P.S3x8.upUni_of_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:15:43.427324+00:00
-- url     : https://prove2.me/theorems/6e4ab666-ff35-40dd-b0ae-56c730670813
-- title:
--   S3x8: up Uni of map
-- statement:
--   The S3x8 construction uses the up Uni of map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CentreBlockStructure.lean#L214-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CentreBlockStructure.lean#L214-L216

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CentreBlockStructure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x8
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni IsLowUni isUpUni_mul isUpUni_inv isUpUni_one isUpUni_det isLowUni_det)
open Formalism.FourierDecayAlt.S3
variable {A F : Type} [CommRing A] [CommRing F]

theorem Formalism.FourierDecayAlt.P.S3x8.upUni_of_map (f : A →+* F) (hf : Function.Injective f) {r : ℕ} {x : Matrix (Fin r) (Fin r) A}
    (h : IsUpUni (x.map f)) : IsUpUni x := by sorry
