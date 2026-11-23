-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_hEmb_map
-- name    : Formalism.FourierDecayAlt.P.S3x2.hEmb_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:23:08.725794+00:00
-- url     : https://prove2.me/theorems/e7c89633-74f7-40ab-bf62-92b5bb2f2740
-- title:
--   S3x2: h Emb map
-- statement:
--   The S3x2 construction uses the h Emb map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ReductionSurjective.lean#L213-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ReductionSurjective.lean#L213-L215

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ReductionSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x2
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.S3
variable {A : Type} [CommRing A] {r k : ℕ}

theorem Formalism.FourierDecayAlt.P.S3x2.hEmb_map {B : Type} [CommRing B] (f : A →+* B) (h : Matrix (Fin k) (Fin k) A) :
    (hEmb r h).map f = hEmb r (h.map f) := by sorry
