-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_hEmb_apply
-- name    : Formalism.FourierDecayAlt.P.S3x2.hEmb_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:23:05.922462+00:00
-- url     : https://prove2.me/theorems/34384a5f-3a04-4cc3-aa6b-8dd258e1cc98
-- title:
--   S3x2: h Emb apply
-- statement:
--   The S3x2 construction uses the h Emb apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ReductionSurjective.lean#L210-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ReductionSurjective.lean#L210-L211

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

theorem Formalism.FourierDecayAlt.P.S3x2.hEmb_apply (h : Matrix (Fin k) (Fin k) A) (a b : Fin k) :
    hEmb r h (Sum.inr (Sum.inl (Sum.inl a))) (Sum.inr (Sum.inl (Sum.inl b))) = h a b := by sorry
