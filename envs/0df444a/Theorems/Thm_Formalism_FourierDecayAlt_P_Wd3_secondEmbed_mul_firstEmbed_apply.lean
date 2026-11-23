-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd3_secondEmbed_mul_firstEmbed_apply
-- name    : Formalism.FourierDecayAlt.P.Wd3.secondEmbed_mul_firstEmbed_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:44:46.833825+00:00
-- url     : https://prove2.me/theorems/c74c5fb4-f056-4288-be6b-cb7f1df1f0f7
-- title:
--   Wd3: second Embed mul first Embed apply
-- statement:
--   The Wd3 construction uses the second Embed mul first Embed apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SecondEmbedMulFirstEmbedApply.lean#L90-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SecondEmbedMulFirstEmbedApply.lean#L90-L93

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondEmbedMulFirstEmbedApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd3
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A]
  [Fintype S] [DecidableEq S]

theorem Formalism.FourierDecayAlt.P.Wd3.secondEmbed_mul_firstEmbed_apply {B : Type} [Ring B] (M N : M2 B) (i r j s : Fin 2) :
    (E2 N * E1 M) (i, r) (j, s) = N r s * M i j := by sorry
