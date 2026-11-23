-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd2_ins_mul_eU
-- name    : Formalism.FourierDecayAlt.P.Wd2.ins_mul_eU
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:33:12.811358+00:00
-- url     : https://prove2.me/theorems/7b226cff-c3db-48d6-8400-1c6b60c6735b
-- title:
--   Wd2: ins mul e U
-- statement:
--   The Wd2 construction uses the ins mul e U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KroneckerEmbedMulApply.lean#L109-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KroneckerEmbedMulApply.lean#L109-L119

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KroneckerEmbedMulApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd2
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [Ring A] [Algebra K A] [Fintype S] [DecidableEq S]

theorem Formalism.FourierDecayAlt.P.Wd2.ins_mul_eU (a : S) (N : M2 (SlopeTestRemainingChoices S A)) (hN : FreeOf2 a N) (j m : Fin 2) :
    ins a N * eU a j m = ∑ k, eU a k m * N k j := by sorry
