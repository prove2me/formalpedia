-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd3_mul_Pf
-- name    : Formalism.FourierDecayAlt.P.Wd3.mul_Pf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:44:44.629181+00:00
-- url     : https://prove2.me/theorems/49b4fcf4-1ee1-40ed-8bf0-29d22c0d35f5
-- title:
--   Wd3: mul Pf
-- statement:
--   The Wd3 construction uses the mul Pf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SecondEmbedMulFirstEmbedApply.lean#L100-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SecondEmbedMulFirstEmbedApply.lean#L100-L103

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

theorem Formalism.FourierDecayAlt.P.Wd3.mul_Pf {B : Type} [Ring B] (X : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) B) (j s : Fin 2)
    (x : Fin 2 × Fin 2) : (X * Pf B) x (j, s) = X x (s, j) := by sorry
