-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd3_plus_core
-- name    : Formalism.FourierDecayAlt.P.Wd3.plus_core
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:44:49.748799+00:00
-- url     : https://prove2.me/theorems/66d4a8f2-ab14-41b1-966c-40a8edb982c8
-- title:
--   Wd3: plus core
-- statement:
--   The Wd3 construction uses the plus core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SecondEmbedMulFirstEmbedApply.lean#L115-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SecondEmbedMulFirstEmbedApply.lean#L115-L144

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

theorem Formalism.FourierDecayAlt.P.Wd3.plus_core (a : S) (M N : M2 (SlopeTestRemainingChoices S A)) (D : K) (hM : FreeOf2 a M) (hN : FreeOf2 a N)
    (h : ∀ i r j s, D • (M i j * N r s) - M r j * N i s = D • (N r s * M i j) - N r j * M i s) :
    (D • (1 : M2 (SlopeTestRemainingChoices S A)) - P0 a) * M * d0 (ins a N) =
      d0 (ins a N) * M * (D • (1 : M2 (SlopeTestRemainingChoices S A)) - P0 a) := by sorry
