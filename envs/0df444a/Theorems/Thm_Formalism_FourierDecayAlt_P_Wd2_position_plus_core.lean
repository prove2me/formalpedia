-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd2_position_plus_core
-- name    : Formalism.FourierDecayAlt.P.Wd2.position_plus_core
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:45:13.554775+00:00
-- url     : https://prove2.me/theorems/61b26a22-e78f-47b0-b5a0-9964a2a3e77d
-- title:
--   Wd2: position plus core
-- statement:
--   The Wd2 construction uses the position plus core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KroneckerEmbedMulApply.lean#L121-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KroneckerEmbedMulApply.lean#L121-L170

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

theorem Formalism.FourierDecayAlt.P.Wd2.position_plus_core (a : S) (M N : M2 (SlopeTestRemainingChoices S A)) (D : K) (hM : FreeOf2 a M) (hN : FreeOf2 a N)
    (H : ∀ i j k l, D • (M i j * N k l) - M k j * N i l = D • (N k l * M i j) - N k j * M i l) :
    (D • (1 : M2 (SlopeTestRemainingChoices S A)) - P0 a) * M * d0 (ins a N) =
      d0 (ins a N) * M * (D • (1 : M2 (SlopeTestRemainingChoices S A)) - P0 a) := by sorry
