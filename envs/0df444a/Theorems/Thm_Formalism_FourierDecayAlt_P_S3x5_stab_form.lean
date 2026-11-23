-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_stab_form
-- name    : Formalism.FourierDecayAlt.P.S3x5.stab_form
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:47:19.413215+00:00
-- url     : https://prove2.me/theorems/cab9d908-5b80-4eef-b505-d1b000ed3cc7
-- title:
--   S3x5: stab form
-- statement:
--   The S3x5 construction uses the stab form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFrameCount.lean#L764-L784
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFrameCount.lean#L764-L784

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFrameCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x5
open Matrix Formalism.FourierDecayAlt.S3
variable {K : Type} [Field K] [Fintype K] [StarRing K]
omit [Fintype K]

theorem Formalism.FourierDecayAlt.P.S3x5.stab_form {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (T : Matrix α α K) (T' : Matrix β β K) (hdT : IsUnit T.det)
    (k : Matrix (α ⊕ β) (α ⊕ β) K) (h1 : k * (fromRows (1 : Matrix α α K) (0 : Matrix β α K) : Matrix (α ⊕ β) α K) =
      (fromRows (1 : Matrix α α K) (0 : Matrix β α K) : Matrix (α ⊕ β) α K))
    (h2 : kᴴ * fromBlocks T 0 0 T' * k = fromBlocks T 0 0 T') :
    ∃ d : Matrix β β K, k = fromBlocks 1 0 0 d ∧ dᴴ * T' * d = T' := by sorry
