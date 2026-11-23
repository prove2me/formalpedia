-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_block_count
-- name    : Formalism.FourierDecayAlt.P.S3x5.block_count
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:42:51.556869+00:00
-- url     : https://prove2.me/theorems/4d9cdfe3-0192-4aa7-a3c9-29ea05399dc5
-- title:
--   S3x5: block count
-- statement:
--   The S3x5 construction uses the block count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFrameCount.lean#L795-L870
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFrameCount.lean#L795-L870

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

theorem Formalism.FourierDecayAlt.P.S3x5.block_count
    (hW : ∀ (n a : ℕ) (J : Matrix (Fin n) (Fin n) K) (X Y : Matrix (Fin n) (Fin a) K),
      Jᴴ = J → IsUnit J.det → X.rank = a → Y.rank = a → Xᴴ * J * X = Yᴴ * J * Y →
      ∃ g : Matrix (Fin n) (Fin n) K, gᴴ * J * g = J ∧ g * X = Y)
    {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (T : Matrix α α K) (T' : Matrix β β K) (hT : Tᴴ = T) (hdT : IsUnit T.det) (hT' : T'ᴴ = T')
    (hdT' : IsUnit T'.det) :
    Nat.card {g : Matrix (α ⊕ β) (α ⊕ β) K // gᴴ * fromBlocks T 0 0 T' * g = fromBlocks T 0 0 T'} =
      Nat.card {X : Matrix (α ⊕ β) α K // Xᴴ * fromBlocks T 0 0 T' * X = T} *
        Nat.card {d : Matrix β β K // dᴴ * T' * d = T'} := by sorry
