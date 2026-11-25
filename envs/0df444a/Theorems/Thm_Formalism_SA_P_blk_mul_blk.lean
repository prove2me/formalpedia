-- Prove2me | Theorems.Thm_Formalism_SA_P_blk_mul_blk
-- name    : Formalism.SA.P.blk_mul_blk
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:52:31.638796+00:00
-- url     : https://prove2.me/theorems/75e50b75-9f28-4a7a-8bf9-eacbafd0ba18
-- title:
--   P: blk mul blk
-- statement:
--   The P construction uses the blk mul blk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeRigidity/HeightMinimum/BlockEquationHolds.lean#L11-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeRigidity/HeightMinimum/BlockEquationHolds.lean#L11-L24

import Definitions.Def_Formalism_LatticeRigidity_StatementA
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_BlockEquationHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.SA Formalism.SA.P
open Matrix Formalism.SA.A
variable {R : Type} [CommRing R] {m : ℕ}

theorem Formalism.SA.P.blk_mul_blk (A A' : Matrix (Fin (m+1)) (Fin (m+1)) R) (b c b' c' : Fin (m+1) → R) (d d' : R) :
    blk A b c d * blk A' b' c' d' =
      blk (A * A' + vecMulVec b c') (A *ᵥ b' + d' • b) (c ᵥ* A' + d • c') (c ⬝ᵥ b' + d * d') := by sorry
