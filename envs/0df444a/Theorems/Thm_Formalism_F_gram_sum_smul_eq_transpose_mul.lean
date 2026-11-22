-- Prove2me | Theorems.Thm_Formalism_F_gram_sum_smul_eq_transpose_mul
-- name    : Formalism.F.gram_sum_smul_eq_transpose_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T16:51:51.012406+00:00
-- url     : https://prove2.me/theorems/a0940b8a-7253-4184-901d-16805d8d91a3
-- title:
--   F: gram sum smul eq transpose mul
-- statement:
--   The F construction uses the gram sum smul eq transpose mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeSlopes/LatticeSlopesProofs/CovolEqGram.lean#L9-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LatticeSlopes/LatticeSlopesProofs/CovolEqGram.lean#L9-L16

import Definitions.Def_Formalism_LatticeSlopes_Statement
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_CovolEqGram
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.F

theorem Formalism.F.gram_sum_smul_eq_transpose_mul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι κ : Type*} [Fintype ι] (v : ι → E) (P : Matrix ι κ ℝ) :
    Matrix.gram ℝ (fun j => ∑ i, P i j • v i) = P.transpose * Matrix.gram ℝ v * P := by sorry
