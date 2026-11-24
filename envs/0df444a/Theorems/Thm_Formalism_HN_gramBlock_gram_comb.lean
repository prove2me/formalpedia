-- Prove2me | Theorems.Thm_Formalism_HN_gramBlock_gram_comb
-- name    : Formalism.HN.gramBlock_gram_comb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:27.30057+00:00
-- url     : https://prove2.me/theorems/150fd8d5-9134-4b80-8a59-42e495651cb7
-- title:
--   HN: gram Block gram comb
-- statement:
--   The HN construction uses the gram Block gram comb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/GramBlock.lean#L20-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/GramBlock.lean#L20-L27

import Definitions.Def_Formalism_HarderNarasimhan_DefsPl
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_GramBlock
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
open Formalism Formalism.HN

theorem Formalism.HN.gramBlock_gram_comb {ι E F : Type*} [Fintype ι] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (g : E →ₗ[ℝ] F) (f : ι → E) (M : Matrix ι ι ℝ) :
    Matrix.gram ℝ (fun j => g (∑ i, M i j • f i)) = M.transpose * Matrix.gram ℝ (fun i => g (f i)) * M := by sorry
