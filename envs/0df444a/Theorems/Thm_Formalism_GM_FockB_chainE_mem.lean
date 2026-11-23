-- Prove2me | Theorems.Thm_Formalism_GM_FockB_chainE_mem
-- name    : Formalism.GM.FockB.chainE_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:20:54.183731+00:00
-- url     : https://prove2.me/theorems/c0a94e6f-4a5a-42e9-b6c6-cac3ff11f9dc
-- title:
--   Fock B: chain E mem
-- statement:
--   The Fock B construction uses the chain E mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FockBlocks.lean#L268-L275
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FockBlocks.lean#L268-L275

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelDecomp
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.FockB
open MvPolynomial Finset
variable {k σ α : Type} [Field k] {r : ℕ} (w e : α → Fin r → σ) (zv sv : α → σ) (z : α → ℕ)
variable {w e zv sv z}

theorem Formalism.GM.FockB.chainE_mem (j : α → ℕ) (L : List α) :
    (chainE w e zv sv j L : MvPolynomial σ k) ∈ Algebra.adjoin k (X '' VL w e zv sv L) := by sorry
