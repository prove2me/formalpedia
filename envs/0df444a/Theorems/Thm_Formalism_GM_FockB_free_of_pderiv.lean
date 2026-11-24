-- Prove2me | Theorems.Thm_Formalism_GM_FockB_free_of_pderiv
-- name    : Formalism.GM.FockB.free_of_pderiv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:13:50.515797+00:00
-- url     : https://prove2.me/theorems/cd0c2b75-b3a3-4ddf-a30b-4b8764b19c24
-- title:
--   Fock B: free of pderiv
-- statement:
--   The Fock B construction uses the free of pderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FockBlocks.lean#L163-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FockBlocks.lean#L163-L172

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
variable {k σ : Type} [Field k] {r : ℕ}
variable {w e : Fin r → σ} {zv sv : σ}

theorem Formalism.GM.FockB.free_of_pderiv [CharZero k] {v : σ} {y : MvPolynomial σ k} (h : pderiv v y = 0) :
    ∀ m ∈ y.support, m v = 0 := by sorry
