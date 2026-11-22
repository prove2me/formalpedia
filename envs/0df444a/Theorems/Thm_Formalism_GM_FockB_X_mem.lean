-- Prove2me | Theorems.Thm_Formalism_GM_FockB_X_mem
-- name    : Formalism.GM.FockB.X_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:22:54.723341+00:00
-- url     : https://prove2.me/theorems/eb147abb-c659-4632-84d4-ae0f56270a5b
-- title:
--   Fock B: X mem
-- statement:
--   The Fock B construction uses the X mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FockBlocks.lean#L100-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FockBlocks.lean#L100-L101

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

theorem Formalism.GM.FockB.X_mem {S : Set σ} {u : σ} (hu : u ∈ S) : (X u : MvPolynomial σ k) ∈ Algebra.adjoin k (X '' S) := by sorry
