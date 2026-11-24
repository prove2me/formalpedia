-- Prove2me | Theorems.Thm_Formalism_GM_FockB_good_of_ops
-- name    : Formalism.GM.FockB.good_of_ops
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:21:00.012863+00:00
-- url     : https://prove2.me/theorems/46d44184-b4ee-4b47-b97e-4f76c39b8f16
-- title:
--   Fock B: good of ops
-- statement:
--   The Fock B construction uses the good of ops property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FockBlocks.lean#L145-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FockBlocks.lean#L145-L157

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

theorem Formalism.GM.FockB.good_of_ops {S : Set σ} (hS : Disjoint (V w e zv sv) S) {T : Module.End k (MvPolynomial σ k)}
    (hT : T ∈ Ops S) {o n : ℕ} {y : MvPolynomial σ k} (hy : Good w e zv sv o n y) :
    Good w e zv sv o n (T y) := by sorry
