-- Prove2me | Theorems.Thm_Formalism_GM_FockB_Ehp_mem
-- name    : Formalism.GM.FockB.Ehp_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:44:18.079717+00:00
-- url     : https://prove2.me/theorems/70ce59d2-6af6-4823-ad8e-f6131c7071cc
-- title:
--   Fock B: Ehp mem
-- statement:
--   The Fock B construction uses the Ehp mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FockBlocks.lean#L103-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FockBlocks.lean#L103-L104

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

theorem Formalism.GM.FockB.Ehp_mem : (Ehp w e zv sv : MvPolynomial σ k) ∈ Algebra.adjoin k (X '' V w e zv sv) := by sorry
