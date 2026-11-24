-- Prove2me | Theorems.Thm_Formalism_GM_FockB_chainPhi_mem
-- name    : Formalism.GM.FockB.chainPhi_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:13:50.213147+00:00
-- url     : https://prove2.me/theorems/3fc12608-89a9-4816-9bd7-48723b765419
-- title:
--   Fock B: chain Phi mem
-- statement:
--   The Fock B construction uses the chain Phi mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FockBlocks.lean#L277-L284
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FockBlocks.lean#L277-L284

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

theorem Formalism.GM.FockB.chainPhi_mem (o n : α → ℕ) (L : List α) :
    (chainPhi w e z o n L : Module.End k (MvPolynomial σ k)) ∈ Ops (VL w e zv sv L) := by sorry
