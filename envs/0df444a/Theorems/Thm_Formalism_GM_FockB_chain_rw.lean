-- Prove2me | Theorems.Thm_Formalism_GM_FockB_chain_rw
-- name    : Formalism.GM.FockB.chain_rw
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:42:16.170376+00:00
-- url     : https://prove2.me/theorems/4815eef8-5531-4aa9-b5f5-dd7e11d1fcfc
-- title:
--   Fock B: chain rw
-- statement:
--   The Fock B construction uses the chain rw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FockBlocks.lean#L286-L297
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FockBlocks.lean#L286-L297

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

theorem Formalism.GM.FockB.chain_rw (o n j : α → ℕ) (a : α) (L : List α) (hdisj : Disjoint (Va w e zv sv a) (VL w e zv sv L))
    (Y0 : MvPolynomial σ k) :
    chainE w e zv sv j (a :: L) * chainP w e zv sv z o n (a :: L) Y0 =
      Ehp (w a) (e a) (zv a) (sv a) ^ j a * M.tieP (w a) (e a) (zv a) (sv a) (o a) (n a) (z a)
        (chainE w e zv sv j L * chainP w e zv sv z o n L Y0) := by sorry
