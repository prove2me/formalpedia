-- Prove2me | Theorems.Thm_Formalism_GM_FockB_step_same
-- name    : Formalism.GM.FockB.step_same
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:42:38.065417+00:00
-- url     : https://prove2.me/theorems/87c9f059-ac28-4c0d-ac7f-cdb9b51120dc
-- title:
--   Fock B: step same
-- statement:
--   The Fock B construction uses the step same property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FockBlocks.lean#L182-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FockBlocks.lean#L182-L196

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

theorem Formalism.GM.FockB.step_same [CharZero k] (hv : M.TieVars w e zv sv) (hr : 1 ≤ r) {o n z : ℕ} {y y' : MvPolynomial σ k}
    (hy : BiHom w e o n y) (hy' : BiHom w e o n y') (hz : M.ZSFree zv sv y) (hz' : M.ZSFree zv sv y')
    (j : ℕ) :
    M.fockK (Ehp w e zv sv ^ j * M.tieP w e zv sv o n z y) (Ehp w e zv sv ^ j * M.tieP w e zv sv o n z y') =
      ((j.factorial : k) ^ 2 * (((o + n + r + z + 1 + j - 1).choose j : ℕ) : k) * (z.factorial : k)) *
        M.fockK y (Formalism.GM.tiePhi w e o n z y') := by sorry
