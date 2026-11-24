-- Prove2me | Theorems.Thm_Formalism_GM_FockB_chain_main
-- name    : Formalism.GM.FockB.chain_main
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T22:13:41.373568+00:00
-- url     : https://prove2.me/theorems/977a0481-a022-41d4-8e07-aadeba98857a
-- title:
--   Fock B: chain main
-- statement:
--   The Fock B construction uses the chain main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FockBlocks.lean#L320-L351
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FockBlocks.lean#L320-L351

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

theorem Formalism.GM.FockB.chain_main [CharZero k] (hr : 1 ≤ r) (o n j : α → ℕ) (L : List α)
    (hv : ∀ a ∈ L, M.TieVars (w a) (e a) (zv a) (sv a))
    (hd : L.Pairwise fun a b => Disjoint (Va w e zv sv a) (Va w e zv sv b))
    (Y : MvPolynomial σ k) (hY : ∀ a ∈ L, Good (w a) (e a) (zv a) (sv a) (o a) (n a) Y) :
    ∀ Y' : MvPolynomial σ k, (∀ a ∈ L, Good (w a) (e a) (zv a) (sv a) (o a) (n a) Y') →
      M.fockK (chainE w e zv sv j L * chainP w e zv sv z o n L Y)
          (chainE w e zv sv j L * chainP w e zv sv z o n L Y') =
        cst (r := r) z o n j L * M.fockK Y (chainPhi w e z o n L Y') := by sorry
