-- Prove2me | Theorems.Thm_Formalism_GM_FockB_chain_orth
-- name    : Formalism.GM.FockB.chain_orth
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:13:41.357391+00:00
-- url     : https://prove2.me/theorems/38668358-790d-45e6-81fe-e2056869c105
-- title:
--   Fock B: chain orth
-- statement:
--   The Fock B construction uses the chain orth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FockBlocks.lean#L353-L389
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FockBlocks.lean#L353-L389

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

theorem Formalism.GM.FockB.chain_orth [CharZero k] (hr : 1 ≤ r) (o n j o' n' j' : α → ℕ) (L : List α)
    (hv : ∀ a ∈ L, M.TieVars (w a) (e a) (zv a) (sv a))
    (hd : L.Pairwise fun a b => Disjoint (Va w e zv sv a) (Va w e zv sv b))
    (hon : ∀ a ∈ L, j a = j' a → o a = o' a ∧ n a = n' a) (hne : ∃ a ∈ L, j a ≠ j' a)
    (Y : MvPolynomial σ k) (hY : ∀ a ∈ L, Good (w a) (e a) (zv a) (sv a) (o a) (n a) Y) :
    ∀ Y' : MvPolynomial σ k, (∀ a ∈ L, Good (w a) (e a) (zv a) (sv a) (o' a) (n' a) Y') →
      M.fockK (chainE w e zv sv j L * chainP w e zv sv z o n L Y)
          (chainE w e zv sv j' L * chainP w e zv sv z o' n' L Y') = 0 := by sorry
