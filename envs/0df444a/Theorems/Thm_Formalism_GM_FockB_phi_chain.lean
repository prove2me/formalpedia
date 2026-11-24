-- Prove2me | Theorems.Thm_Formalism_GM_FockB_phi_chain
-- name    : Formalism.GM.FockB.phi_chain
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:42:29.565098+00:00
-- url     : https://prove2.me/theorems/f1da1f5a-3637-4e22-a63d-ad64bae323b3
-- title:
--   Fock B: phi chain
-- statement:
--   The Fock B construction uses the phi chain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FockBlocks.lean#L307-L318
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FockBlocks.lean#L307-L318

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

theorem Formalism.GM.FockB.phi_chain (o n j : α → ℕ) (a : α) (L : List α) (hdisj : Disjoint (Va w e zv sv a) (VL w e zv sv L))
    (o0 n0 z0 : ℕ) (Y0 : MvPolynomial σ k) :
    Formalism.GM.tiePhi (w a) (e a) o0 n0 z0 (chainE w e zv sv j L * chainP w e zv sv z o n L Y0) =
      chainE w e zv sv j L * chainP w e zv sv z o n L (Formalism.GM.tiePhi (w a) (e a) o0 n0 z0 Y0) := by sorry
