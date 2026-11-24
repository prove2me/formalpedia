-- Prove2me | Theorems.Thm_Formalism_GM_FockB_goodA
-- name    : Formalism.GM.FockB.goodA
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:13:54.48483+00:00
-- url     : https://prove2.me/theorems/c7a47f35-a75e-4005-b7d9-b6ee3f06505c
-- title:
--   Fock B: good A
-- statement:
--   The Fock B construction uses the good A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FockBlocks.lean#L595-L679
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FockBlocks.lean#L595-L679

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
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
variable {D : BlockData N}

theorem Formalism.GM.FockB.goodA [NeZero r] (hB : D.BlockOK) (j : Fin D.T.t → ℕ) (jp : ℕ) (y : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hy : y ∈ Y p (r := r) (D.lettersAt j jp) D.T.J D.T.thr) (g : MvPolynomial (BVar N r D.T.t) ℚ_[p])
    (hg : g ∈ XiPolZ p N r D.T.t (D.B - jp)) (a : Option (Fin D.T.t)) :
    Good (wA D a) (eA D a) (zA D a) (sA D a) (oA D j jp a) (nA D j jp a)
      (rename (chainEmb N r D.T.t) y * g) := by sorry
