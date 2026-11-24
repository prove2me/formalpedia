-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_po_Y_iter
-- name    : Formalism.InvariantFactorPaths.KP.LL.po_Y_iter
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:36:41.829492+00:00
-- url     : https://prove2.me/theorems/96f2d16f-54e5-43e3-b2a7-33aee0525cee
-- title:
--   LL: po Y iter
-- statement:
--   The LL construction uses the po Y iter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/PlusOp.lean#L152-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/PlusOp.lean#L152-L161

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LatticeEqualHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PlusOp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.KP Formalism.InvariantFactorPaths.KP.LL
open Formalism.GM
open MvPolynomial Finset Formalism.GM.M Formalism.GM.M.PhiIntegrality
variable {p : ℕ} [Fact p.Prime]
variable {N r : ℕ} [NeZero r] {D : BlockData N}

theorem Formalism.InvariantFactorPaths.KP.LL.po_Y_iter (hU : HypU p (r := r) D) (c : Fin r) (j : Fin D.T.t → ℕ) :
    ∀ k (jp : ℕ), ∀ y ∈ Y p (r := r) (D.lettersAt j jp) D.T.J D.T.thr,
      (po_d (D.uPos, c) ^ k) y ∈ Y p (r := r) (D.lettersAt j (jp + k)) D.T.J D.T.thr := by sorry
