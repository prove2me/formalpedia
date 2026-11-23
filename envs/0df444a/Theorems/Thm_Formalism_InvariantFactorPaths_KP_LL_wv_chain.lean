-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_wv_chain
-- name    : Formalism.InvariantFactorPaths.KP.LL.wv_chain
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:58:39.156831+00:00
-- url     : https://prove2.me/theorems/f1c7b75b-97d0-47ac-b7c4-9ef9a0eb40c0
-- title:
--   LL: wv chain
-- statement:
--   The LL construction uses the wv chain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/ChainEmbInj.lean#L38-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/ChainEmbInj.lean#L38-L42

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LetterAtSuccVal
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_ChainEmbInj
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
open MvPolynomial Finset Formalism.GM.M
open scoped Pointwise
variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (D : BlockData N)
variable {p D}

theorem Formalism.InvariantFactorPaths.KP.LL.wv_chain (hB : D.BlockOK) (i : Fin D.T.t) (c : Fin r) :
    wv D i c = chainEmb N r D.T.t (D.letterAt (D.T.pos i), c) := by sorry
