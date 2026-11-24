-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_tieP_smul
-- name    : Formalism.InvariantFactorPaths.KP.LL.tieP_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:23.779226+00:00
-- url     : https://prove2.me/theorems/2c5d5413-70a8-42af-b239-d047df5a7c03
-- title:
--   LL: tie P smul
-- statement:
--   The LL construction uses the tie P smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/PstScalMem.lean#L10-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/PstScalMem.lean#L10-L15

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PairStep
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_PhiInt
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PstScalMem
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

theorem Formalism.InvariantFactorPaths.KP.LL.tieP_smul {k σ : Type} [Field k] {r : ℕ} (w e : Fin r → σ) (zv sv : σ) (o n z : ℕ) (c : k)
    (y : MvPolynomial σ k) : tieP w e zv sv o n z (c • y) = c • tieP w e zv sv o n z y := by sorry
