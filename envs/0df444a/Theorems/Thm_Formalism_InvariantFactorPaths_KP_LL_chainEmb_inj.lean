-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_chainEmb_inj
-- name    : Formalism.InvariantFactorPaths.KP.LL.chainEmb_inj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:26:00.557983+00:00
-- url     : https://prove2.me/theorems/e39e7479-b271-47db-8bf0-13bc20f55128
-- title:
--   LL: chain Emb inj
-- statement:
--   The LL construction uses the chain Emb inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/ChainEmbInj.lean#L50-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/ChainEmbInj.lean#L50-L53

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

theorem Formalism.InvariantFactorPaths.KP.LL.chainEmb_inj : Function.Injective (chainEmb N r D.T.t) := by sorry
