-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_xi_notin
-- name    : Formalism.InvariantFactorPaths.KP.LL.xi_notin
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:58:39.717636+00:00
-- url     : https://prove2.me/theorems/b4ccc184-a985-4c1e-bbab-0321802e5eb9
-- title:
--   LL: xi notin
-- statement:
--   The LL construction uses the xi notin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/ChainEmbInj.lean#L55-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/ChainEmbInj.lean#L55-L58

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

theorem Formalism.InvariantFactorPaths.KP.LL.xi_notin (c : Fin r) : xiVar N r D.T.t c ∉ Set.range (chainEmb N r D.T.t) := by sorry
