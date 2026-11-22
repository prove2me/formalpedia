-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_wU_ne_xi
-- name    : Formalism.InvariantFactorPaths.KP.LL.wU_ne_xi
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:41:50.226641+00:00
-- url     : https://prove2.me/theorems/a40c5466-6e19-4722-bd33-eace15060133
-- title:
--   LL: w U ne xi
-- statement:
--   The LL construction uses the w U ne xi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/BiHomPlus.lean#L28-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/BiHomPlus.lean#L28-L31

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_ChainEmbInj
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_BiHomPlus
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
variable {p : ℕ} [Fact p.Prime] {N r : ℕ} [NeZero r] {D : BlockData N}

theorem Formalism.InvariantFactorPaths.KP.LL.wU_ne_xi (c d : Fin r) : wU D c ≠ xiVar N r D.T.t d := by sorry
