-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_ev_ne_xi
-- name    : Formalism.InvariantFactorPaths.KP.LL.ev_ne_xi
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:41:31.609519+00:00
-- url     : https://prove2.me/theorems/5dd0f8e6-8f07-47ca-a04a-105967de71cd
-- title:
--   LL: ev ne xi
-- statement:
--   The LL construction uses the ev ne xi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/BiHomPlus.lean#L20-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/BiHomPlus.lean#L20-L26

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

theorem Formalism.InvariantFactorPaths.KP.LL.ev_ne_xi (hB : D.BlockOK) (i : Fin D.T.t) (c d : Fin r) : ev D i c ≠ xiVar N r D.T.t d := by sorry
