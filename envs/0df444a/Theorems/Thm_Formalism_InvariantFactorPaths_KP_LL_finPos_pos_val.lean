-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_finPos_pos_val
-- name    : Formalism.InvariantFactorPaths.KP.LL.finPos_pos_val
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T21:25:42.192923+00:00
-- url     : https://prove2.me/theorems/75ff1d22-6e35-4246-83a9-35a44c77f387
-- title:
--   LL: fin Pos pos val
-- statement:
--   The LL construction uses the fin Pos pos val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/LetterAtSuccVal.lean#L27-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/LetterAtSuccVal.lean#L27-L30

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_SmulMemOfNorm
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LetterAtSuccVal
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
variable {N r : ℕ} (D : BlockData N)
variable {D}

theorem Formalism.InvariantFactorPaths.KP.LL.finPos_pos_val (hB : D.BlockOK) (i : Fin D.T.t) : (finPos N (D.T.pos i)).val = D.T.pos i := by sorry
