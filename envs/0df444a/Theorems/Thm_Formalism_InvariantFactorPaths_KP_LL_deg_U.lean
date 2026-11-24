-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_deg_U
-- name    : Formalism.InvariantFactorPaths.KP.LL.deg_U
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:36:29.211997+00:00
-- url     : https://prove2.me/theorems/38f57872-73b7-459b-9565-10bd5356a00a
-- title:
--   LL: deg U
-- statement:
--   The LL construction uses the deg U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/LetterAtSuccVal.lean#L107-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/LetterAtSuccVal.lean#L107-L114

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

theorem Formalism.InvariantFactorPaths.KP.LL.deg_U (hB : D.BlockOK) (j : Fin D.T.t → ℕ) (jp : ℕ) :
    (D.lettersAt j jp).deg D.uPos = D.LL.deg D.uPos - jp := by sorry
