-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_update_single
-- name    : Formalism.InvariantFactorPaths.KP.LL.update_single
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:15.808794+00:00
-- url     : https://prove2.me/theorems/2f2cd4d0-3dc5-44d4-9db3-c6544c632d2f
-- title:
--   LL: update single
-- statement:
--   The LL construction uses the update single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/LatticeEqualHolds.lean#L70-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/LatticeEqualHolds.lean#L70-L76

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PairStep
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LatticeEqualHolds
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
omit [NeZero r]

theorem Formalism.InvariantFactorPaths.KP.LL.update_single (j : Fin D.T.t → ℕ) (i : Fin D.T.t) (m : ℕ) :
    Function.update (j + Pi.single i m : Fin D.T.t → ℕ) i ((j + Pi.single i m : Fin D.T.t → ℕ) i + 1) =
      j + Pi.single i (m + 1) := by sorry
