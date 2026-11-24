-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_Pall_eq
-- name    : Formalism.InvariantFactorPaths.KP.LL.Pall_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:36:12.887731+00:00
-- url     : https://prove2.me/theorems/a132d2e4-0802-479b-bdab-d1608e1490d3
-- title:
--   LL: Pall eq
-- statement:
--   The LL construction uses the Pall eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/ChainEmbInj.lean#L33-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/ChainEmbInj.lean#L33-L34

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

theorem Formalism.InvariantFactorPaths.KP.LL.Pall_eq (j : Fin D.T.t → ℕ) (jp : ℕ) (y : MvPolynomial (BVar N r D.T.t) ℚ_[p]) :
    D.Pall p j jp y = Pplus p D jp (PL p D (List.finRange D.T.t) j jp y) := by sorry
