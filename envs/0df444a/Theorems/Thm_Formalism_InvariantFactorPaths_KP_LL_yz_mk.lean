-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_yz_mk
-- name    : Formalism.InvariantFactorPaths.KP.LL.yz_mk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:58:56.833163+00:00
-- url     : https://prove2.me/theorems/db52a683-7fe7-4ddb-8755-1b6a7d6a3c7f
-- title:
--   LL: yz mk
-- statement:
--   The LL construction uses the yz mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/BiHomPlus.lean#L45-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/BiHomPlus.lean#L45-L48

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

theorem Formalism.InvariantFactorPaths.KP.LL.yz_mk {LL : Letters N} {q : ℕ} {J : Fin q → ℕ} {M : Fin q → WithTop ℤ}
    {y : MvPolynomial (Fin N × Fin r) ℚ_[p]} (h1 : y ∈ Y p (r := r) LL J M) (h2 : y ∈ IntPol p (Fin N × Fin r)) :
    y ∈ YZ p (r := r) LL J M := by sorry
