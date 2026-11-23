-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_st_drop
-- name    : Formalism.InvariantFactorPaths.KP.LL.st_drop
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:59:14.715931+00:00
-- url     : https://prove2.me/theorems/71070a67-3b72-4e97-85ad-c9b912bd5053
-- title:
--   LL: st drop
-- statement:
--   The LL construction uses the st drop property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/StepTie.lean#L17-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/StepTie.lean#L17-L22

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PairStep
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_StepTie
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
variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (D : BlockData N)

theorem Formalism.InvariantFactorPaths.KP.LL.st_drop (t k : ℕ) (hk : k < t) :
    (List.finRange t).drop k = ⟨k, hk⟩ :: (List.finRange t).drop (k + 1) := by sorry
