-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_st_notin
-- name    : Formalism.InvariantFactorPaths.KP.LL.st_notin
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:36:50.515473+00:00
-- url     : https://prove2.me/theorems/83a34216-8eeb-4c92-8272-a712c038ddfd
-- title:
--   LL: st notin
-- statement:
--   The LL construction uses the st notin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/StepTie.lean#L24-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/StepTie.lean#L24-L27

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

theorem Formalism.InvariantFactorPaths.KP.LL.st_notin (t k : ℕ) (hk : k < t) : (⟨k, hk⟩ : Fin t) ∉ (List.finRange t).drop (k + 1) := by sorry
