-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_asm_num
-- name    : Formalism.InvariantFactorPaths.KP.LL.asm_num
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:36:17.46044+00:00
-- url     : https://prove2.me/theorems/a4eaf76a-2a9a-4b68-b4c5-467f885f89f5
-- title:
--   LL: asm num
-- statement:
--   The LL construction uses the asm num property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/LevelLatticeOf.lean#L9-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/LevelLatticeOf.lean#L9-L29

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PairStep
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LevelLatticeOf
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

theorem Formalism.InvariantFactorPaths.KP.LL.asm_num (p : ℕ) [Fact p.Prime] (a r : ℕ) (ha : 1 ≤ a) :
    r * Nat.log p (2 * a) + Nat.log p (6 * a + r) ≤ ⌈((r : ℝ) + 1) * lgV2 p a r⌉₊ := by sorry
