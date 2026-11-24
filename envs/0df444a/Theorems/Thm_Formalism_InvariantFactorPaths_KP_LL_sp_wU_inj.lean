-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_sp_wU_inj
-- name    : Formalism.InvariantFactorPaths.KP.LL.sp_wU_inj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:36:38.784768+00:00
-- url     : https://prove2.me/theorems/fec276d7-4169-4b7f-b05e-f5eb506aeda8
-- title:
--   LL: sp w U inj
-- statement:
--   The LL construction uses the sp w U inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/StepPlus.lean#L30-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/StepPlus.lean#L30-L33

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PairStep
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_StepPlus
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

theorem Formalism.InvariantFactorPaths.KP.LL.sp_wU_inj : Function.Injective (wU (r := r) D) := by sorry
