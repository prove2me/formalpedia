-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_mulLeft_pow_apply
-- name    : Formalism.InvariantFactorPaths.KP.LL.mulLeft_pow_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:36:19.216765+00:00
-- url     : https://prove2.me/theorems/8848c2c5-9c2a-492d-b9ac-1791a1bdfb80
-- title:
--   LL: mul Left pow apply
-- statement:
--   The LL construction uses the mul Left pow apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/TieFPowMulFree.lean#L14-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/TieFPowMulFree.lean#L14-L21

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelDecomp
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_ScalSum
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_TieFPowMulFree
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
open MvPolynomial Finset
variable {k σ : Type} [Field k] {r : ℕ} (w e : Fin r → σ) (zv sv : σ)

theorem Formalism.InvariantFactorPaths.KP.LL.mulLeft_pow_apply (a f : MvPolynomial σ k) (m : ℕ) :
    ((LinearMap.mulLeft k a) ^ m) f = a ^ m * f := by sorry
