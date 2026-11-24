-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_free_ehP
-- name    : Formalism.InvariantFactorPaths.KP.LL.free_ehP
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:36:15.249231+00:00
-- url     : https://prove2.me/theorems/d589d125-7323-45b5-867d-a4c1afb93dca
-- title:
--   LL: free eh P
-- statement:
--   The LL construction uses the free eh P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/SmulMemOfNorm.lean#L60-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/SmulMemOfNorm.lean#L60-L64

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_PhiInt
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_TieFPowMulFree
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_SmulMemOfNorm
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
variable {p : ℕ} [Fact p.Prime] {σ : Type}

theorem Formalism.InvariantFactorPaths.KP.LL.free_ehP {r : ℕ} {w e : Fin r → σ} {zv sv v : σ} (h1 : zv ≠ v) (h2 : sv ≠ v) (h3 : ∀ c, w c ≠ v)
    (h4 : ∀ c, e c ≠ v) : pderiv v (ehP w e zv sv : MvPolynomial σ ℚ_[p]) = 0 := by sorry
