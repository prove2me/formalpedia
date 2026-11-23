-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_smul_mem_of_norm
-- name    : Formalism.InvariantFactorPaths.KP.LL.smul_mem_of_norm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:58:38.967192+00:00
-- url     : https://prove2.me/theorems/c8f1c68f-144a-465a-b90e-826e2d24b9d7
-- title:
--   LL: smul mem of norm
-- statement:
--   The LL construction uses the smul mem of norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/SmulMemOfNorm.lean#L27-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/SmulMemOfNorm.lean#L27-L33

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

theorem Formalism.InvariantFactorPaths.KP.LL.smul_mem_of_norm (Λ : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p])) {s : ℚ_[p]} (hs : ‖s‖ ≤ 1)
    {v : MvPolynomial σ ℚ_[p]} (hv : v ∈ Λ) : s • v ∈ Λ := by sorry
