-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_span_map_mem
-- name    : Formalism.InvariantFactorPaths.KP.LL.span_map_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:20:50.724801+00:00
-- url     : https://prove2.me/theorems/6dae3221-df87-4dae-b98e-201e985b1177
-- title:
--   LL: span map mem
-- statement:
--   The LL construction uses the span map mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/SmulMemOfNorm.lean#L35-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/SmulMemOfNorm.lean#L35-L45

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

theorem Formalism.InvariantFactorPaths.KP.LL.span_map_mem {τ : Type} (T : MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial τ ℚ_[p])
    (S : Set (MvPolynomial σ ℚ_[p])) (Λ : Submodule ℤ_[p] (MvPolynomial τ ℚ_[p]))
    (h : ∀ v ∈ S, T v ∈ Λ) : ∀ v ∈ Submodule.span ℤ_[p] S, T v ∈ Λ := by sorry
