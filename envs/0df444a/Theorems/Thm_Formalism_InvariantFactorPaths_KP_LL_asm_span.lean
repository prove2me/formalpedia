-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_asm_span
-- name    : Formalism.InvariantFactorPaths.KP.LL.asm_span
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:36:33.647476+00:00
-- url     : https://prove2.me/theorems/5dc9e326-8521-415e-b10b-a9c1c42483fe
-- title:
--   LL: asm span
-- statement:
--   The LL construction uses the asm span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/LevelLatticeOf.lean#L50-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/BihomogeneousPairs/LetterChainEmbeddings/LevelLatticeOf.lean#L50-L58

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

theorem Formalism.InvariantFactorPaths.KP.LL.asm_span (p : ℕ) [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module ℚ_[p] V] [Module ℤ_[p] V]
    (A B : Submodule ℤ_[p] V) (K : ℕ) (h : ∀ v ∈ A, (p : ℚ_[p]) ^ K • v ∈ B) :
    Submodule.span ℚ_[p] (A : Set V) ≤ Submodule.span ℚ_[p] (B : Set V) := by sorry
