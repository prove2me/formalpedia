-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_supp_le_of_monomial
-- name    : Formalism.InvariantFactorPaths.L4.supp_le_of_monomial
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:42:01.176947+00:00
-- url     : https://prove2.me/theorems/6366246a-6cf9-40ac-b03f-19cd53ea14e0
-- title:
--   L4: supp le of monomial
-- statement:
--   The L4 construction uses the supp le of monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/HighestVectorProjectionPos.lean#L11-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/HighestVectorProjectionPos.lean#L11-L20

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementH
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_HighestVectorProjection
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_HighestVectorProjectionPos
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem Formalism.InvariantFactorPaths.L4.supp_le_of_monomial {σ : Type} (Q : Set (σ →₀ ℕ)) (S : Submodule ℚ_[p] (MvPolynomial σ ℚ_[p]))
    (h : ∀ m ∈ Q, monomial m (1 : ℚ_[p]) ∈ S) : restrictSupport ℚ_[p] Q ≤ S := by sorry
