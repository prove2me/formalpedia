-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_move_mem
-- name    : Formalism.InvariantFactorPaths.L4.move_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:45.822955+00:00
-- url     : https://prove2.me/theorems/e79f0e4a-e6bc-4abe-b0ba-5a553c3bb629
-- title:
--   L4: move mem
-- statement:
--   The L4 construction uses the move mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/HighestVectorProjectionPos.lean#L60-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/HighestVectorProjectionPos.lean#L60-L112

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

theorem Formalism.InvariantFactorPaths.L4.move_mem (i0 : Fin N) (t : Fin r) (d : ℕ) (S : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))
    (hbase : ∀ m : Fin N × Fin r →₀ ℕ, (∀ c, c ≠ t → m (i0, c) = 0) → m (i0, t) = d →
      monomial m (1 : ℚ_[p]) ∈ S)
    (hst : ∀ a, ∀ x ∈ S, X (i0, a) * pderiv (i0, t) x ∈ S) :
    ∀ (n : ℕ) (m : Fin N × Fin r →₀ ℕ), m (i0, t) + n = d → ∑ c, m (i0, c) = d →
      monomial m (1 : ℚ_[p]) ∈ S := by sorry
