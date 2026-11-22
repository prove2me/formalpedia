-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_hypE_eproj
-- name    : Formalism.InvariantFactorPaths.L4.hypE_eproj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:43:22.297399+00:00
-- url     : https://prove2.me/theorems/59f15bb2-4ee9-46d2-912c-ffb729f252ab
-- title:
--   L4: hyp E eproj
-- statement:
--   The L4 construction uses the hyp E eproj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/RestrictionMinMaxIntHolds.lean#L21-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/RestrictionMinMaxIntHolds.lean#L21-L26

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RestrictionMinMaxIntHolds
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

theorem Formalism.InvariantFactorPaths.L4.hypE_eproj (LL : Letters N) (ρ : Fin r) (e1 : ℕ) (hE : HypE p LL ρ e1) (j : ℕ) (hj : j ≤ N) (w : Fin r → ℤ) :
    ∃ PE, IsEProj p LL j ρ w PE ∧
      (∀ F G, F ∈ WtSpC p LL j univ w → G ∈ WtSpC p LL j univ w → fock p (PE F) G = fock p F (PE G)) ∧
      ∀ F ∈ PolZ p r LL, F ∈ WtSpC p LL j univ w → ((p : ℚ_[p]) ^ e1) • PE F ∈ IntPol p (Fin N × Fin r) := by sorry
