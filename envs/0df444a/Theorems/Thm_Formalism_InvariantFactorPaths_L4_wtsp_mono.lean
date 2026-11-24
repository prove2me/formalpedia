-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_wtsp_mono
-- name    : Formalism.InvariantFactorPaths.L4.wtsp_mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:54.839795+00:00
-- url     : https://prove2.me/theorems/926a1c6c-290d-4af6-b015-bc5dfec6b16d
-- title:
--   L4: wtsp mono
-- statement:
--   The L4 construction uses the wtsp mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/RestrictionMinMaxIntHolds.lean#L28-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/RestrictionMinMaxIntHolds.lean#L28-L36

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

theorem Formalism.InvariantFactorPaths.L4.wtsp_mono (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (w : Fin r → ℤ) :
    WtSpC p LL j univ w ≤ WtSpC p LL j Cs w := by sorry
