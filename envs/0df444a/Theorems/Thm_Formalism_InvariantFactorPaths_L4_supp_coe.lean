-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_supp_coe
-- name    : Formalism.InvariantFactorPaths.L4.supp_coe
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:41.210787+00:00
-- url     : https://prove2.me/theorems/f742d2ea-e0cc-4186-b5d0-7a06d658cb56
-- title:
--   L4: supp coe
-- statement:
--   The L4 construction uses the supp coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/RaisingKeepsEarlyLetters.lean#L69-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/RaisingKeepsEarlyLetters.lean#L69-L74

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FiltrationBotHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
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
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}

theorem Formalism.InvariantFactorPaths.L4.supp_coe {N : ℕ} [NeZero r] (LL : Letters N) (j : ℕ) (k : ℤ) :
    restrictSupport ℚ_[p] {m : Fin N × Fin r →₀ ℕ | ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ ((k : ℤ) : WithTop ℤ)} =
      restrictSupport ℚ_[p] {m : Fin N × Fin r →₀ ℕ | wt LL j 0 m ≤ k} := by sorry
