-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_dpow_int_map
-- name    : Formalism.InvariantFactorPaths.L4.dpow_int_map
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:40:35.035406+00:00
-- url     : https://prove2.me/theorems/7524ac85-350a-4eaf-bf3f-3cd27a36f562
-- title:
--   L4: dpow int map
-- statement:
--   The L4 construction uses the dpow int map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/MulEarlyLettersModP.lean#L84-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/MulEarlyLettersModP.lean#L84-L113

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FiltrationBotHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersModP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (LL : Letters N) (j : ℕ)

theorem Formalism.InvariantFactorPaths.L4.dpow_int_map (c : Fin r) (hc : c ≠ 0) (P : MvPolynomial (Fin N × Fin r) ℤ_[p]) :
    ∀ k, dpow p LL j c k (map (algebraMap ℤ_[p] ℚ_[p]) P) ∈ IntPol p (Fin N × Fin r) := by sorry
