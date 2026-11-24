-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_DDop_vec
-- name    : Formalism.InvariantFactorPaths.L4.DDop_vec
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:40:33.287587+00:00
-- url     : https://prove2.me/theorems/09cc40f9-3bb8-462e-9687-17f6c048c205
-- title:
--   L4: DDop vec
-- statement:
--   The L4 construction uses the DDop vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/DerivativeDividedIntegral.lean#L221-L225
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/DerivativeDividedIntegral.lean#L221-L225

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementG
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_DerivativeDividedIntegral
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
variable (LL : Letters (K + 1)) (Cs : Finset (Fin r)) (a : Fin r)

theorem Formalism.InvariantFactorPaths.L4.DDop_vec (i : Fin (K + 1)) (hi : i ≠ Fin.last K) (hv : LL.vec i = true) (d : Fin r) :
    DDop p LL Cs a (X (i, d)) = if d ∈ Cs then X (Fin.last K, d) * X (i, a) else 0 := by sorry
