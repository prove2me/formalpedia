-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_DDop_last
-- name    : Formalism.InvariantFactorPaths.L4.DDop_last
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:20:43.207176+00:00
-- url     : https://prove2.me/theorems/5d3ce80e-81a2-4e74-8f35-eceff70e2170
-- title:
--   L4: DDop last
-- statement:
--   The L4 construction uses the DDop last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/DerivativeDividedIntegral.lean#L212-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/DerivativeDividedIntegral.lean#L212-L219

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

theorem Formalism.InvariantFactorPaths.L4.DDop_last (d : Fin r) :
    DDop p LL Cs a (X (Fin.last K, d)) = ((1 : ℤ) : ℚ_[p]) • (X (Fin.last K, a) * X (Fin.last K, d)) := by sorry
