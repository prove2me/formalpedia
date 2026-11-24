-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_DDop_mul
-- name    : Formalism.InvariantFactorPaths.L4.DDop_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:20:45.654812+00:00
-- url     : https://prove2.me/theorems/479051af-6df0-44b9-81fc-9ce031f7ccba
-- title:
--   L4: DDop mul
-- statement:
--   The L4 construction uses the DDop mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/DerivativeDividedIntegral.lean#L99-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/DerivativeDividedIntegral.lean#L99-L126

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

theorem Formalism.InvariantFactorPaths.L4.DDop_mul (f g : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    DDop p LL Cs a (f * g) = DDop p LL Cs a f * g + f * DDop p LL Cs a g := by sorry
