-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_DDop_cov
-- name    : Formalism.InvariantFactorPaths.L4.DDop_cov
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:20:56.432728+00:00
-- url     : https://prove2.me/theorems/efd26b30-6589-48f5-9b53-ddd3c3680cef
-- title:
--   L4: DDop cov
-- statement:
--   The L4 construction uses the DDop cov property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/DerivativeDividedIntegral.lean#L227-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/DerivativeDividedIntegral.lean#L227-L233

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

theorem Formalism.InvariantFactorPaths.L4.DDop_cov (i : Fin (K + 1)) (hi : i ≠ Fin.last K) (hv : LL.vec i = false) (d : Fin r) :
    DDop p LL Cs a (X (i, d)) = if a = d then -∑ b ∈ Cs, X (Fin.last K, b) * X (i, b) else 0 := by sorry
