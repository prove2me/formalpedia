-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_pderiv_freeLast
-- name    : Formalism.InvariantFactorPaths.L4.pderiv_freeLast
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:03:14.578908+00:00
-- url     : https://prove2.me/theorems/c8fcbcc1-26dd-4875-ac5e-699ec28b613d
-- title:
--   L4: pderiv free Last
-- statement:
--   The L4 construction uses the pderiv free Last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/ResInto.lean#L250-L258
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/ResInto.lean#L250-L258

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FirstWeightLeOfSupport
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
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

theorem Formalism.InvariantFactorPaths.L4.pderiv_freeLast (x : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (hx : x ∈ FreeLast p K r) (d : Fin r) :
    pderiv (Fin.last K, d) x = 0 := by sorry
