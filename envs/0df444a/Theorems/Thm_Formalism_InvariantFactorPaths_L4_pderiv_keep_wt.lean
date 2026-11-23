-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_pderiv_keep_wt
-- name    : Formalism.InvariantFactorPaths.L4.pderiv_keep_wt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:02:35.67628+00:00
-- url     : https://prove2.me/theorems/1a5201b2-191e-4265-af27-acc14aacd200
-- title:
--   L4: pderiv keep wt
-- statement:
--   The L4 construction uses the pderiv keep wt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/ResInto.lean#L140-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/ResInto.lean#L140-L167

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

theorem Formalism.InvariantFactorPaths.L4.pderiv_keep_wt [NeZero r] (LL : Letters (K + 1)) (hv : LL.vec (Fin.last K) = true) (c : Fin r)
    (Mt : WithTop ℤ) :
    ∀ x ∈ restrictSupport ℚ_[p] {m : Fin (K + 1) × Fin r →₀ ℕ | ((wt LL (K + 1) 0 m : ℤ) : WithTop ℤ) ≤ Mt},
      pderiv (Fin.last K, c) x ∈
        restrictSupport ℚ_[p] {m : Fin (K + 1) × Fin r →₀ ℕ | ((wt LL (K + 1) 0 m : ℤ) : WithTop ℤ) ≤ Mt} := by sorry
