-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_wt_succ
-- name    : Formalism.InvariantFactorPaths.L4.wt_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:37:15.973476+00:00
-- url     : https://prove2.me/theorems/763e1cf8-49d8-452a-9832-d17ec65e66fd
-- title:
--   L4: wt succ
-- statement:
--   The L4 construction uses the wt succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/ResInto.lean#L115-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/ResInto.lean#L115-L124

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

theorem Formalism.InvariantFactorPaths.L4.wt_succ (LL : Letters (K + 1)) (hv : LL.vec (Fin.last K) = true) (c : Fin r)
    (m : Fin (K + 1) × Fin r →₀ ℕ) : wt LL (K + 1) c m = wt LL K c m + (m (Fin.last K, c) : ℤ) := by sorry
