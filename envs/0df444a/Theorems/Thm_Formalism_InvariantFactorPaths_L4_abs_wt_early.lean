-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_abs_wt_early
-- name    : Formalism.InvariantFactorPaths.L4.abs_wt_early
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:40:36.71072+00:00
-- url     : https://prove2.me/theorems/418f70c8-4528-4e2c-be98-779cb9ed2c05
-- title:
--   L4: abs wt early
-- statement:
--   The L4 construction uses the abs wt early property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/Vanish.lean#L8-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/Vanish.lean#L8-L28

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementG
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_OmegaInjectiveHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_Vanish
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

theorem Formalism.InvariantFactorPaths.L4.abs_wt_early {K r : ℕ} (LL : Letters (K + 1)) (o : ℕ) (c : Fin r) (m : Fin (K + 1) × Fin r →₀ ℕ)
    (hm : MultiDeg (setLast LL o) m) :
    |wt LL K c m| ≤ ∑ i : Fin (K + 1), if i = Fin.last K then 0 else (LL.deg i : ℤ) := by sorry
