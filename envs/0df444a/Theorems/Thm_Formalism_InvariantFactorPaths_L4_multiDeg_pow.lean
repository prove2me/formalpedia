-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_multiDeg_pow
-- name    : Formalism.InvariantFactorPaths.L4.multiDeg_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:34:28.366455+00:00
-- url     : https://prove2.me/theorems/c2ca4a0a-8b25-4fb9-a184-a45e5badbfd1
-- title:
--   L4: multi Deg pow
-- statement:
--   The L4 construction uses the multi Deg pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/FiltrationBotHolds.lean#L142-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/FiltrationBotHolds.lean#L142-L173

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementB
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_InitPartZeroXMul
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FiltrationBotHolds
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
variable {p : ℕ} [Fact p.Prime] {K r : ℕ} (LL : Letters (K + 1))

theorem Formalism.InvariantFactorPaths.L4.multiDeg_pow (ρ : Fin r) (e : ℕ) (he : e ≤ LL.deg (Fin.last K)) (m : Fin (K + 1) × Fin r →₀ ℕ) :
    MultiDeg LL (Finsupp.single (Fin.last K, ρ) e + m) ↔ MultiDeg (setLast LL (LL.deg (Fin.last K) - e)) m := by sorry
