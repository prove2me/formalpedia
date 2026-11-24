-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_wt_pow
-- name    : Formalism.InvariantFactorPaths.L4.wt_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:47.278813+00:00
-- url     : https://prove2.me/theorems/159fa044-daff-4276-a83c-ce59507069a1
-- title:
--   L4: wt pow
-- statement:
--   The L4 construction uses the wt pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/FiltrationBotHolds.lean#L125-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/FiltrationBotHolds.lean#L125-L140

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

theorem Formalism.InvariantFactorPaths.L4.wt_pow (hv : LL.vec (Fin.last K) = true) (ρ c : Fin r) (e : ℕ) (m : Fin (K + 1) × Fin r →₀ ℕ) :
    wt LL (K + 1) c (Finsupp.single (Fin.last K, ρ) e + m) = wt LL (K + 1) c m + (if ρ = c then (e : ℤ) else 0) := by sorry
