-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_yCond_pow
-- name    : Formalism.InvariantFactorPaths.L4.yCond_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:04:23.918998+00:00
-- url     : https://prove2.me/theorems/382b32e5-d7e8-4ca5-a98e-f5bc8ce3b1cd
-- title:
--   L4: y Cond pow
-- statement:
--   The L4 construction uses the y Cond pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/FiltrationBotHolds.lean#L241-L256
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/FiltrationBotHolds.lean#L241-L256

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

theorem Formalism.InvariantFactorPaths.L4.yCond_pow [NeZero r] (hv : LL.vec (Fin.last K) = true) (ρ : Fin r) (e j : ℕ) (M : WithTop ℤ)
    (h : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    X (Fin.last K, ρ) ^ e * h ∈ YCond p LL j M ↔
      h ∈ YCond p LL j (if K + 1 ≤ j then M + ((-(e : ℤ) : ℤ) : WithTop ℤ) else M) := by sorry
