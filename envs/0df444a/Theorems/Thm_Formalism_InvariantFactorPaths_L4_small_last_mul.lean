-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_small_last_mul
-- name    : Formalism.InvariantFactorPaths.L4.small_last_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:38.294627+00:00
-- url     : https://prove2.me/theorems/00dd72a5-ae96-4d0b-948a-6ee15cee8d21
-- title:
--   L4: small last mul
-- statement:
--   The L4 construction uses the small last mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/MulEarlyLettersModP.lean#L246-L266
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/MulEarlyLettersModP.lean#L246-L266

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FiltrationBotHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersModP
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
variable (p : ℕ) [Fact p.Prime] {K r : ℕ} [NeZero r] (LL : Letters (K + 1)) (j : ℕ) (M : WithTop ℤ)

theorem Formalism.InvariantFactorPaths.L4.small_last_mul (hj : K + 1 ≤ j) (hv : LL.vec (Fin.last K) = true) (c' : Fin r)
    (g : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p])
    (hg : ∀ m : Fin (K + 1) × Fin r →₀ ℕ, ¬ (((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ M + ((-1 : ℤ) : WithTop ℤ)) →
      ‖coeff m g‖ < 1) :
    ∀ m : Fin (K + 1) × Fin r →₀ ℕ, ¬ (((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ M) →
      ‖coeff m (X (Fin.last K, c') * g)‖ < 1 := by sorry
