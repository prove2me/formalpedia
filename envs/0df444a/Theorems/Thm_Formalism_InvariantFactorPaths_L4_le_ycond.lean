-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_le_ycond
-- name    : Formalism.InvariantFactorPaths.L4.le_ycond
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T21:29:25.105966+00:00
-- url     : https://prove2.me/theorems/998bb34e-d380-4950-aab7-f9b3713c1b88
-- title:
--   L4: le ycond
-- statement:
--   The L4 construction uses the le ycond property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/FirstWeightLeOfSupport.lean#L365-L369
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/FirstWeightLeOfSupport.lean#L365-L369

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_InitPartZeroXMul
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FirstWeightLeOfSupport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem Formalism.InvariantFactorPaths.L4.le_ycond [NeZero r] (LL : Letters N) (j : ℕ) (Mt : WithTop ℤ)
    (S : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))
    (h1 : S ≤ restrictSupport ℚ_[p] {m : Fin N × Fin r →₀ ℕ | ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ Mt})
    (h2 : GlStable p LL j S) : S ≤ YCond p LL j Mt := by sorry
