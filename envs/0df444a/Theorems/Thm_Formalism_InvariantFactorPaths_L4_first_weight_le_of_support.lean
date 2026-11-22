-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_first_weight_le_of_support
-- name    : Formalism.InvariantFactorPaths.L4.first_weight_le_of_support
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:43:10.464653+00:00
-- url     : https://prove2.me/theorems/8106d52f-ed50-4058-a898-9a03398eadd8
-- title:
--   L4: first weight le of support
-- statement:
--   The L4 construction uses the first weight le of support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/FirstWeightLeOfSupport.lean#L371-L385
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/FirstWeightLeOfSupport.lean#L371-L385

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

theorem Formalism.InvariantFactorPaths.L4.first_weight_le_of_support [NeZero r] (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (h0 : (0 : Fin r) ∈ Cs)
    (Mt : WithTop ℤ) (μ : Fin r → ℤ) (h : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hh0 : h ≠ 0)
    (h1 : h ∈ restrictSupport ℚ_[p] {m : Fin N × Fin r →₀ ℕ | ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ Mt})
    (h3 : h ∈ WtSpC p LL j Cs μ) : ((μ 0 : ℤ) : WithTop ℤ) ≤ Mt := by sorry
